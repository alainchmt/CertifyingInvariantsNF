
import IdealArithmetic.Examples.NF5_3_1215000000_2.RI5_3_1215000000_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0, 0, 0]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![199, 0, 0, 0, 0]] 
 ![![199, 0, 0, 0, 0], ![0, 199, 0, 0, 0], ![0, 0, 199, 0, 0], ![0, 0, 0, 199, 0], ![0, 0, 0, 0, 199]] where
  M :=![![![199, 0, 0, 0, 0], ![0, 199, 0, 0, 0], ![0, 0, 199, 0, 0], ![0, 0, 0, 199, 0], ![0, 0, 0, 0, 199]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 5 2 7 [171, 37, 67, 14, 78, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [191, 186, 19, 26, 194], [195, 128, 27, 164, 151], [166, 36, 138, 10, 111], [166, 47, 15, 198, 141], [0, 1]]
 g := ![![[85, 76, 173, 193, 92], [192, 98, 84, 190, 89], [133, 11, 102, 196, 7], [118, 164, 35, 124], [67, 192, 110, 50], [121, 1], []], ![[136, 51, 189, 11, 92, 152, 90, 6], [121, 28, 196, 143, 197, 35, 98, 143], [117, 44, 2, 195, 136, 152, 21, 118], [109, 122, 83, 91], [103, 167, 89, 131], [163, 187, 19, 28], [131, 84, 122, 141, 86, 14, 158, 74]], ![[134, 191, 180, 46, 69, 135, 61, 187], [75, 107, 105, 182, 144, 154, 64, 100], [11, 149, 55, 188, 49, 99, 162, 92], [146, 104, 182, 124], [187, 3, 193, 56], [56, 106, 117, 35], [114, 115, 144, 131, 101, 84, 187, 52]], ![[158, 194, 172, 50, 36, 121, 160, 155], [118, 131, 27, 61, 66, 93, 165, 106], [52, 97, 2, 73, 14, 113, 117, 5], [83, 33, 195, 158], [53, 169, 167, 40], [181, 154, 22, 43], [92, 126, 15, 144, 140, 125, 13, 103]], ![[7, 111, 23, 69, 90, 70, 53, 164], [173, 147, 100, 48, 43, 177, 107, 185], [102, 63, 96, 80, 3, 1, 51, 3], [102, 145, 6, 49], [172, 138, 109, 31], [60, 196, 71, 122], [3, 82, 64, 130, 178, 51, 69, 107]]]
 h' := ![![[191, 186, 19, 26, 194], [3, 83, 3, 77, 106], [142, 157, 63, 146, 158], [81, 184, 32, 165, 112], [110, 197, 61, 6, 129], [5, 128, 15, 30, 100], [0, 0, 0, 1], [0, 1]], ![[195, 128, 27, 164, 151], [175, 23, 100, 139, 77], [39, 184, 116, 134, 161], [23, 60, 122, 135, 102], [126, 193, 192, 115, 84], [174, 101, 72, 135, 176], [171, 183, 78, 56, 25], [191, 186, 19, 26, 194]], ![[166, 36, 138, 10, 111], [198, 89, 39, 97, 99], [133, 88, 64, 141, 121], [118, 21, 62, 94, 190], [72, 5, 130, 5, 70], [127, 52, 92, 156, 102], [143, 171, 6, 25, 45], [195, 128, 27, 164, 151]], ![[166, 47, 15, 198, 141], [116, 129, 65, 3, 189], [162, 35, 44, 167, 61], [185, 68, 37, 179, 114], [99, 173, 113, 119, 122], [159, 127, 156, 133, 55], [71, 127, 104, 33, 21], [166, 36, 138, 10, 111]], ![[0, 1], [60, 74, 191, 82, 126], [143, 133, 111, 9, 96], [55, 65, 145, 24, 79], [130, 29, 101, 153, 192], [182, 189, 63, 143, 164], [166, 116, 11, 84, 108], [166, 47, 15, 198, 141]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [131, 130, 194, 120], [], [], []]
 b := ![[], [14, 2, 79, 165, 24], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 5
  hpos := by decide
  P := [171, 37, 67, 14, 78, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![16157108237121, 3244067473201, -4999442584144, -25120822824226, -12615845945419]
  a := ![0, 7, -7, -5, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![81191498679, 16301846599, -25122827056, -126235290574, -63396210781]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 312079600999 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def PBC199 : ContainsPrimesAboveP 199 ![I199N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI199N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![199, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 199 (by decide) 𝕀

instance hp211 : Fact (Nat.Prime 211) := {out := by norm_num}

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![117, -606, 430, 160, -222]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![117, -606, 430, 160, -222]] 
 ![![211, 0, 0, 0, 0], ![0, 211, 0, 0, 0], ![135, 55, 1, 0, 0], ![102, 180, 0, 1, 0], ![75, 47, 0, 0, 1]] where
  M :=![![![117, -606, 430, 160, -222], ![1332, -1139, -876, 118, 320], ![-1920, 3050, -145, -590, 236], ![-668, 478, 528, -27, -208], ![2584, -3230, -668, 522, 119]]]
  hmulB := by decide  
  f := ![![![-4481, -2350, -1230, 68, 518]], ![![-3108, -1765, -1052, -514, 136]], ![![-3681, -1969, -1067, -104, 362]], ![![-4814, -2646, -1500, -431, 356]], ![![-2261, -1225, -678, -128, 197]]]
  g := ![![![-273, -202, 430, 160, -222], ![396, 51, -876, 118, 320], ![285, 503, -145, -590, 236], ![-254, -66, 528, -27, -208], ![145, -313, -668, 522, 119]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 2 2 7 [152, 141, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [70, 210], [0, 1]]
 g := ![![[180, 36], [11, 204], [84], [47], [9, 34], [53], [70, 1]], ![[168, 175], [154, 7], [84], [47], [68, 177], [53], [140, 210]]]
 h' := ![![[70, 210], [16, 6], [55, 41], [95, 57], [109, 141], [44, 33], [121, 106], [0, 1]], ![[0, 1], [14, 205], [182, 170], [76, 154], [62, 70], [33, 178], [156, 105], [70, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [82]]
 b := ![[], [42, 41]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 2
  hpos := by decide
  P := [152, 141, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-698106, -1704826, 1779546, 1464282, 2598950]
  a := ![3, 62, -124, -1, -249]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2773530, -2300006, 1779546, 1464282, 2598950]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![515, 290, 131, -31, -64]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![515, 290, 131, -31, -64]] 
 ![![211, 0, 0, 0, 0], ![0, 211, 0, 0, 0], ![167, 78, 1, 0, 0], ![4, 93, 0, 1, 0], ![167, 87, 0, 0, 1]] where
  M :=![![![515, 290, 131, -31, -64], ![384, 223, 128, -22, -62], ![372, 92, 73, -10, -44], ![340, 164, 70, -29, -42], ![-38, 70, 25, -27, -17]]]
  hmulB := by decide  
  f := ![![![4789, -4258, 3565, -5999, 3094]], ![![-18564, 16505, -13822, 23260, -11998]], ![![-2731, 2428, -2034, 3423, -1766]], ![![-8448, 7511, -6290, 10585, -5460]], ![![-3209, 2853, -2390, 4022, -2075]]]
  g := ![![![-50, -7, 131, -31, -64], ![-50, -11, 128, -22, -62], ![-21, -4, 73, -10, -44], ![-20, 5, 70, -29, -42], ![-6, 10, 25, -27, -17]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P1 : CertificateIrreducibleZModOfList' 211 2 2 7 [96, 137, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [74, 210], [0, 1]]
 g := ![![[30, 11], [163, 109], [185], [179], [94, 173], [53], [74, 1]], ![[0, 200], [0, 102], [185], [179], [25, 38], [53], [148, 210]]]
 h' := ![![[74, 210], [177, 86], [133, 98], [198, 117], [49, 161], [23, 54], [70, 105], [0, 1]], ![[0, 1], [0, 125], [0, 113], [205, 94], [147, 50], [10, 157], [33, 106], [74, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [78, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N1 : CertifiedPrimeIdeal' SI211N1 211 where
  n := 2
  hpos := by decide
  P := [96, 137, 1]
  hirr := P211P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6462, -7232, 7723, 11601, 11730]
  a := ![1, 6, -8, -3, -18]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-15647, -12839, 7723, 11601, 11730]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N1 B_one_repr
lemma NI211N1 : Nat.card (O ⧸ I211N1) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N1

def I211N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-163, 214, 34, -38, -4]] i)))

def SI211N2: IdealEqSpanCertificate' Table ![![-163, 214, 34, -38, -4]] 
 ![![211, 0, 0, 0, 0], ![78, 1, 0, 0, 0], ![35, 0, 1, 0, 0], ![42, 0, 0, 1, 0], ![156, 0, 0, 0, 1]] where
  M :=![![![-163, 214, 34, -38, -4], ![24, -171, 142, 40, -76], ![456, -386, -273, 10, 80], ![0, 134, -78, -93, 8], ![-240, 138, 306, -78, -175]]]
  hmulB := by decide  
  f := ![![![130991, 66886, 34590, -7150, -16556]], ![![48894, 24981, 12906, -2656, -6188]], ![![22135, 11256, 5861, -1248, -2772]], ![![26418, 13542, 6958, -1397, -3368]], ![![96924, 49398, 25626, -5370, -12199]]]
  g := ![![![-75, 214, 34, -38, -4], ![88, -171, 142, 40, -76], ![129, -386, -273, 10, 80], ![-24, 134, -78, -93, 8], ![42, 138, 306, -78, -175]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N2 : Nat.card (O ⧸ I211N2) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N2)

lemma isPrimeI211N2 : Ideal.IsPrime I211N2 := prime_ideal_of_norm_prime hp211.out _ NI211N2
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![117, -606, 430, 160, -222]] ![![515, 290, 131, -31, -64]]
  ![![50347, -50948, -25201, 6759, 8218]] where
 M := ![![![50347, -50948, -25201, 6759, 8218]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI211N1 : IdealMulLeCertificate' Table 
  ![![50347, -50948, -25201, 6759, 8218]] ![![-163, 214, 34, -38, -4]]
  ![![211, 0, 0, 0, 0]] where
 M := ![![![-22893289, 31253742, 3344561, -5472707, 270502]]]
 hmul := by decide  
 g := ![![![![-108499, 148122, 15851, -25937, 1282]]]]
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

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-453375, -233837, -118916, 22749, 58594]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![-453375, -233837, -118916, 22749, 58594]] 
 ![![223, 0, 0, 0, 0], ![0, 223, 0, 0, 0], ![0, 0, 223, 0, 0], ![82, 196, 127, 1, 0], ![171, 5, 85, 0, 1]] where
  M :=![![![-453375, -233837, -118916, 22749, 58594], ![-351564, -181426, -92172, 17565, 45498], ![-272988, -140463, -71689, 14037, 35130], ![-278444, -143945, -72866, 13784, 36234], ![-8768, -3839, -2456, 1167, 851]]]
  hmulB := by decide  
  f := ![![![55, -4615, 4538, 1359, -2246]], ![![13476, -12580, -7794, 1497, 2718]], ![![-16308, 27927, -3289, -5577, 2994]], ![![2546, 3176, -7033, -1363, 3260]], ![![-5765, 6683, 2031, -1026, -519]]]
  g := ![![![-55329, -22357, -35823, 22749, 58594], ![-42924, -17272, -27759, 17565, 45498], ![-33324, -13755, -21706, 14037, 35130], ![-34102, -13573, -21988, 13784, 36234], ![-1121, -1062, -1000, 1167, 851]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 3 2 7 [87, 190, 171, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [158, 123, 122], [117, 99, 101], [0, 1]]
 g := ![![[11, 131, 66], [174, 166, 25], [55, 135, 17], [185, 46, 202], [34, 61, 127], [205, 28], [1]], ![[53, 137, 158, 160], [192, 110, 186, 123], [29, 203, 34, 44], [216, 59, 109, 87], [5, 20, 133, 157], [34, 69], [146, 140, 27, 182]], ![[63, 18, 174, 25], [41, 102, 68, 188], [181, 171, 196, 126], [214, 61, 97, 169], [211, 104, 200, 86], [124, 199], [38, 219, 144, 41]]]
 h' := ![![[158, 123, 122], [26, 143, 206], [121, 65, 5], [184, 9, 169], [164, 116, 176], [215, 148, 57], [136, 33, 52], [0, 1]], ![[117, 99, 101], [100, 63, 153], [119, 137, 174], [107, 163, 212], [70, 182, 133], [69, 72, 61], [120, 29, 31], [158, 123, 122]], ![[0, 1], [215, 17, 87], [182, 21, 44], [113, 51, 65], [88, 148, 137], [35, 3, 105], [66, 161, 140], [117, 99, 101]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [115, 80], []]
 b := ![[], [75, 138, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 3
  hpos := by decide
  P := [87, 190, 171, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-917340275, -1063560552, 1135441000, 1668714452, 1867583356]
  a := ![1, -25, 48, -1, 95]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2049814705, -1513316188, -1657111568, 1668714452, 1867583356]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 11089567 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-55, 4615, -4538, -1359, 2246]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![-55, 4615, -4538, -1359, 2246]] 
 ![![223, 0, 0, 0, 0], ![0, 223, 0, 0, 0], ![147, 64, 1, 0, 0], ![35, 117, 0, 1, 0], ![118, 85, 0, 0, 1]] where
  M :=![![![-55, 4615, -4538, -1359, 2246], ![-13476, 12580, 7794, -1497, -2718], ![16308, -27927, 3289, 5577, -2994], ![6932, -5629, -4852, 520, 1814], ![-23800, 31421, 4550, -5373, -249]]]
  hmulB := by decide  
  f := ![![![453375, 233837, 118916, -22749, -58594]], ![![351564, 181426, 92172, -17565, -45498]], ![![400983, 206842, 105163, -20100, -51840]], ![![256859, 132534, 67350, -12848, -33230]], ![![373946, 192905, 98068, -18738, -48351]]]
  g := ![![![2016, 1180, -4538, -1359, 2246], ![-3525, -359, 7794, -1497, -2718], ![-1386, -2854, 3289, 5577, -2994], ![2188, 403, -4852, 520, 1814], ![-2131, 1749, 4550, -5373, -249]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P1 : CertificateIrreducibleZModOfList' 223 2 2 7 [100, 110, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [113, 222], [0, 1]]
 g := ![![[68, 29], [96, 153], [141, 2], [178, 128], [37, 34], [203], [113, 1]], ![[0, 194], [214, 70], [144, 221], [147, 95], [88, 189], [203], [3, 222]]]
 h' := ![![[113, 222], [212, 156], [172, 162], [40, 208], [91, 120], [193, 82], [73, 181], [0, 1]], ![[0, 1], [0, 67], [192, 61], [129, 15], [48, 103], [93, 141], [10, 42], [113, 222]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60]]
 b := ![[], [89, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N1 : CertifiedPrimeIdeal' SI223N1 223 where
  n := 2
  hpos := by decide
  P := [100, 110, 1]
  hirr := P223P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5469, -27848, 25931, -149, 31559]
  a := ![-1, 7, -17, 8, -29]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-33745, -19518, 25931, -149, 31559]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N1 B_one_repr
lemma NI223N1 : Nat.card (O ⧸ I223N1) = 49729 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N1
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![-453375, -233837, -118916, 22749, 58594]] ![![-55, 4615, -4538, -1359, 2246]]
  ![![223, 0, 0, 0, 0]] where
 M := ![![![-223, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC223 : ContainsPrimesAboveP 223 ![I223N0, I223N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI223N0
    exact isPrimeI223N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 223 (by decide) (𝕀 ⊙ MulI223N0)
instance hp227 : Fact (Nat.Prime 227) := {out := by norm_num}

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-153, 138, -64, 140, -82]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![-153, 138, -64, 140, -82]] 
 ![![227, 0, 0, 0, 0], ![0, 227, 0, 0, 0], ![0, 0, 227, 0, 0], ![210, 49, 185, 1, 0], ![186, 10, 145, 0, 1]] where
  M :=![![![-153, 138, -64, 140, -82], ![492, -475, 342, -544, 280], ![-1680, 1534, -1361, 2162, -1088], ![1780, -1562, 1346, -2277, 1172], ![-3320, 2890, -2414, 4182, -2179]]]
  hmulB := by decide  
  f := ![![![1709, 882, 448, -88, -222]], ![![1332, 683, 346, -76, -176]], ![![1056, 534, 261, -94, -152]], ![![2734, 1401, 703, -175, -368]], ![![2134, 1094, 549, -136, -287]]]
  g := ![![![-63, -26, -62, 140, -82], ![276, 103, 266, -544, 280], ![-1116, -412, -1073, 2162, -1088], ![1154, 433, 1113, -2277, 1172], ![-2098, -794, -2027, 4182, -2179]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 3 2 7 [9, 96, 123, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [25, 214, 161], [79, 12, 66], [0, 1]]
 g := ![![[199, 217, 36], [22, 66, 181], [8, 195], [54, 188], [27, 102], [10, 87, 147], [1]], ![[69, 0, 197, 82], [190, 95, 208, 141], [175, 63], [75, 65], [68, 30], [126, 166, 82, 71], [60, 197, 87, 113]], ![[144, 224, 204, 96], [135, 7, 21, 67], [220, 185], [88, 3], [182, 177], [167, 123, 77, 153], [28, 74, 11, 114]]]
 h' := ![![[25, 214, 161], [29, 179, 6], [191, 126, 194], [221, 63, 167], [139, 96, 142], [137, 154, 130], [218, 131, 104], [0, 1]], ![[79, 12, 66], [74, 143, 62], [12, 213, 141], [15, 132, 116], [224, 156, 135], [90, 137, 22], [103, 99, 93], [25, 214, 161]], ![[0, 1], [170, 132, 159], [204, 115, 119], [145, 32, 171], [16, 202, 177], [135, 163, 75], [197, 224, 30], [79, 12, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [174, 40], []]
 b := ![[], [119, 56, 35], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 3
  hpos := by decide
  P := [9, 96, 123, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![23170977, -20681712, 17256840, -28933356, 14975220]
  a := ![0, 4, 16, -26, 14]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![14598171, 5494716, 14090400, -28933356, 14975220]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 11697083 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11, 3, 14, 1, -6]] i)))

def SI227N1: IdealEqSpanCertificate' Table ![![-11, 3, 14, 1, -6]] 
 ![![227, 0, 0, 0, 0], ![36, 1, 0, 0, 0], ![66, 0, 1, 0, 0], ![150, 0, 0, 1, 0], ![161, 0, 0, 0, 1]] where
  M :=![![![-11, 3, 14, 1, -6], ![36, -44, -10, 7, 2], ![-12, 45, -27, -11, 14], ![-20, 23, 8, -4, -2], ![40, -71, 10, 15, -9]]]
  hmulB := by decide  
  f := ![![![591, 309, 148, -41, -86]], ![![96, 50, 24, -7, -14]], ![![174, 91, 43, -13, -26]], ![![394, 205, 98, -30, -58]], ![![421, 220, 104, -32, -63]]]
  g := ![![![-1, 3, 14, 1, -6], ![4, -44, -10, 7, 2], ![-2, 45, -27, -11, 14], ![-2, 23, 8, -4, -2], ![5, -71, 10, 15, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N1 : Nat.card (O ⧸ I227N1) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N1)

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := prime_ideal_of_norm_prime hp227.out _ NI227N1

def I227N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6713, 3465, 1764, -327, -864]] i)))

def SI227N2: IdealEqSpanCertificate' Table ![![6713, 3465, 1764, -327, -864]] 
 ![![227, 0, 0, 0, 0], ![89, 1, 0, 0, 0], ![24, 0, 1, 0, 0], ![158, 0, 0, 1, 0], ![73, 0, 0, 0, 1]] where
  M :=![![![6713, 3465, 1764, -327, -864], ![5184, 2684, 1374, -219, -654], ![3924, 2067, 1091, -21, -438], ![3912, 2097, 1140, 128, -378], ![-192, 15, 114, 477, 209]]]
  hmulB := by decide  
  f := ![![![1339, -369, -1494, -273, 756]], ![![505, -121, -582, -108, 294]], ![![156, -69, -139, -33, 78]], ![![934, -261, -1050, -178, 522]], ![![425, -96, -474, -114, 257]]]
  g := ![![![-1010, 3465, 1764, -327, -864], ![-812, 2684, 1374, -219, -654], ![-753, 2067, 1091, -21, -438], ![-893, 2097, 1140, 128, -378], ![-418, 15, 114, 477, 209]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N2 : Nat.card (O ⧸ I227N2) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N2)

lemma isPrimeI227N2 : Ideal.IsPrime I227N2 := prime_ideal_of_norm_prime hp227.out _ NI227N2
def MulI227N0 : IdealMulLeCertificate' Table 
  ![![-153, 138, -64, 140, -82]] ![![-11, 3, 14, 1, -6]]
  ![![1339, -369, -1494, -273, 756]] where
 M := ![![![1339, -369, -1494, -273, 756]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI227N1 : IdealMulLeCertificate' Table 
  ![![1339, -369, -1494, -273, 756]] ![![6713, 3465, 1764, -327, -864]]
  ![![227, 0, 0, 0, 0]] where
 M := ![![![227, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC227 : ContainsPrimesAboveP 227 ![I227N0, I227N1, I227N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI227N0
    exact isPrimeI227N1
    exact isPrimeI227N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 227 (by decide) (𝕀 ⊙ MulI227N0 ⊙ MulI227N1)
instance hp229 : Fact (Nat.Prime 229) := {out := by norm_num}

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1875, -116, -103, -2777, -818]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![1875, -116, -103, -2777, -818]] 
 ![![229, 0, 0, 0, 0], ![0, 229, 0, 0, 0], ![32, 94, 1, 0, 0], ![153, 226, 0, 1, 0], ![70, 57, 0, 0, 1]] where
  M :=![![![1875, -116, -103, -2777, -818], ![4908, 2301, -2790, -7994, -5554], ![33324, -970, -2903, -49688, -15988], ![44720, 13094, -17816, -70669, -40306], ![84350, 1232, -10915, -126795, -45299]]]
  hmulB := by decide  
  f := ![![![-18997, 13512, 15417, -835, -6012]], ![![36072, -51615, -2740, 9344, -1670]], ![![12196, -19192, 857, 3680, -1444]], ![![22811, -41784, 7615, 8642, -5666]], ![![3280, -8995, 4145, 2135, -2319]]]
  g := ![![![2128, 2986, -103, -2777, -818], ![7450, 10427, -2790, -7994, -5554], ![38636, 54204, -2903, -49688, -15988], ![62221, 87146, -17816, -70669, -40306], ![100455, 140895, -10915, -126795, -45299]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 2 2 7 [219, 93, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [136, 228], [0, 1]]
 g := ![![[151, 100], [192], [117, 118], [132], [44], [81, 17], [136, 1]], ![[11, 129], [192], [135, 111], [132], [44], [103, 212], [43, 228]]]
 h' := ![![[136, 228], [26, 10], [25, 110], [184, 205], [226, 19], [123, 161], [215, 186], [0, 1]], ![[0, 1], [12, 219], [100, 119], [126, 24], [62, 210], [35, 68], [92, 43], [136, 228]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [106]]
 b := ![[], [60, 53]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 2
  hpos := by decide
  P := [219, 93, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2279, -22367, 21225, 5356, 26978]
  a := ![13, 7, -15, 5, -27]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-14781, -20811, 21225, 5356, 26978]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 52441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def I229N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![707, 109, -186, -1091, -508]] i)))

def SI229N1: IdealEqSpanCertificate' Table ![![707, 109, -186, -1091, -508]] 
 ![![229, 0, 0, 0, 0], ![0, 229, 0, 0, 0], ![90, 218, 1, 0, 0], ![131, 62, 0, 1, 0], ![191, 37, 0, 0, 1]] where
  M :=![![![707, 109, -186, -1091, -508], ![3048, 460, -796, -4697, -2182], ![13092, 1995, -3441, -20177, -9394], ![24168, 3661, -6326, -37246, -17310], ![34824, 5307, -9144, -53679, -24985]]]
  hmulB := by decide  
  f := ![![![24839, 12821, 6544, -1243, -3224]], ![![19344, 9866, 5034, -955, -2486]], ![![28242, 14465, 7381, -1401, -3642]], ![![19513, 10040, 5124, -973, -2526]], ![![23845, 12288, 6272, -1191, -3091]]]
  g := ![![![1124, 555, -186, -1091, -508], ![4833, 2384, -796, -4697, -2182], ![20787, 10265, -3441, -20177, -9394], ![38336, 18919, -6326, -37246, -17310], ![55292, 27298, -9144, -53679, -24985]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P1 : CertificateIrreducibleZModOfList' 229 2 2 7 [29, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [207, 228], [0, 1]]
 g := ![![[135, 196], [3], [13, 217], [97], [97], [96, 9], [207, 1]], ![[174, 33], [3], [48, 12], [97], [97], [127, 220], [185, 228]]]
 h' := ![![[207, 228], [62, 215], [81, 71], [3, 149], [86, 201], [193, 28], [180, 226], [0, 1]], ![[0, 1], [141, 14], [122, 158], [160, 80], [15, 28], [35, 201], [17, 3], [207, 228]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [112]]
 b := ![[], [158, 56]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N1 : CertifiedPrimeIdeal' SI229N1 229 where
  n := 2
  hpos := by decide
  P := [29, 22, 1]
  hirr := P229P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-598, -552, 613, 1019, 985]
  a := ![-1, 1, -2, -1, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1648, -1021, 613, 1019, 985]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N1 : Ideal.IsPrime I229N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N1 B_one_repr
lemma NI229N1 : Nat.card (O ⧸ I229N1) = 52441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N1

def I229N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-40699, -20998, -10674, 2034, 5262]] i)))

def SI229N2: IdealEqSpanCertificate' Table ![![-40699, -20998, -10674, 2034, 5262]] 
 ![![229, 0, 0, 0, 0], ![146, 1, 0, 0, 0], ![210, 0, 1, 0, 0], ![51, 0, 0, 1, 0], ![227, 0, 0, 0, 1]] where
  M :=![![![-40699, -20998, -10674, 2034, 5262], ![-31572, -16273, -8290, 1584, 4068], ![-24408, -12662, -6399, 1122, 3168], ![-24996, -12854, -6610, 1213, 3160], ![-564, -438, -156, -204, 83]]]
  hmulB := by decide  
  f := ![![![-27319, 142878, -101734, -37830, 52542]], ![![-18794, 92271, -63958, -24240, 33168]], ![![-23070, 127874, -93139, -34086, 47940]], ![![-5397, 31328, -23204, -8393, 11914]], ![![-29741, 144960, -100154, -38046, 51965]]]
  g := ![![![17329, -20998, -10674, 2034, 5262], ![13454, -16273, -8290, 1584, 4068], ![10444, -12662, -6399, 1122, 3168], ![10745, -12854, -6610, 1213, 3160], ![383, -438, -156, -204, 83]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N2 : Nat.card (O ⧸ I229N2) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N2)

lemma isPrimeI229N2 : Ideal.IsPrime I229N2 := prime_ideal_of_norm_prime hp229.out _ NI229N2
def MulI229N0 : IdealMulLeCertificate' Table 
  ![![1875, -116, -103, -2777, -818]] ![![707, 109, -186, -1091, -508]]
  ![![-95976987, -14562193, 25145103, 147919022, 68775794]] where
 M := ![![![-95976987, -14562193, 25145103, 147919022, 68775794]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI229N1 : IdealMulLeCertificate' Table 
  ![![-95976987, -14562193, 25145103, 147919022, 68775794]] ![![-40699, -20998, -10674, 2034, 5262]]
  ![![229, 0, 0, 0, 0]] where
 M := ![![![16009855557, 2433138969, -4198334173, -24675387994, -11477719992]]]
 hmul := by decide  
 g := ![![![![69912033, 10625061, -18333337, -107752786, -50121048]]]]
 hle2 := by decide  


def PBC229 : ContainsPrimesAboveP 229 ![I229N0, I229N1, I229N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI229N0
    exact isPrimeI229N1
    exact isPrimeI229N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 229 (by decide) (𝕀 ⊙ MulI229N0 ⊙ MulI229N1)
instance hp233 : Fact (Nat.Prime 233) := {out := by norm_num}

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![441, 321, 84, 59, -108]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![441, 321, 84, 59, -108]] 
 ![![233, 0, 0, 0, 0], ![0, 233, 0, 0, 0], ![0, 0, 233, 0, 0], ![191, 72, 197, 1, 0], ![83, 4, 109, 0, 1]] where
  M :=![![![441, 321, 84, 59, -108], ![648, -26, 296, -337, 118], ![-708, 1043, -659, 1259, -674], ![1328, -771, 866, -1280, 654], ![-1948, 1703, -1414, 2463, -1211]]]
  hmulB := by decide  
  f := ![![![337, -387, -122, 59, 32]], ![![-192, 496, -206, -115, 118]], ![![-708, 483, 587, -25, -230]], ![![-381, 243, 333, -8, -132]], ![![-213, 97, 225, 7, -93]]]
  g := ![![![-8, -15, 1, 59, -108], ![237, 102, 231, -337, 118], ![-795, -373, -752, 1259, -674], ![822, 381, 780, -1280, 654], ![-1596, -733, -1522, 2463, -1211]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 3 2 7 [1, 143, 100, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [182, 72, 19], [184, 160, 214], [0, 1]]
 g := ![![[51, 109, 204], [134, 196], [182, 225], [64, 224, 157], [104, 36], [36, 210, 214], [1]], ![[158, 35, 51, 74], [34, 201], [221, 51], [232, 40, 189, 219], [121, 100], [106, 149, 58, 112], [2, 29, 206, 102]], ![[229, 16, 225, 9], [169, 23], [9, 187], [197, 184, 161, 113], [181, 16], [145, 89, 208, 64], [111, 94, 109, 131]]]
 h' := ![![[182, 72, 19], [211, 192, 196], [186, 144, 219], [169, 207, 218], [27, 93, 33], [197, 2, 227], [232, 90, 133], [0, 1]], ![[184, 160, 214], [163, 1, 58], [68, 188, 30], [17, 169, 135], [120, 202, 57], [63, 75, 10], [157, 204, 156], [182, 72, 19]], ![[0, 1], [33, 40, 212], [193, 134, 217], [40, 90, 113], [141, 171, 143], [97, 156, 229], [138, 172, 177], [184, 160, 214]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [148, 92], []]
 b := ![[], [44, 76, 81], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 3
  hpos := by decide
  P := [1, 143, 100, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1053407, -558872, 664630, 1735582, 1281746]
  a := ![3, -3, 4, 2, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1883839, -560720, -2064186, 1735582, 1281746]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N0 B_one_repr
lemma NI233N0 : Nat.card (O ⧸ I233N0) = 12649337 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N0

def I233N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![27, -38, 0, 4, 0]] i)))

def SI233N1: IdealEqSpanCertificate' Table ![![27, -38, 0, 4, 0]] 
 ![![233, 0, 0, 0, 0], ![149, 1, 0, 0, 0], ![167, 0, 1, 0, 0], ![199, 0, 0, 1, 0], ![211, 0, 0, 0, 1]] where
  M :=![![![27, -38, 0, 4, 0], ![0, 23, -34, 4, 8], ![-48, 54, 61, -50, 8], ![-32, 14, -10, 45, -28], ![124, -98, -8, -72, 59]]]
  hmulB := by decide  
  f := ![![![-11125, -5698, -2860, 724, 1504]], ![![-7153, -3663, -1838, 468, 968]], ![![-8011, -4100, -2055, 534, 1088]], ![![-9547, -4884, -2446, 645, 1300]], ![![-10099, -5164, -2584, 692, 1379]]]
  g := ![![![21, -38, 0, 4, 0], ![-1, 23, -34, 4, 8], ![-43, 54, 61, -50, 8], ![-15, 14, -10, 45, -28], ![77, -98, -8, -72, 59]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N1 : Nat.card (O ⧸ I233N1) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N1)

lemma isPrimeI233N1 : Ideal.IsPrime I233N1 := prime_ideal_of_norm_prime hp233.out _ NI233N1

def I233N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13, -9, -6, 3, 4]] i)))

def SI233N2: IdealEqSpanCertificate' Table ![![-13, -9, -6, 3, 4]] 
 ![![233, 0, 0, 0, 0], ![191, 1, 0, 0, 0], ![100, 0, 1, 0, 0], ![99, 0, 0, 1, 0], ![211, 0, 0, 0, 1]] where
  M :=![![![-13, -9, -6, 3, 4], ![-24, 2, 0, 9, 6], ![-36, -15, 11, 45, 18], ![-56, -17, 10, 80, 38], ![-80, 1, 16, 111, 55]]]
  hmulB := by decide  
  f := ![![![-7405, 6571, -5516, 9279, -4784]], ![![-5947, 5277, -4430, 7452, -3842]], ![![-3656, 3245, -2723, 4581, -2362]], ![![-2647, 2348, -1972, 3317, -1710]], ![![-7623, 6766, -5678, 9552, -4925]]]
  g := ![![![5, -9, -6, 3, 4], ![-11, 2, 0, 9, 6], ![-28, -15, 11, 45, 18], ![-59, -17, 10, 80, 38], ![-105, 1, 16, 111, 55]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N2 : Nat.card (O ⧸ I233N2) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N2)

lemma isPrimeI233N2 : Ideal.IsPrime I233N2 := prime_ideal_of_norm_prime hp233.out _ NI233N2
def MulI233N0 : IdealMulLeCertificate' Table 
  ![![441, 321, 84, 59, -108]] ![![27, -38, 0, 4, 0]]
  ![![-7405, 6571, -5516, 9279, -4784]] where
 M := ![![![-7405, 6571, -5516, 9279, -4784]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI233N1 : IdealMulLeCertificate' Table 
  ![![-7405, 6571, -5516, 9279, -4784]] ![![-13, -9, -6, 3, 4]]
  ![![233, 0, 0, 0, 0]] where
 M := ![![![233, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC233 : ContainsPrimesAboveP 233 ![I233N0, I233N1, I233N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI233N0
    exact isPrimeI233N1
    exact isPrimeI233N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 233 (by decide) (𝕀 ⊙ MulI233N0 ⊙ MulI233N1)
instance hp239 : Fact (Nat.Prime 239) := {out := by norm_num}

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2057, 357, 779, -710, 120]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![2057, 357, 779, -710, 120]] 
 ![![239, 0, 0, 0, 0], ![0, 239, 0, 0, 0], ![0, 0, 239, 0, 0], ![0, 0, 0, 239, 0], ![51, 236, 124, 14, 1]] where
  M :=![![![2057, 357, 779, -710, 120], ![-720, 2348, -1132, 2347, -1420], ![8520, -6195, 5827, -9569, 4694], ![-6788, 7499, -5632, 9618, -5288], ![14638, -12797, 10711, -18354, 9205]]]
  hmulB := by decide  
  f := ![![![-205, 263, 47, -44, -6]], ![![36, -226, 172, 61, -88]], ![![528, -461, -337, 49, 122]], ![![-56, 165, -80, -40, 44]], ![![261, -396, 2, 74, -23]]]
  g := ![![![-17, -117, -59, -10, 120], ![300, 1412, 732, 93, -1420], ![-966, -4661, -2411, -315, 4694], ![1100, 5253, 2720, 350, -5288], ![-1903, -9143, -4731, -616, 9205]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P0 : CertificateIrreducibleZModOfList' 239 4 2 7 [34, 108, 38, 123, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [187, 236, 116, 80], [237, 233, 59, 71], [170, 8, 64, 88], [0, 1]]
 g := ![![[114, 116, 145, 165], [7, 237, 48, 163], [91, 65, 36, 134], [236, 173, 60, 10], [169, 224, 44], [145, 34, 116, 1], []], ![[218, 68, 176, 152, 21, 54], [100, 191, 53, 235, 175, 225], [38, 135, 115, 19, 61, 67], [137, 107, 80, 92, 67, 225], [219, 97, 93], [137, 85, 168, 221, 79, 176], [118, 72, 208, 52, 220, 62]], ![[37, 48, 195, 167, 56, 36], [146, 37, 14, 135, 198, 182], [166, 216, 131, 109, 103, 198], [69, 202, 71, 81, 47, 49], [35, 146, 121], [210, 184, 227, 133, 90, 44], [133, 23, 146, 201, 100, 128]], ![[81, 62, 106, 179, 80, 33], [114, 140, 153, 152, 116, 108], [119, 96, 173, 17, 42, 20], [118, 230, 83, 48, 56, 166], [126, 37, 11], [173, 67, 199, 154, 162, 34], [198, 25, 230, 233, 97, 83]]]
 h' := ![![[187, 236, 116, 80], [1, 198, 49, 72], [13, 39, 148, 101], [102, 37, 26, 143], [24, 171, 178, 201], [89, 153, 19, 98], [0, 0, 0, 1], [0, 1]], ![[237, 233, 59, 71], [107, 134, 222, 65], [11, 227, 117, 156], [63, 60, 107, 100], [65, 227, 70, 156], [126, 105, 56, 103], [214, 146, 106, 222], [187, 236, 116, 80]], ![[170, 8, 64, 88], [133, 152, 123, 216], [34, 16, 159, 74], [183, 103, 234, 20], [17, 26, 222, 13], [27, 127, 23, 228], [11, 78, 179, 182], [237, 233, 59, 71]], ![[0, 1], [231, 233, 84, 125], [150, 196, 54, 147], [208, 39, 111, 215], [28, 54, 8, 108], [201, 93, 141, 49], [76, 15, 193, 73], [170, 8, 64, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [34, 233, 143], []]
 b := ![[], [], [219, 131, 151, 136], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 4
  hpos := by decide
  P := [34, 108, 38, 123, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2735401244, -13917833950, 13771878664, 7958390730, 19639448882]
  a := ![1, -5, 12, -5, 21]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4202289934, -19451162218, -10131881936, -1117129262, 19639448882]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N0 B_one_repr
lemma NI239N0 : Nat.card (O ⧸ I239N0) = 3262808641 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N0

def I239N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-205, 263, 47, -44, -6]] i)))

def SI239N1: IdealEqSpanCertificate' Table ![![-205, 263, 47, -44, -6]] 
 ![![239, 0, 0, 0, 0], ![211, 1, 0, 0, 0], ![172, 0, 1, 0, 0], ![60, 0, 0, 1, 0], ![232, 0, 0, 0, 1]] where
  M :=![![![-205, 263, 47, -44, -6], ![36, -226, 172, 61, -88], ![528, -461, -337, 49, 122], ![-56, 165, -80, -40, 44], ![-350, 133, 397, 18, -167]]]
  hmulB := by decide  
  f := ![![![2057, 357, 779, -710, 120]], ![![1813, 325, 683, -617, 100]], ![![1516, 231, 585, -551, 106]], ![![488, 121, 172, -138, 8]], ![![2058, 293, 801, -766, 155]]]
  g := ![![![-250, 263, 47, -44, -6], ![146, -226, 172, 61, -88], ![521, -461, -337, 49, 122], ![-121, 165, -80, -40, 44], ![-247, 133, 397, 18, -167]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N1 : Nat.card (O ⧸ I239N1) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N1)

lemma isPrimeI239N1 : Ideal.IsPrime I239N1 := prime_ideal_of_norm_prime hp239.out _ NI239N1
def MulI239N0 : IdealMulLeCertificate' Table 
  ![![2057, 357, 779, -710, 120]] ![![-205, 263, 47, -44, -6]]
  ![![239, 0, 0, 0, 0]] where
 M := ![![![239, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I241N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0, 0, 0]] i)))

def SI241N0: IdealEqSpanCertificate' Table ![![241, 0, 0, 0, 0]] 
 ![![241, 0, 0, 0, 0], ![0, 241, 0, 0, 0], ![0, 0, 241, 0, 0], ![0, 0, 0, 241, 0], ![0, 0, 0, 0, 241]] where
  M :=![![![241, 0, 0, 0, 0], ![0, 241, 0, 0, 0], ![0, 0, 241, 0, 0], ![0, 0, 0, 241, 0], ![0, 0, 0, 0, 241]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P241P0 : CertificateIrreducibleZModOfList' 241 5 2 7 [20, 176, 157, 189, 70, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [92, 180, 209, 69, 80], [175, 12, 35, 213, 233], [58, 145, 215, 236, 184], [87, 144, 23, 205, 226], [0, 1]]
 g := ![![[140, 145, 10, 169, 36], [178, 95, 110, 201], [146, 150, 228, 24], [42, 42, 3, 235], [157, 54, 74, 30, 47], [132, 171, 1], []], ![[34, 130, 67, 149, 39, 3, 122, 216], [31, 52, 156, 82], [82, 141, 148, 90], [94, 167, 6, 187], [144, 115, 180, 67, 188, 169, 74, 200], [33, 18, 103, 130, 44, 150, 69, 181], [160, 128, 39, 33, 121, 174, 97, 116]], ![[25, 193, 127, 49, 143, 172, 223, 125], [196, 124, 151, 96], [213, 172, 127, 40], [117, 54, 91, 187], [231, 230, 58, 45, 155, 138, 108, 145], [88, 2, 145, 58, 14, 170, 97, 164], [109, 89, 215, 148, 85, 210, 98, 211]], ![[62, 194, 156, 49, 158, 12, 172, 34], [89, 61, 207, 161], [16, 192, 168, 209], [145, 176, 236, 133], [46, 196, 229, 111, 72, 26, 134, 56], [91, 46, 135, 201, 143, 60, 120, 175], [207, 55, 32, 179, 29, 145, 67, 136]], ![[3, 22, 151, 81, 120, 228, 34, 67], [194, 237, 239, 15], [108, 208, 39, 229], [225, 14, 226, 196], [223, 86, 224, 110, 205, 45, 2, 2], [38, 230, 174, 153, 102, 18, 43, 154], [158, 117, 127, 171, 138, 234, 111, 240]]]
 h' := ![![[92, 180, 209, 69, 80], [103, 208, 94, 204, 6], [17, 147, 214, 165, 116], [173, 176, 71, 98, 54], [234, 88, 44, 202, 200], [11, 99, 11, 85, 218], [0, 0, 0, 1], [0, 1]], ![[175, 12, 35, 213, 233], [115, 90, 135, 67, 39], [129, 33, 144, 110, 75], [166, 182, 222, 238, 50], [29, 213, 122, 161, 123], [149, 46, 212, 220, 72], [191, 123, 216, 233, 105], [92, 180, 209, 69, 80]], ![[58, 145, 215, 236, 184], [169, 206, 166, 187, 193], [165, 82, 99, 217, 133], [150, 209, 131, 126, 47], [70, 189, 56, 63, 118], [202, 235, 42, 195, 129], [6, 169, 166, 4, 231], [175, 12, 35, 213, 233]], ![[87, 144, 23, 205, 226], [147, 185, 72, 37, 149], [177, 102, 166, 138, 142], [225, 75, 234, 101, 152], [76, 98, 166, 227, 55], [21, 55, 42, 12, 151], [100, 52, 106, 75, 65], [58, 145, 215, 236, 184]], ![[0, 1], [3, 34, 15, 228, 95], [73, 118, 100, 93, 16], [233, 81, 65, 160, 179], [40, 135, 94, 70, 227], [117, 47, 175, 211, 153], [64, 138, 235, 169, 81], [87, 144, 23, 205, 226]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [218, 44, 65, 101], [], [], []]
 b := ![[], [191, 116, 172, 17, 62], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 5
  hpos := by decide
  P := [20, 176, 157, 189, 70, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1726042, -1827262, 1540713, -1998131, 1463111]
  a := ![4, 0, -1, 1, -1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![7162, -7582, 6393, -8291, 6071]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI241N0 : Ideal.IsPrime I241N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI241N0 B_one_repr
lemma NI241N0 : Nat.card (O ⧸ I241N0) = 812990017201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI241N0

def PBC241 : ContainsPrimesAboveP 241 ![I241N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI241N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![241, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 241 (by decide) 𝕀

instance hp251 : Fact (Nat.Prime 251) := {out := by norm_num}

def I251N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, -94, 77, 49, -26]] i)))

def SI251N0: IdealEqSpanCertificate' Table ![![-3, -94, 77, 49, -26]] 
 ![![251, 0, 0, 0, 0], ![0, 251, 0, 0, 0], ![0, 0, 251, 0, 0], ![126, 6, 24, 1, 0], ![170, 208, 245, 0, 1]] where
  M :=![![![-3, -94, 77, 49, -26], ![156, -207, -122, 124, 98], ![-588, 448, 39, 346, 248], ![-640, 4, 224, 807, 346], ![-346, -646, 101, 1263, 559]]]
  hmulB := by decide  
  f := ![![![2947, 1526, 771, -143, -384]], ![![2304, 1167, 612, -134, -286]], ![![1716, 968, 421, -14, -268]], ![![1706, 890, 444, -77, -226]], ![![5580, 2946, 1440, -221, -759]]]
  g := ![![![-7, 20, 21, 49, -26], ![-128, -85, -108, 124, 98], ![-344, -212, -275, 346, 248], ![-642, -306, -414, 807, 346], ![-1014, -496, -666, 1263, 559]]]
  hle1 := by decide   
  hle2 := by decide  


def P251P0 : CertificateIrreducibleZModOfList' 251 3 2 7 [3, 67, 36, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [229, 199, 36], [237, 51, 215], [0, 1]]
 g := ![![[91, 249, 108], [238, 162, 117], [82, 100], [130, 161, 93], [137, 173, 93], [153, 85, 41], [1]], ![[222, 50, 59, 80], [34, 107, 198, 114], [50, 175], [206, 73, 167, 124], [19, 214, 214, 25], [237, 159, 29, 195], [16, 39, 206, 221]], ![[225, 107, 139, 111], [155, 114, 42, 160], [195, 208], [178, 132, 67, 111], [211, 39, 65, 220], [43, 138, 62, 138], [128, 41, 173, 30]]]
 h' := ![![[229, 199, 36], [39, 135, 46], [250, 5, 86], [112, 92, 241], [91, 183, 120], [43, 45, 120], [248, 184, 215], [0, 1]], ![[237, 51, 215], [247, 146, 178], [243, 249, 48], [49, 206, 41], [143, 131, 158], [119, 28, 210], [97, 113, 19], [229, 199, 36]], ![[0, 1], [231, 221, 27], [111, 248, 117], [52, 204, 220], [112, 188, 224], [239, 178, 172], [135, 205, 17], [237, 51, 215]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [185, 221], []]
 b := ![[], [48, 90, 210], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI251N0 : CertifiedPrimeIdeal' SI251N0 251 where
  n := 3
  hpos := by decide
  P := [3, 67, 36, 1]
  hirr := P251P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![91394535, 11334203, -21498516, -140153009, -62129740]
  a := ![7, 21, 7, -50, -11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![112799719, 54881427, 73960000, -140153009, -62129740]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI251N0 : Ideal.IsPrime I251N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI251N0 B_one_repr
lemma NI251N0 : Nat.card (O ⧸ I251N0) = 15813251 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI251N0

def I251N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2947, -1526, -771, 143, 384]] i)))

def SI251N1: IdealEqSpanCertificate' Table ![![-2947, -1526, -771, 143, 384]] 
 ![![251, 0, 0, 0, 0], ![0, 251, 0, 0, 0], ![24, 178, 1, 0, 0], ![90, 215, 0, 1, 0], ![124, 40, 0, 0, 1]] where
  M :=![![![-2947, -1526, -771, 143, 384], ![-2304, -1167, -612, 134, 286], ![-1716, -968, -421, 14, 268], ![-1876, -880, -522, 169, 194], ![62, -130, 71, -141, 81]]]
  hmulB := by decide  
  f := ![![![3, 94, -77, -49, 26]], ![![-156, 207, 122, -124, -98]], ![![-108, 154, 79, -94, -68]], ![![-130, 211, 76, -127, -76]], ![![-22, 82, -19, -49, -5]]]
  g := ![![![-179, 357, -771, 143, 384], ![-140, 269, -612, 134, 286], ![-104, 240, -421, 14, 268], ![-114, 191, -522, 169, 194], ![4, 57, 71, -141, 81]]]
  hle1 := by decide   
  hle2 := by decide  


def P251P1 : CertificateIrreducibleZModOfList' 251 2 2 7 [187, 96, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [155, 250], [0, 1]]
 g := ![![[124, 25], [222, 197], [211], [91, 65], [199, 195], [239, 49], [155, 1]], ![[234, 226], [135, 54], [211], [126, 186], [53, 56], [53, 202], [59, 250]]]
 h' := ![![[155, 250], [152, 5], [41, 166], [51, 151], [186, 127], [236, 114], [131, 244], [0, 1]], ![[0, 1], [174, 246], [169, 85], [113, 100], [42, 124], [85, 137], [50, 7], [155, 250]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [175]]
 b := ![[], [184, 213]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI251N1 : CertifiedPrimeIdeal' SI251N1 251 where
  n := 2
  hpos := by decide
  P := [187, 96, 1]
  hirr := P251P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-76, -1142, 1943, -276, 2196]
  a := ![1, 6, 4, -15, 0]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1172, -1496, 1943, -276, 2196]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI251N1 : Ideal.IsPrime I251N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI251N1 B_one_repr
lemma NI251N1 : Nat.card (O ⧸ I251N1) = 63001 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI251N1
def MulI251N0 : IdealMulLeCertificate' Table 
  ![![-3, -94, 77, 49, -26]] ![![-2947, -1526, -771, 143, 384]]
  ![![251, 0, 0, 0, 0]] where
 M := ![![![-251, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC251 : ContainsPrimesAboveP 251 ![I251N0, I251N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI251N0
    exact isPrimeI251N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 251 (by decide) (𝕀 ⊙ MulI251N0)


lemma PB1705I5_primes (p : ℕ) :
  p ∈ Set.range ![199, 211, 223, 227, 229, 233, 239, 241, 251] ↔ Nat.Prime p ∧ 197 < p ∧ p ≤ 251 := by
  rw [← List.mem_ofFn']
  convert primes_range 197 251 (by omega)

def PB1705I5 : PrimesBelowBoundCertificateInterval O 197 251 1705 where
  m := 9
  g := ![1, 3, 2, 3, 3, 3, 2, 1, 2]
  P := ![199, 211, 223, 227, 229, 233, 239, 241, 251]
  hP := PB1705I5_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I199N0]
    · exact ![I211N0, I211N1, I211N2]
    · exact ![I223N0, I223N1]
    · exact ![I227N0, I227N1, I227N2]
    · exact ![I229N0, I229N1, I229N2]
    · exact ![I233N0, I233N1, I233N2]
    · exact ![I239N0, I239N1]
    · exact ![I241N0]
    · exact ![I251N0, I251N1]
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
    · exact ![312079600999]
    · exact ![44521, 44521, 211]
    · exact ![11089567, 49729]
    · exact ![11697083, 227, 227]
    · exact ![52441, 52441, 229]
    · exact ![12649337, 233, 233]
    · exact ![3262808641, 239]
    · exact ![812990017201]
    · exact ![15813251, 63001]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI199N0
    · dsimp ; intro j
      fin_cases j
      exact NI211N0
      exact NI211N1
      exact NI211N2
    · dsimp ; intro j
      fin_cases j
      exact NI223N0
      exact NI223N1
    · dsimp ; intro j
      fin_cases j
      exact NI227N0
      exact NI227N1
      exact NI227N2
    · dsimp ; intro j
      fin_cases j
      exact NI229N0
      exact NI229N1
      exact NI229N2
    · dsimp ; intro j
      fin_cases j
      exact NI233N0
      exact NI233N1
      exact NI233N2
    · dsimp ; intro j
      fin_cases j
      exact NI239N0
      exact NI239N1
    · dsimp ; intro j
      fin_cases j
      exact NI241N0
    · dsimp ; intro j
      fin_cases j
      exact NI251N0
      exact NI251N1
  β := ![I211N2, I227N1, I227N2, I229N2, I233N1, I233N2, I239N1]
  Il := ![[], [I211N2], [], [I227N1, I227N2], [I229N2], [I233N1, I233N2], [I239N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
