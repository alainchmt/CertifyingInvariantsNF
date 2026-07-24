
import IdealArithmetic.Examples.NF5_1_72900000_2.RI5_1_72900000_2
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


def P199P0 : CertificateIrreducibleZModOfList' 199 5 2 7 [8, 63, 136, 116, 77, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [56, 43, 194, 34, 79], [113, 88, 132, 189, 11], [74, 194, 81, 82, 82], [78, 72, 190, 93, 27], [0, 1]]
 g := ![![[192, 184, 168, 119, 64], [53, 88, 52, 143, 79], [56, 83, 41, 57, 29], [94, 47, 7, 63], [111, 197, 66, 172], [122, 1], []], ![[86, 71, 125, 38, 148, 124, 183, 125], [81, 170, 29, 112, 102, 164, 21, 31], [36, 102, 35, 190, 29, 13, 90, 70], [7, 128, 46, 124], [144, 53, 146, 94], [23, 11, 6, 165], [60, 131, 127, 146, 8, 30, 4, 116]], ![[79, 38, 49, 38, 178, 29, 1, 95], [124, 14, 135, 150, 139, 53, 108, 171], [153, 109, 190, 143, 101, 89, 85, 37], [63, 122, 14, 31], [85, 104, 39, 35], [126, 10, 68, 81], [139, 116, 197, 186, 89, 170, 149, 137]], ![[139, 164, 88, 118, 160, 150, 115, 101], [101, 58, 144, 182, 20, 81, 76, 6], [1, 146, 68, 107, 149, 101, 34, 39], [144, 132, 70, 32], [87, 35, 184, 56], [192, 163, 12, 117], [141, 117, 69, 191, 118, 145, 136, 138]], ![[150, 165, 8, 176, 40, 2, 148, 41], [26, 181, 136, 98, 156, 64, 174, 167], [8, 74, 3, 40, 140, 132, 133, 195], [146, 134, 98, 90], [186, 143, 42, 115], [86, 124, 103, 106], [2, 68, 173, 58, 28, 141, 6, 181]]]
 h' := ![![[56, 43, 194, 34, 79], [173, 49, 89, 95, 191], [149, 152, 150, 158, 26], [168, 13, 88, 42, 32], [70, 146, 65, 113, 62], [19, 67, 61, 40, 42], [0, 0, 0, 1], [0, 1]], ![[113, 88, 132, 189, 11], [110, 89, 176, 42, 16], [133, 112, 67, 91, 9], [61, 184, 55, 33, 4], [52, 79, 180, 60, 70], [72, 43, 164, 63, 166], [16, 124, 0, 67, 31], [56, 43, 194, 34, 79]], ![[74, 194, 81, 82, 82], [153, 5, 33, 33, 9], [136, 48, 47, 88, 92], [22, 197, 163, 24, 54], [39, 20, 143, 105, 164], [91, 68, 128, 194, 45], [30, 22, 14, 96, 9], [113, 88, 132, 189, 11]], ![[78, 72, 190, 93, 27], [22, 133, 10, 180, 18], [142, 1, 116, 4, 36], [77, 117, 76, 154, 128], [45, 147, 4, 116, 119], [12, 14, 149, 56, 97], [126, 178, 97, 81, 52], [74, 194, 81, 82, 82]], ![[0, 1], [65, 122, 90, 48, 164], [74, 85, 18, 57, 36], [137, 86, 16, 145, 180], [67, 6, 6, 4, 182], [180, 7, 95, 45, 48], [120, 74, 88, 153, 107], [78, 72, 190, 93, 27]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [84, 183, 4, 183], [], [], []]
 b := ![[], [20, 106, 20, 179, 106], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 5
  hpos := by decide
  P := [8, 63, 136, 116, 77, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3182597163430, -4640802242118, -3189465799670, 3449729462269, -6558466736919]
  a := ![10, -11, -18, 14, -145]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-15992950570, -23320614282, -16027466330, 17335323931, -32957119281]
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

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5181, -1302, 2176, -600, 5966]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![-5181, -1302, 2176, -600, 5966]] 
 ![![211, 0, 0, 0, 0], ![0, 211, 0, 0, 0], ![0, 0, 211, 0, 0], ![0, 0, 0, 211, 0], ![38, 174, 103, 157, 1]] where
  M :=![![![-5181, -1302, 2176, -600, 5966], ![2400, -1615, 464, -190, 996], ![760, 2636, -1949, 608, -5044], ![-2432, -1852, 1848, -553, 5000], ![-828, -482, 532, -156, 1433]]]
  hmulB := by decide  
  f := ![![![-7, -22, -24, 4, -54]], ![![-16, -45, -48, 6, -92]], ![![-24, -84, -95, 8, -204]], ![![-32, -196, -232, 61, -760]], ![![-50, -228, -263, 55, -751]]]
  g := ![![![-1099, -4926, -2902, -4442, 5966], ![-168, -829, -484, -742, 996], ![912, 4172, 2453, 3756, -5044], ![-912, -4132, -2432, -3723, 5000], ![-262, -1184, -697, -1067, 1433]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 4 2 7 [96, 116, 7, 5, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [48, 9, 72, 131], [74, 185, 198, 65], [84, 16, 152, 15], [0, 1]]
 g := ![![[105, 19, 82, 144], [71, 111, 113, 100], [103, 71, 69], [108, 151, 64], [26, 119, 173, 123], [18, 206, 1], []], ![[142, 62, 30, 134, 100, 28], [39, 82, 17, 122, 82, 202], [33, 199, 209], [53, 150, 184], [13, 11, 131, 50, 136, 18], [34, 86, 203], [42, 125, 110, 94, 76, 97]], ![[95, 173, 142, 12, 204, 56], [131, 199, 68, 55, 23, 154], [201, 24, 34], [49, 133, 105], [78, 169, 63, 38, 188, 125], [41, 57, 173], [208, 143, 186, 144, 79, 114]], ![[62, 108, 157, 143, 122, 111], [127, 204, 167, 16, 67, 42], [151, 188, 139], [150, 149, 84], [25, 31, 201, 155, 97, 177], [91, 102, 56], [30, 193, 49, 45, 59, 210]]]
 h' := ![![[48, 9, 72, 131], [147, 154, 160, 199], [30, 16, 210, 10], [1, 106, 62, 51], [36, 31, 142, 203], [171, 80, 147, 40], [0, 0, 0, 1], [0, 1]], ![[74, 185, 198, 65], [151, 209, 71, 50], [92, 2, 115, 43], [99, 5, 16, 118], [171, 173, 200, 124], [137, 170, 79, 10], [5, 182, 151, 186], [48, 9, 72, 131]], ![[84, 16, 152, 15], [176, 51, 31, 112], [200, 108, 133, 174], [154, 163, 61, 178], [146, 11, 209, 152], [129, 98, 165, 88], [181, 60, 200, 54], [74, 185, 198, 65]], ![[0, 1], [34, 8, 160, 61], [36, 85, 175, 195], [124, 148, 72, 75], [133, 207, 82, 154], [37, 74, 31, 73], [79, 180, 71, 181], [84, 16, 152, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [193, 127, 92], []]
 b := ![[], [], [203, 197, 190, 70], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 4
  hpos := by decide
  P := [96, 116, 7, 5, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3625594993, -715644328, 1424744235, -2163454387, 28218341800]
  a := ![-9, -52, 17, -13, 132]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5099159163, -23273493448, -13768078015, -21006839417, 28218341800]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 1982119441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, -22, -24, 4, -54]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![-7, -22, -24, 4, -54]] 
 ![![211, 0, 0, 0, 0], ![172, 1, 0, 0, 0], ![167, 0, 1, 0, 0], ![183, 0, 0, 1, 0], ![139, 0, 0, 0, 1]] where
  M :=![![![-7, -22, -24, 4, -54], ![-16, -45, -48, 6, -92], ![-24, -84, -95, 8, -204], ![-32, -196, -232, 61, -760], ![-4, -18, -20, 8, -69]]]
  hmulB := by decide  
  f := ![![![-5181, -1302, 2176, -600, 5966]], ![![-4212, -1069, 1776, -490, 4868]], ![![-4097, -1018, 1713, -472, 4698]], ![![-4505, -1138, 1896, -523, 5198]], ![![-3417, -860, 1436, -396, 3937]]]
  g := ![![![69, -22, -24, 4, -54], ![130, -45, -48, 6, -92], ![271, -84, -95, 8, -204], ![791, -196, -232, 61, -760], ![69, -18, -20, 8, -69]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![-5181, -1302, 2176, -600, 5966]] ![![-7, -22, -24, 4, -54]]
  ![![211, 0, 0, 0, 0]] where
 M := ![![![211, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC211 : ContainsPrimesAboveP 211 ![I211N0, I211N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI211N0
    exact isPrimeI211N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 211 (by decide) (𝕀 ⊙ MulI211N0)
instance hp223 : Fact (Nat.Prime 223) := {out := by norm_num}

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![231, 311, 198, -209, 212]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![231, 311, 198, -209, 212]] 
 ![![223, 0, 0, 0, 0], ![0, 223, 0, 0, 0], ![0, 0, 223, 0, 0], ![0, 0, 0, 223, 0], ![202, 215, 205, 19, 1]] where
  M :=![![![231, 311, 198, -209, 212], ![836, -393, -940, 1240, -10850], ![-4960, -5054, -2563, 2470, 6820], ![-9880, 11740, 19056, -24203, 184180], ![1204, 3209, 2816, -3245, 13843]]]
  hmulB := by decide  
  f := ![![![-3, 113, 134, -21, 302]], ![![84, 215, 268, -42, 594]], ![![168, 510, 515, -74, 1128]], ![![296, 1000, 1120, -169, 2476]], ![![258, 864, 949, -142, 2095]]]
  g := ![![![-191, -203, -194, -19, 212], ![9832, 10459, 9970, 930, -10850], ![-6200, -6598, -6281, -570, 6820], ![-166880, -177520, -169228, -15801, 184180], ![-12534, -13332, -12713, -1194, 13843]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 4 2 7 [78, 153, 201, 98, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [25, 174, 110, 207], [142, 80, 165, 71], [181, 191, 171, 168], [0, 1]]
 g := ![![[54, 214, 31, 133], [12, 176, 53, 179], [28, 17, 9, 220], [31, 79, 136, 66], [198, 158, 66, 37], [37, 125, 1], []], ![[122, 32, 69, 12, 60, 163], [132, 69, 130, 219, 222, 22], [160, 172, 179, 123, 188, 190], [71, 136, 159, 189], [154, 209, 17, 135, 165, 137], [35, 140, 89], [84, 91, 133, 93, 194, 141]], ![[78, 47, 97, 209, 32, 189], [56, 78, 26, 63, 193, 6], [103, 14, 44, 68, 62, 52], [145, 117, 78, 164, 20, 174], [10, 60, 66, 190, 201, 160], [167, 219, 60], [209, 53, 9, 164, 94, 219]], ![[169, 54, 174, 220, 129, 54], [25, 189, 142, 37, 118, 108], [212, 12, 104, 137, 97, 48], [218, 198, 155, 147, 178, 96], [112, 161, 54, 55, 115, 104], [22, 199, 56], [174, 203, 8, 63, 73, 206]]]
 h' := ![![[25, 174, 110, 207], [179, 155, 186, 170], [46, 75, 161, 198], [35, 149, 150, 144], [166, 144, 55, 206], [13, 199, 120, 86], [0, 0, 0, 1], [0, 1]], ![[142, 80, 165, 71], [83, 59, 145, 174], [136, 207, 166, 204], [24, 9, 48, 4], [161, 172, 91], [163, 12, 132, 138], [153, 121, 163, 138], [25, 174, 110, 207]], ![[181, 191, 171, 168], [30, 150, 171, 12], [136, 134, 50, 32], [1, 98, 221, 67], [136, 62, 26, 137], [34, 38, 115, 130], [168, 52, 172, 196], [142, 80, 165, 71]], ![[0, 1], [155, 82, 167, 90], [90, 30, 69, 12], [64, 190, 27, 8], [67, 68, 51, 103], [63, 197, 79, 92], [202, 50, 111, 111], [181, 191, 171, 168]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [164, 211, 157], []]
 b := ![[], [], [12, 153, 131, 114], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 4
  hpos := by decide
  P := [78, 153, 201, 98, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![16646041, 36584747, 30302659, -34563190, 130842235]
  a := ![3, -5, -5, 4, -43]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-118446123, -125984286, -120145092, -11302985, 130842235]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 2472973441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, 113, 134, -21, 302]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![-3, 113, 134, -21, 302]] 
 ![![223, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![174, 0, 1, 0, 0], ![120, 0, 0, 1, 0], ![184, 0, 0, 0, 1]] where
  M :=![![![-3, 113, 134, -21, 302], ![84, 215, 268, -42, 594], ![168, 510, 515, -74, 1128], ![296, 1000, 1120, -169, 2476], ![16, 71, 84, -13, 187]]]
  hmulB := by decide  
  f := ![![![231, 311, 198, -209, 212]], ![![11, 8, 2, -1, -42]], ![![158, 220, 143, -152, 196]], ![![80, 220, 192, -221, 940]], ![![196, 271, 176, -187, 237]]]
  g := ![![![-346, 113, 134, -21, 302], ![-683, 215, 268, -42, 594], ![-1308, 510, 515, -74, 1128], ![-2856, 1000, 1120, -169, 2476], ![-215, 71, 84, -13, 187]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N1 : Nat.card (O ⧸ I223N1) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N1)

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := prime_ideal_of_norm_prime hp223.out _ NI223N1
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![231, 311, 198, -209, 212]] ![![-3, 113, 134, -21, 302]]
  ![![223, 0, 0, 0, 0]] where
 M := ![![![223, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![497, -806, -1576, 1764, -11998]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![497, -806, -1576, 1764, -11998]] 
 ![![227, 0, 0, 0, 0], ![0, 227, 0, 0, 0], ![0, 0, 227, 0, 0], ![107, 95, 202, 1, 0], ![108, 84, 188, 0, 1]] where
  M :=![![![497, -806, -1576, 1764, -11998], ![-7056, -4445, -456, -162, 30324], ![648, 22620, 24745, -29808, 172548], ![119232, 53964, -13488, 31045, -693576], ![10636, -4658, -11740, 15456, -136197]]]
  hmulB := by decide  
  f := ![![![-336463125, -1068511238, -1169073232, 174483336, -2577908122]], ![![-697933344, -2216437903, -2425036008, 361934874, -5347415244]], ![![-1447739496, -4597609092, -5030309029, 750769992, -11092268772]], ![![-1752210045, -5564521005, -6088221006, 908662591, -13425056662]], ![![-1618316536, -5139313282, -5622995232, 839227980, -12399193381]]]
  g := ![![![4879, 3698, 8360, 1764, -11998], ![-14382, -11173, -24972, -162, 30324], ![-68040, -51276, -116269, -29808, 172548], ![315875, 243899, 546730, 31045, -693576], ![57560, 43910, 98992, 15456, -136197]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 3 2 7 [97, 102, 188, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [187, 59, 93], [79, 167, 134], [0, 1]]
 g := ![![[87, 185, 16], [197, 54, 90], [173, 28], [100, 36], [29, 3], [122, 61, 159], [1]], ![[85, 130, 98, 8], [203, 82, 177, 88], [107, 214], [0, 122], [169, 182], [96, 172, 66, 66], [73, 177, 97, 96]], ![[29, 86, 76, 113], [179, 210, 134, 131], [103, 172], [154, 97], [173, 40], [97, 95, 10, 136], [35, 218, 61, 131]]]
 h' := ![![[187, 59, 93], [186, 140, 223], [27, 218, 192], [163, 201, 153], [130, 194, 6], [197, 128, 177], [130, 125, 39], [0, 1]], ![[79, 167, 134], [108, 67, 94], [13, 23, 128], [75, 7, 206], [204, 14, 203], [88, 139, 149], [197, 32, 205], [187, 59, 93]], ![[0, 1], [2, 20, 137], [130, 213, 134], [70, 19, 95], [88, 19, 18], [57, 187, 128], [5, 70, 210], [79, 167, 134]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [132, 153], []]
 b := ![[], [42, 184, 13], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 3
  hpos := by decide
  P := [97, 102, 188, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![15948184, 38256961, 32761507, -36918859, 149217052]
  a := ![-15, 35, 27, -23, 218]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-53520597, -39597726, -90583413, -36918859, 149217052]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 11697083 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-907, -4219, -4118, 4853, -24552]] i)))

def SI227N1: IdealEqSpanCertificate' Table ![![-907, -4219, -4118, 4853, -24552]] 
 ![![227, 0, 0, 0, 0], ![102, 1, 0, 0, 0], ![38, 0, 1, 0, 0], ![210, 0, 0, 1, 0], ![173, 0, 0, 0, 1]] where
  M :=![![![-907, -4219, -4118, 4853, -24552], ![-19412, -6047, 5200, -8684, 134162], ![34736, 80014, 67327, -76858, 301300], ![307432, 28604, -156692, 227175, -2649964], ![13220, -31293, -42756, 53197, -368403]]]
  hmulB := by decide  
  f := ![![![12062860051, 38308214759, 41913558706, -6255568387, 92423041158]], ![![5530546250, 17563442877, 19216410860, -2868035452, 42373856734]], ![![2247986654, 7138966636, 7810844203, -1165762860, 17223590588]], ![![11633774858, 36945562138, 40422661232, -6033053015, 89135482600]], ![![9227776277, 29304794540, 32062789510, -4785348194, 70701238597]]]
  g := ![![![16803, -4219, -4118, 4853, -24552], ![-92452, -6047, 5200, -8684, 134162], ![-205594, 80014, 67327, -76858, 301300], ![1824146, 28604, -156692, 227175, -2649964], ![252829, -31293, -42756, 53197, -368403]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N1 : Nat.card (O ⧸ I227N1) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N1)

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := prime_ideal_of_norm_prime hp227.out _ NI227N1

def I227N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-21, -19, 18, -7, 70]] i)))

def SI227N2: IdealEqSpanCertificate' Table ![![-21, -19, 18, -7, 70]] 
 ![![227, 0, 0, 0, 0], ![150, 1, 0, 0, 0], ![200, 0, 1, 0, 0], ![191, 0, 0, 1, 0], ![47, 0, 0, 0, 1]] where
  M :=![![![-21, -19, 18, -7, 70], ![28, 21, 2, -10, 14], ![40, 2, -35, 48, -496], ![-192, -264, -158, 173, -192], ![-40, -25, 2, -5, 197]]]
  hmulB := by decide  
  f := ![![![-550579, -1748489, -1913066, 285525, -4218480]], ![![-368850, -1171367, -1281622, 191282, -2826090]], ![![-495528, -1573662, -1721783, 256976, -3796684]], ![![-484911, -1539945, -1684892, 251470, -3715336]], ![![-115571, -367022, -401568, 59934, -885493]]]
  g := ![![![-12, -19, 18, -7, 70], ![-10, 21, 2, -10, 14], ![92, 2, -35, 48, -496], ![207, -264, -158, 173, -192], ![-22, -25, 2, -5, 197]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N2 : Nat.card (O ⧸ I227N2) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N2)

lemma isPrimeI227N2 : Ideal.IsPrime I227N2 := prime_ideal_of_norm_prime hp227.out _ NI227N2
def MulI227N0 : IdealMulLeCertificate' Table 
  ![![497, -806, -1576, 1764, -11998]] ![![-907, -4219, -4118, 4853, -24552]]
  ![![344147845, 302585845, 124236602, -106981453, -849623018]] where
 M := ![![![344147845, 302585845, 124236602, -106981453, -849623018]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI227N1 : IdealMulLeCertificate' Table 
  ![![344147845, 302585845, 124236602, -106981453, -849623018]] ![![-21, -19, 18, -7, 70]]
  ![![227, 0, 0, 0, 0]] where
 M := ![![![60740122691, 49547645936, 17655375368, -13731212748, -180130099182]]]
 hmul := by decide  
 g := ![![![![267577633, 218271568, 77776984, -60489924, -793524666]]]]
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

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-547, -245, 301, -86, 812]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![-547, -245, 301, -86, 812]] 
 ![![229, 0, 0, 0, 0], ![0, 229, 0, 0, 0], ![112, 216, 1, 0, 0], ![82, 172, 0, 1, 0], ![26, 166, 0, 0, 1]] where
  M :=![![![-547, -245, 301, -86, 812], ![344, -79, -35, 5, -116], ![-20, 248, -160, 51, -406], ![-204, -222, 199, -60, 522], ![-76, -63, 61, -18, 161]]]
  hmulB := by decide  
  f := ![![![-11, -53, -63, 10, -174]], ![![-40, -145, -157, 51, -464]], ![![-44, -164, -180, 53, -522]], ![![-34, -128, -141, 40, -406]], ![![-30, -111, -121, 38, -357]]]
  g := ![![![-211, -809, 301, -86, 812], ![30, 113, -35, 5, -116], ![106, 408, -160, 51, -406], ![-136, -522, 199, -60, 522], ![-42, -161, 61, -18, 161]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 2 2 7 [174, 200, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [29, 228], [0, 1]]
 g := ![![[38, 204], [62], [130, 161], [121], [213], [12, 171], [29, 1]], ![[0, 25], [62], [219, 68], [121], [213], [162, 58], [58, 228]]]
 h' := ![![[29, 228], [57, 77], [51, 156], [144, 187], [78, 11], [202, 199], [221, 209], [0, 1]], ![[0, 1], [0, 152], [224, 73], [71, 42], [168, 218], [19, 30], [99, 20], [29, 228]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [120]]
 b := ![[], [46, 60]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 2
  hpos := by decide
  P := [174, 200, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1989, 29956, 34813, -43782, 264330]
  a := ![19, -20, -33, 30, -276]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-31369, -191432, 34813, -43782, 264330]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 52441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def I229N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7837, -5892, -1723, 1103, 27156]] i)))

def SI229N1: IdealEqSpanCertificate' Table ![![-7837, -5892, -1723, 1103, 27156]] 
 ![![229, 0, 0, 0, 0], ![51, 1, 0, 0, 0], ![147, 0, 1, 0, 0], ![60, 0, 0, 1, 0], ![94, 0, 0, 0, 1]] where
  M :=![![![-7837, -5892, -1723, 1103, 27156], ![-4412, 23731, 28985, -35497, 226910], ![141988, 80510, 2162, 15057, -697366], ![-60228, -495150, -511457, 609186, -3310890], ![-65616, -79092, -47387, 48973, -5437]]]
  hmulB := by decide  
  f := ![![![-3031018329, -9625651996, -10531562131, 1571828069, -23223010204]], ![![-702485795, -2230895057, -2440853862, 364295682, -5382294994]], ![![-2002627131, -6359774106, -6958318887, 1038524086, -15343698162]], ![![-912289336, -2897171438, -3169836275, 473095782, -6989764598]], ![![-1252765342, -3978426360, -4352852607, 649660119, -9598418473]]]
  g := ![![![-9052, -5892, -1723, 1103, 27156], ![-107752, 23731, 28985, -35497, 226910], ![263612, 80510, 2162, 15057, -697366], ![1637769, -495150, -511457, 609186, -3310890], ![37147, -79092, -47387, 48973, -5437]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N1 : Nat.card (O ⧸ I229N1) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N1)

lemma isPrimeI229N1 : Ideal.IsPrime I229N1 := prime_ideal_of_norm_prime hp229.out _ NI229N1

def I229N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-15215, -48185, -52701, 7864, -116202]] i)))

def SI229N2: IdealEqSpanCertificate' Table ![![-15215, -48185, -52701, 7864, -116202]] 
 ![![229, 0, 0, 0, 0], ![80, 1, 0, 0, 0], ![12, 0, 1, 0, 0], ![185, 0, 0, 1, 0], ![57, 0, 0, 0, 1]] where
  M :=![![![-15215, -48185, -52701, 7864, -116202], ![-31456, -99961, -109339, 16317, -241100], ![-65268, -207288, -226842, 33859, -500214], ![-135436, -430046, -470489, 70218, -1037462], ![-9856, -31279, -34215, 5106, -75445]]]
  hmulB := by decide  
  f := ![![![-5407, -6881, -4313, 4528, -3352]], ![![-1968, -2363, -1413, 1459, -112]], ![![208, 128, 14, 9, -946]], ![![-3455, -6751, -5364, 6038, -20570]], ![![-1471, -2028, -1346, 1440, -2131]]]
  g := ![![![42099, -48185, -52701, 7864, -116202], ![87343, -99961, -109339, 16317, -241100], ![181171, -207288, -226842, 33859, -500214], ![375804, -430046, -470489, 70218, -1037462], ![27331, -31279, -34215, 5106, -75445]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N2 : Nat.card (O ⧸ I229N2) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N2)

lemma isPrimeI229N2 : Ideal.IsPrime I229N2 := prime_ideal_of_norm_prime hp229.out _ NI229N2

def I229N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-15849, -50332, -55069, 8219, -121432]] i)))

def SI229N3: IdealEqSpanCertificate' Table ![![-15849, -50332, -55069, 8219, -121432]] 
 ![![229, 0, 0, 0, 0], ![111, 1, 0, 0, 0], ![45, 0, 1, 0, 0], ![43, 0, 0, 1, 0], ![138, 0, 0, 0, 1]] where
  M :=![![![-15849, -50332, -55069, 8219, -121432], ![-32876, -104405, -114231, 17049, -251890], ![-68196, -216570, -236952, 35365, -522498], ![-141460, -449234, -491513, 73356, -1083818], ![-10288, -32672, -35747, 5335, -78825]]]
  hmulB := by decide  
  f := ![![![-7357, -11676, 9611, -2923, 25128]], ![![-3515, -5633, 4628, -1408, 12098]], ![![-1481, -2290, 1895, -576, 4958]], ![![-1375, -2214, 1818, -553, 4746]], ![![-4434, -7044, 5797, -1763, 15155]]]
  g := ![![![106783, -50332, -55069, 8219, -121432], ![221503, -104405, -114231, 17049, -251890], ![459467, -216570, -236952, 35365, -522498], ![953075, -449234, -491513, 73356, -1083818], ![69316, -32672, -35747, 5335, -78825]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N3 : Nat.card (O ⧸ I229N3) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N3)

lemma isPrimeI229N3 : Ideal.IsPrime I229N3 := prime_ideal_of_norm_prime hp229.out _ NI229N3
def MulI229N0 : IdealMulLeCertificate' Table 
  ![![-547, -245, 301, -86, 812]] ![![-7837, -5892, -1723, 1103, 27156]]
  ![![5583, 2535, -1024, 1661, -32752]] where
 M := ![![![5583, 2535, -1024, 1661, -32752]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI229N1 : IdealMulLeCertificate' Table 
  ![![5583, 2535, -1024, 1661, -32752]] ![![-15215, -48185, -52701, 7864, -116202]]
  ![![-7357, -11676, 9611, -2923, 25128]] where
 M := ![![![-7357, -11676, 9611, -2923, 25128]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI229N2 : IdealMulLeCertificate' Table 
  ![![-7357, -11676, 9611, -2923, 25128]] ![![-15849, -50332, -55069, 8219, -121432]]
  ![![229, 0, 0, 0, 0]] where
 M := ![![![229, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC229 : ContainsPrimesAboveP 229 ![I229N0, I229N1, I229N2, I229N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI229N0
    exact isPrimeI229N1
    exact isPrimeI229N2
    exact isPrimeI229N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 229 (by decide) (𝕀 ⊙ MulI229N0 ⊙ MulI229N1 ⊙ MulI229N2)
instance hp233 : Fact (Nat.Prime 233) := {out := by norm_num}

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-45, 5, 34, -41, 446]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![-45, 5, 34, -41, 446]] 
 ![![233, 0, 0, 0, 0], ![0, 233, 0, 0, 0], ![0, 0, 233, 0, 0], ![107, 63, 155, 1, 0], ![179, 57, 65, 0, 1]] where
  M :=![![![-45, 5, 34, -41, 446], ![164, 237, 164, -166, 298], ![664, -202, -627, 862, -7840], ![-3448, -3728, -2008, 2041, 2956], ![-592, -245, 92, -181, 3609]]]
  hmulB := by decide  
  f := ![![![-625, 533, -194, 73, -448]], ![![-292, -781, 596, -184, 1546]], ![![736, 518, -523, 154, -1396]], ![![121, 378, -275, 86, -714]], ![![-347, 363, -149, 54, -355]]]
  g := ![![![-324, -98, -97, -41, 446], ![-152, -27, 28, -166, 298], ![5630, 1684, 1611, 862, -7840], ![-3223, -1291, -2191, 2041, 2956], ![-2692, -835, -886, -181, 3609]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 3 2 7 [81, 78, 64, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [54, 145, 168], [115, 87, 65], [0, 1]]
 g := ![![[77, 194, 110], [115, 25], [38, 4], [125, 192, 210], [48, 98], [58, 179, 135], [1]], ![[190, 12, 93, 111], [0, 205], [228, 105], [168, 136, 212, 190], [54, 132], [47, 53, 176, 78], [24, 128, 82, 82]], ![[106, 125, 35, 54], [125, 52], [97, 102], [110, 136, 169, 147], [100, 19], [3, 199, 15, 230], [93, 231, 58, 151]]]
 h' := ![![[54, 145, 168], [14, 92, 209], [3, 178, 228], [127, 43, 231], [119, 168, 207], [195, 120, 104], [152, 155, 169], [0, 1]], ![[115, 87, 65], [167, 121, 87], [20, 57, 111], [9, 221, 60], [72, 1, 99], [46, 200, 83], [109, 117, 201], [54, 145, 168]], ![[0, 1], [69, 20, 170], [116, 231, 127], [98, 202, 175], [212, 64, 160], [33, 146, 46], [7, 194, 96], [115, 87, 65]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25, 31], []]
 b := ![[], [161, 200, 65], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 3
  hpos := by decide
  P := [81, 78, 64, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![36569561, 5422792, -16403244, 24329712, -299419316]
  a := ![-12, 12, 22, -28, 174]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![219010077, 66693356, 67273592, 24329712, -299419316]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N0 B_one_repr
lemma NI233N0 : Nat.card (O ⧸ I233N0) = 12649337 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N0

def I233N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-625, 533, -194, 73, -448]] i)))

def SI233N1: IdealEqSpanCertificate' Table ![![-625, 533, -194, 73, -448]] 
 ![![233, 0, 0, 0, 0], ![0, 233, 0, 0, 0], ![211, 78, 1, 0, 0], ![85, 185, 0, 1, 0], ![186, 120, 0, 0, 1]] where
  M :=![![![-625, 533, -194, 73, -448], ![-292, -781, 596, -184, 1546], ![736, 518, -523, 154, -1396], ![-616, -44, 200, -51, 556], ![-172, 19, 32, -7, 95]]]
  hmulB := by decide  
  f := ![![![-45, 5, 34, -41, 446]], ![![164, 237, 164, -166, 298]], ![![17, 83, 83, -89, 470]], ![![99, 174, 134, -138, 412]], ![![46, 125, 112, -119, 525]]]
  g := ![![![504, 240, -194, 73, -448], ![-1708, -853, 596, -184, 1546], ![1535, 774, -523, 154, -1396], ![-609, -313, 200, -51, 556], ![-103, -54, 32, -7, 95]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P1 : CertificateIrreducibleZModOfList' 233 2 2 7 [106, 200, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [33, 232], [0, 1]]
 g := ![![[103, 52], [18], [91], [170, 64], [16], [16, 38], [33, 1]], ![[188, 181], [18], [91], [185, 169], [16], [105, 195], [66, 232]]]
 h' := ![![[33, 232], [134, 127], [90, 22], [154, 215], [199, 8], [168, 4], [230, 51], [0, 1]], ![[0, 1], [131, 106], [117, 211], [26, 18], [230, 225], [67, 229], [49, 182], [33, 232]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [192]]
 b := ![[], [47, 96]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N1 : CertifiedPrimeIdeal' SI233N1 233 where
  n := 2
  hpos := by decide
  P := [106, 200, 1]
  hirr := P233P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5543, 2842, -1784, 6924, -49874]
  a := ![1, 11, 2, 9, -8]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![38927, 20798, -1784, 6924, -49874]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N1 : Ideal.IsPrime I233N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N1 B_one_repr
lemma NI233N1 : Nat.card (O ⧸ I233N1) = 54289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N1
def MulI233N0 : IdealMulLeCertificate' Table 
  ![![-45, 5, 34, -41, 446]] ![![-625, 533, -194, 73, -448]]
  ![![233, 0, 0, 0, 0]] where
 M := ![![![233, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, -226, 123, -41, 306]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![109, -226, 123, -41, 306]] 
 ![![239, 0, 0, 0, 0], ![0, 239, 0, 0, 0], ![18, 26, 1, 0, 0], ![10, 59, 0, 1, 0], ![203, 224, 0, 0, 1]] where
  M :=![![![109, -226, 123, -41, 306], ![164, 251, -207, 63, -542], ![-252, -126, 150, -43, 402], ![172, -22, -25, 6, -82], ![44, -18, 1, -1, -1]]]
  hmulB := by decide  
  f := ![![![3, 22, 25, -13, 110]], ![![52, 61, 41, -7, -94]], ![![6, 8, 6, -1, -6]], ![![10, 15, 12, -3, 0]], ![![51, 76, 60, -18, 9]]]
  g := ![![![-267, -291, 123, -41, 306], ![474, 516, -207, 63, -542], ![-352, -383, 150, -43, 402], ![72, 78, -25, 6, -82], ![1, 1, 1, -1, -1]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P0 : CertificateIrreducibleZModOfList' 239 2 2 7 [16, 206, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [33, 238], [0, 1]]
 g := ![![[222, 15], [64, 198], [110, 67], [39, 128], [220], [38, 66], [33, 1]], ![[0, 224], [145, 41], [170, 172], [200, 111], [220], [65, 173], [66, 238]]]
 h' := ![![[33, 238], [171, 60], [152, 213], [93, 211], [235, 75], [109, 69], [189, 117], [0, 1]], ![[0, 1], [0, 179], [11, 26], [125, 28], [81, 164], [235, 170], [226, 122], [33, 238]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [90]]
 b := ![[], [94, 45]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 2
  hpos := by decide
  P := [16, 206, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-269, 3184, 4699, -5184, 31104]
  a := ![-5, 1, 9, -9, 72]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-26557, -28370, 4699, -5184, 31104]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N0 B_one_repr
lemma NI239N0 : Nat.card (O ⧸ I239N0) = 57121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N0

def I239N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![595, 1468, 1536, -1650, 6898]] i)))

def SI239N1: IdealEqSpanCertificate' Table ![![595, 1468, 1536, -1650, 6898]] 
 ![![239, 0, 0, 0, 0], ![0, 239, 0, 0, 0], ![88, 108, 1, 0, 0], ![56, 135, 0, 1, 0], ![54, 72, 0, 0, 1]] where
  M :=![![![595, 1468, 1536, -1650, 6898], ![6600, 893, -3184, 4538, -54312], ![-18152, -29560, -21653, 23900, -62668], ![-95600, 14780, 75072, -102385, 1010192], ![-1052, 13844, 16020, -19434, 118405]]]
  hmulB := by decide  
  f := ![![![-41476575475, -131717813260, -144114319432, 21508958162, -317784604450]], ![![-86035832648, -273225347277, -298939710576, 44616536046, -659188053304]], ![![-54896546912, -174335827676, -190743290797, 28468298484, -420605540492]], ![![-59864946192, -190114051433, -208006468208, 31044815253, -458672347640]], ![![-35402673338, -112428826684, -123009966844, 18359148770, -271247672063]]]
  g := ![![![-1735, -1834, 1536, -1650, 6898], ![12408, 15241, -3184, 4538, -54312], ![16456, 15040, -21653, 23900, -62668], ![-232296, -280355, 75072, -102385, 1010192], ![-28102, -31874, 16020, -19434, 118405]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P1 : CertificateIrreducibleZModOfList' 239 2 2 7 [182, 35, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [204, 238], [0, 1]]
 g := ![![[230, 109], [15, 166], [55, 232], [228, 50], [1], [34, 160], [204, 1]], ![[0, 130], [180, 73], [61, 7], [151, 189], [1], [170, 79], [169, 238]]]
 h' := ![![[204, 238], [138, 161], [28, 40], [90, 145], [16, 17], [26, 1], [156, 87], [0, 1]], ![[0, 1], [0, 78], [62, 199], [34, 94], [138, 222], [230, 238], [218, 152], [204, 238]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [113]]
 b := ![[], [212, 176]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N1 : CertifiedPrimeIdeal' SI239N1 239 where
  n := 2
  hpos := by decide
  P := [182, 35, 1]
  hirr := P239P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1076, 29892, 32766, -37844, 220992]
  a := ![-17, 20, 34, -28, 248]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-53124, -59880, 32766, -37844, 220992]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N1 : Ideal.IsPrime I239N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N1 B_one_repr
lemma NI239N1 : Nat.card (O ⧸ I239N1) = 57121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N1

def I239N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2901, 2646, -2485, 737, -6586]] i)))

def SI239N2: IdealEqSpanCertificate' Table ![![2901, 2646, -2485, 737, -6586]] 
 ![![239, 0, 0, 0, 0], ![105, 1, 0, 0, 0], ![208, 0, 1, 0, 0], ![148, 0, 0, 1, 0], ![160, 0, 0, 0, 1]] where
  M :=![![![2901, 2646, -2485, 737, -6586], ![-2948, -737, 1219, -321, 3230], ![1284, -1002, 246, -85, 762], ![340, 1706, -835, -6, -358], ![284, 530, -349, 75, -849]]]
  hmulB := by decide  
  f := ![![![-20195400405, -64134850786, -70170845871, 10472948101, -154732816190]], ![![-9047735711, -28733036639, -31437221116, 4691982562, -69321805888]], ![![-17939499628, -56970751198, -62332503350, 9303081137, -137448589422]], ![![-13260133920, -42110415902, -46073600665, 6876451646, -101596295362]], ![![-13574784972, -43109658198, -47166885771, 7039623659, -104007084077]]]
  g := ![![![4965, 2646, -2485, 737, -6586], ![-2713, -737, 1219, -321, 3230], ![-226, -1002, 246, -85, 762], ![222, 1706, -835, -6, -358], ![594, 530, -349, 75, -849]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N2 : Nat.card (O ⧸ I239N2) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N2)

lemma isPrimeI239N2 : Ideal.IsPrime I239N2 := prime_ideal_of_norm_prime hp239.out _ NI239N2
def MulI239N0 : IdealMulLeCertificate' Table 
  ![![109, -226, 123, -41, 306]] ![![595, 1468, 1536, -1650, 6898]]
  ![![-61753, -47402, 47857, -14757, 132288]] where
 M := ![![![-61753, -47402, 47857, -14757, 132288]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI239N1 : IdealMulLeCertificate' Table 
  ![![-61753, -47402, 47857, -14757, 132288]] ![![2901, 2646, -2485, 737, -6586]]
  ![![239, 0, 0, 0, 0]] where
 M := ![![![54596443, -131478680, 73599572, -24353622, 183034326]]]
 hmul := by decide  
 g := ![![![![228437, -550120, 307948, -101898, 765834]]]]
 hle2 := by decide  


def PBC239 : ContainsPrimesAboveP 239 ![I239N0, I239N1, I239N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI239N0
    exact isPrimeI239N1
    exact isPrimeI239N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 239 (by decide) (𝕀 ⊙ MulI239N0 ⊙ MulI239N1)
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


def P241P0 : CertificateIrreducibleZModOfList' 241 5 2 7 [149, 130, 90, 61, 132, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [77, 80, 24, 223, 229], [240, 153, 193, 100, 219], [94, 226, 9, 141, 192], [180, 22, 15, 18, 83], [0, 1]]
 g := ![![[103, 79, 74, 13, 225], [56, 190, 93, 81], [71, 11, 143, 121], [79, 174, 160, 49], [221, 195, 116, 216, 9], [11, 109, 1], []], ![[69, 62, 103, 154, 99, 28, 160, 107], [54, 132, 218, 237], [162, 188, 29, 217], [193, 203, 193, 141], [84, 138, 35, 210, 71, 95, 79, 196], [229, 0, 203, 113, 218, 87, 98, 226], [53, 47, 33, 131, 163, 194, 46, 200]], ![[1, 8, 190, 26, 122, 133, 116, 19], [136, 197, 106, 150], [18, 49, 131, 150], [64, 226, 28, 120], [80, 224, 144, 193, 205, 34, 52, 137], [234, 43, 174, 224, 197, 80, 190, 156], [35, 19, 41, 136, 142, 139, 142, 197]], ![[211, 17, 236, 3, 229, 78, 55, 108], [63, 183, 129, 123], [188, 96, 207, 72], [219, 15, 63, 64], [2, 123, 61, 119, 191, 51, 20, 54], [16, 21, 2, 177, 0, 61, 131, 81], [96, 121, 196, 9, 67, 168, 159, 200]], ![[197, 4, 87, 90, 159, 69, 44, 47], [56, 145, 158, 107], [216, 104, 89, 10], [180, 59, 83, 79], [15, 140, 18, 122, 0, 209, 13, 236], [22, 79, 13, 178, 13, 217, 204, 121], [135, 53, 171, 155, 239, 222, 157, 135]]]
 h' := ![![[77, 80, 24, 223, 229], [30, 68, 226, 163, 15], [105, 218, 236, 77, 9], [70, 136, 100, 111, 230], [88, 190, 119, 43, 234], [48, 163, 115, 234, 3], [0, 0, 0, 1], [0, 1]], ![[240, 153, 193, 100, 219], [7, 40, 29, 109, 104], [10, 35, 183, 101, 113], [224, 108, 112, 191, 82], [28, 39, 82, 74, 158], [83, 80, 17, 42, 233], [135, 181, 51, 216, 69], [77, 80, 24, 223, 229]], ![[94, 226, 9, 141, 192], [203, 221, 233, 36, 88], [114, 184, 184, 128, 106], [164, 88, 16, 64, 135], [32, 168, 53, 1, 222], [154, 183, 99, 126, 105], [86, 67, 81, 59, 137], [240, 153, 193, 100, 219]], ![[180, 22, 15, 18, 83], [170, 225, 230, 234, 180], [188, 109, 69, 199, 72], [185, 77, 132, 45, 132], [194, 93, 109, 65, 8], [6, 223, 200, 147, 52], [13, 128, 218, 28, 21], [94, 226, 9, 141, 192]], ![[0, 1], [181, 169, 5, 181, 95], [191, 177, 51, 218, 182], [232, 73, 122, 71, 144], [32, 233, 119, 58, 101], [111, 74, 51, 174, 89], [170, 106, 132, 178, 14], [180, 22, 15, 18, 83]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [130, 197, 142, 210], [], [], []]
 b := ![[], [99, 27, 71, 227, 138], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 5
  hpos := by decide
  P := [149, 130, 90, 61, 132, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11179438454871, 8855882034644, 2957703503686, -2175234296450, -35215806895906]
  a := ![-11, 13, 19, -17, 160]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![46387711431, 36746398484, 12272628646, -9025868450, -146123680066]
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

def I251N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![115, 20, -20, -6, -26]] i)))

def SI251N0: IdealEqSpanCertificate' Table ![![115, 20, -20, -6, -26]] 
 ![![251, 0, 0, 0, 0], ![0, 251, 0, 0, 0], ![229, 180, 1, 0, 0], ![195, 208, 0, 1, 0], ![93, 141, 0, 0, 1]] where
  M :=![![![115, 20, -20, -6, -26], ![24, 65, -48, 42, -504], ![-168, -312, -145, 204, -588], ![-816, 60, 528, -781, 8304], ![-4, 116, 124, -162, 1041]]]
  hmulB := by decide  
  f := ![![![-867855, -2756068, -3015452, 450054, -6649334]], ![![-1800216, -5716973, -6255024, 933558, -13792872]], ![![-2097657, -6661568, -7288517, 1087806, -16071814]], ![![-2196903, -6976744, -7633356, 1139273, -16832214]], ![![-1335077, -4239827, -4638856, 692346, -10229081]]]
  g := ![![![33, 34, -20, -6, -26], ![198, 283, -48, 42, -504], ![191, 264, -145, 204, -588], ![-2955, -4396, 528, -781, 8304], ![-373, -539, 124, -162, 1041]]]
  hle1 := by decide   
  hle2 := by decide  


def P251P0 : CertificateIrreducibleZModOfList' 251 2 2 7 [190, 169, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [82, 250], [0, 1]]
 g := ![![[240, 144], [119, 222], [105], [119, 153], [166, 207], [191, 64], [82, 1]], ![[0, 107], [0, 29], [105], [115, 98], [72, 44], [168, 187], [164, 250]]]
 h' := ![![[82, 250], [231, 239], [28, 67], [231, 132], [86, 116], [105, 61], [233, 8], [0, 1]], ![[0, 1], [0, 12], [0, 184], [11, 119], [60, 135], [87, 190], [136, 243], [82, 250]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [67]]
 b := ![[], [7, 159]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI251N0 : CertifiedPrimeIdeal' SI251N0 251 where
  n := 2
  hpos := by decide
  P := [190, 169, 1]
  hirr := P251P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1138, 0, 219, 789, 5702]
  a := ![-2, 6, 4, 0, 31]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2930, -4014, 219, 789, 5702]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI251N0 : Ideal.IsPrime I251N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI251N0 B_one_repr
lemma NI251N0 : Nat.card (O ⧸ I251N0) = 63001 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI251N0

def I251N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 52, 92, -16, 208]] i)))

def SI251N1: IdealEqSpanCertificate' Table ![![19, 52, 92, -16, 208]] 
 ![![251, 0, 0, 0, 0], ![74, 1, 0, 0, 0], ![46, 0, 1, 0, 0], ![110, 0, 0, 1, 0], ![94, 0, 0, 0, 1]] where
  M :=![![![19, 52, 92, -16, 208], ![64, 163, 148, -20, 320], ![80, 304, 343, -52, 760], ![208, 632, 700, -105, 1544], ![16, 44, 52, -8, 115]]]
  hmulB := by decide  
  f := ![![![57, -92, -148, 176, -1232]], ![![14, -29, -44, 52, -352]], ![![10, -8, -17, 20, -152]], ![![74, -16, -68, 87, -808]], ![![26, -36, -60, 72, -517]]]
  g := ![![![-103, 52, 92, -16, 208], ![-186, 163, 148, -20, 320], ![-414, 304, 343, -52, 760], ![-846, 632, 700, -105, 1544], ![-62, 44, 52, -8, 115]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N1 : Nat.card (O ⧸ I251N1) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N1)

lemma isPrimeI251N1 : Ideal.IsPrime I251N1 := prime_ideal_of_norm_prime hp251.out _ NI251N1

def I251N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![913, 292, -239, 405, -6324]] i)))

def SI251N2: IdealEqSpanCertificate' Table ![![913, 292, -239, 405, -6324]] 
 ![![251, 0, 0, 0, 0], ![118, 1, 0, 0, 0], ![132, 0, 1, 0, 0], ![237, 0, 0, 1, 0], ![176, 0, 0, 0, 1]] where
  M :=![![![913, 292, -239, 405, -6324], ![-1620, -3791, -3197, 3655, -14454], ![-14620, -1454, 7340, -10673, 125266], ![42692, 67954, 49101, -53888, 132562], ![10072, 6792, 1351, -375, -41019]]]
  hmulB := by decide  
  f := ![![![-5940309909, -18864735540, -20640173545, 3080531005, -45513377236]], ![![-2841747782, -9024583095, -9873923801, 1473676001, -21772860474]], ![![-3225820632, -10244289282, -11208421564, 1672848829, -24715544070]], ![![-5820212359, -18483339866, -20222883152, 3018250715, -44593215638]], ![![-4180679712, -13276650268, -14526170539, 2168020469, -32031469023]]]
  g := ![![![4044, 292, -239, 405, -6324], ![10141, -3791, -3197, 3655, -14454], ![-80993, -1454, 7340, -10673, 125266], ![-99668, 67954, 49101, -53888, 132562], ![25253, 6792, 1351, -375, -41019]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N2 : Nat.card (O ⧸ I251N2) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N2)

lemma isPrimeI251N2 : Ideal.IsPrime I251N2 := prime_ideal_of_norm_prime hp251.out _ NI251N2

def I251N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10721, 1276, 1867, -403, 5604]] i)))

def SI251N3: IdealEqSpanCertificate' Table ![![-10721, 1276, 1867, -403, 5604]] 
 ![![251, 0, 0, 0, 0], ![130, 1, 0, 0, 0], ![168, 0, 1, 0, 0], ![248, 0, 0, 1, 0], ![55, 0, 0, 0, 1]] where
  M :=![![![-10721, 1276, 1867, -403, 5604], ![1612, -6729, 4059, -1319, 10250], ![5276, 6586, -5712, 1723, -15002], ![-6892, -2834, 3645, -1048, 9922], ![-2128, -556, 911, -253, 2495]]]
  hmulB := by decide  
  f := ![![![449962885, 1428954212, 1563438981, -233342139, 3447518884]], ![![236767106, 751905023, 822669903, -122782889, 1814058662]], ![![308883956, 980927638, 1073246780, -160181307, 2366602462]], ![![460585300, 1462687982, 1600347575, -238850720, 3528905542]], ![![99761137, 316813012, 346629590, -51734216, 764348383]]]
  g := ![![![-2783, 1276, 1867, -403, 5604], ![-168, -6729, 4059, -1319, 10250], ![2018, 6586, -5712, 1723, -15002], ![-2138, -2834, 3645, -1048, 9922], ![-627, -556, 911, -253, 2495]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N3 : Nat.card (O ⧸ I251N3) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N3)

lemma isPrimeI251N3 : Ideal.IsPrime I251N3 := prime_ideal_of_norm_prime hp251.out _ NI251N3
def MulI251N0 : IdealMulLeCertificate' Table 
  ![![115, 20, -20, -6, -26]] ![![19, 52, 92, -16, 208]]
  ![![201, -1776, 1128, -362, 2866]] where
 M := ![![![201, -1776, 1128, -362, 2866]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI251N1 : IdealMulLeCertificate' Table 
  ![![201, -1776, 1128, -362, 2866]] ![![913, 292, -239, 405, -6324]]
  ![![-18879, 17920, 6757, -16313, 151330]] where
 M := ![![![-18879, 17920, 6757, -16313, 151330]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI251N2 : IdealMulLeCertificate' Table 
  ![![-18879, 17920, 6757, -16313, 151330]] ![![-10721, 1276, 1867, -403, 5604]]
  ![![251, 0, 0, 0, 0]] where
 M := ![![![57337687, -138080120, 77294948, -25576398, 192224334]]]
 hmul := by decide  
 g := ![![![![228437, -550120, 307948, -101898, 765834]]]]
 hle2 := by decide  


def PBC251 : ContainsPrimesAboveP 251 ![I251N0, I251N1, I251N2, I251N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI251N0
    exact isPrimeI251N1
    exact isPrimeI251N2
    exact isPrimeI251N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 251 (by decide) (𝕀 ⊙ MulI251N0 ⊙ MulI251N1 ⊙ MulI251N2)


lemma PB532I5_primes (p : ℕ) :
  p ∈ Set.range ![199, 211, 223, 227, 229, 233, 239, 241, 251] ↔ Nat.Prime p ∧ 197 < p ∧ p ≤ 251 := by
  rw [← List.mem_ofFn']
  convert primes_range 197 251 (by omega)

def PB532I5 : PrimesBelowBoundCertificateInterval O 197 251 532 where
  m := 9
  g := ![1, 2, 2, 3, 4, 2, 3, 1, 4]
  P := ![199, 211, 223, 227, 229, 233, 239, 241, 251]
  hP := PB532I5_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I199N0]
    · exact ![I211N0, I211N1]
    · exact ![I223N0, I223N1]
    · exact ![I227N0, I227N1, I227N2]
    · exact ![I229N0, I229N1, I229N2, I229N3]
    · exact ![I233N0, I233N1]
    · exact ![I239N0, I239N1, I239N2]
    · exact ![I241N0]
    · exact ![I251N0, I251N1, I251N2, I251N3]
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
    · exact ![1982119441, 211]
    · exact ![2472973441, 223]
    · exact ![11697083, 227, 227]
    · exact ![52441, 229, 229, 229]
    · exact ![12649337, 54289]
    · exact ![57121, 57121, 239]
    · exact ![812990017201]
    · exact ![63001, 251, 251, 251]
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
      exact NI229N3
    · dsimp ; intro j
      fin_cases j
      exact NI233N0
      exact NI233N1
    · dsimp ; intro j
      fin_cases j
      exact NI239N0
      exact NI239N1
      exact NI239N2
    · dsimp ; intro j
      fin_cases j
      exact NI241N0
    · dsimp ; intro j
      fin_cases j
      exact NI251N0
      exact NI251N1
      exact NI251N2
      exact NI251N3
  β := ![I211N1, I223N1, I227N1, I227N2, I229N1, I229N2, I229N3, I239N2, I251N1, I251N2, I251N3]
  Il := ![[], [I211N1], [I223N1], [I227N1, I227N2], [I229N1, I229N2, I229N3], [], [I239N2], [], [I251N1, I251N2, I251N3]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
