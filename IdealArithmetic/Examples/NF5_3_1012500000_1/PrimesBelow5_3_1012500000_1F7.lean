
import IdealArithmetic.Examples.NF5_3_1012500000_1.RI5_3_1012500000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp311 : Fact (Nat.Prime 311) := {out := by norm_num}

def I311N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-163, -574, 31, 717, 243]] i)))

def SI311N0: IdealEqSpanCertificate' Table ![![-163, -574, 31, 717, 243]] 
 ![![311, 0, 0, 0, 0], ![0, 311, 0, 0, 0], ![0, 0, 311, 0, 0], ![0, 0, 0, 311, 0], ![71, 292, 59, 241, 1]] where
  M :=![![![-163, -574, 31, 717, 243], ![1458, 3482, -2170, -6339, 717], ![4302, 12213, 443, -6909, -6339], ![-8490, -21237, 7413, 26369, 2018], ![-9060, -29718, -10757, 1245, 26084]]]
  hmulB := by decide  
  f := ![![![-2093, -1216, 365, -147, 153]], ![![918, 202, -586, -123, -147]], ![![-882, -1287, -845, -501, -123]], ![![318, 189, -49, 25, -22]], ![![463, -188, -668, -226, -144]]]
  g := ![![![-56, -230, -46, -186, 243], ![-159, -662, -143, -576, 717], ![1461, 5991, 1204, 4890, -6339], ![-488, -1963, -359, -1479, 2018], ![-5984, -24586, -4983, -20209, 26084]]]
  hle1 := by decide   
  hle2 := by decide  


def P311P0 : CertificateIrreducibleZModOfList' 311 4 2 8 [281, 128, 59, 268, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [43, 300, 47, 164], [267, 121, 164, 49], [44, 200, 100, 98], [0, 1]]
 g := ![![[74, 215, 137, 273], [25, 102, 215, 212], [90, 192, 168, 100], [185, 42, 224], [185, 228, 276, 12], [128, 125, 104, 294], [1], []], ![[256, 56, 148, 7, 251, 119], [219, 20, 168, 22, 134, 22], [45, 152, 118, 13, 156, 309], [307, 71, 106], [295, 9, 180, 143, 81, 123], [304, 21, 70, 109, 123, 230], [175, 203, 42], [99, 96, 150]], ![[11, 291, 76, 139, 3, 292], [202, 112, 113, 153, 171, 108], [239, 97, 254, 173, 295, 16], [289, 49, 121], [209, 282, 298, 140, 86, 40], [83, 219, 191, 71, 35, 235], [120, 264, 10], [14, 202, 224]], ![[90, 290, 252, 213, 199, 7], [47, 58, 151, 25, 306, 196], [5, 265, 293, 283, 17, 8], [146, 213, 67], [188, 158, 254, 190, 196, 63], [154, 26, 203, 215, 41, 139], [80, 77, 89], [65, 282, 274]]]
 h' := ![![[43, 300, 47, 164], [128, 20, 244, 133], [212, 170, 70, 183], [79, 201, 20, 301], [263, 111, 9, 262], [108, 84, 189, 261], [30, 183, 252, 43], [0, 0, 1], [0, 1]], ![[267, 121, 164, 49], [246, 225, 202, 221], [67, 227, 4, 39], [197, 259, 34, 188], [95, 287, 27, 130], [303, 251, 137, 143], [43, 43, 30, 167], [154, 147, 175, 238], [43, 300, 47, 164]], ![[44, 200, 100, 98], [28, 286, 305, 306], [190, 235, 245, 23], [250, 100, 145, 266], [141, 80, 105, 11], [194, 152, 271, 104], [187, 279, 211, 10], [179, 151, 151, 53], [267, 121, 164, 49]], ![[0, 1], [157, 91, 182, 273], [232, 301, 303, 66], [4, 62, 112, 178], [17, 144, 170, 219], [283, 135, 25, 114], [303, 117, 129, 91], [154, 13, 295, 20], [44, 200, 100, 98]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [89, 238, 139], []]
 b := ![[], [], [116, 102, 134, 232], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI311N0 : CertifiedPrimeIdeal' SI311N0 311 where
  n := 4
  hpos := by decide
  P := [281, 128, 59, 268, 1]
  hirr := P311P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![216641897, 550709864, -181010622, -668633424, -76958804]
  a := ![0, -1, -4, -1, -6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![18265971, 74027912, 14017874, 57486940, -76958804]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI311N0 : Ideal.IsPrime I311N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI311N0 B_one_repr
lemma NI311N0 : Nat.card (O ⧸ I311N0) = 9354951841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI311N0

def I311N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2093, 1216, -365, 147, -153]] i)))

def SI311N1: IdealEqSpanCertificate' Table ![![2093, 1216, -365, 147, -153]] 
 ![![311, 0, 0, 0, 0], ![70, 1, 0, 0, 0], ![76, 0, 1, 0, 0], ![112, 0, 0, 1, 0], ![36, 0, 0, 0, 1]] where
  M :=![![![2093, 1216, -365, 147, -153], ![-918, -202, 586, 123, 147], ![882, 1287, 845, 501, 123], ![-318, -189, 49, -25, 22], ![60, 732, 887, 399, 164]]]
  hmulB := by decide  
  f := ![![![163, 574, -31, -717, -243]], ![![32, 118, 0, -141, -57]], ![![26, 101, -9, -153, -39]], ![![86, 275, -35, -343, -94]], ![![48, 162, 31, -87, -112]]]
  g := ![![![-213, 1216, -365, 147, -153], ![-162, -202, 586, 123, 147], ![-688, 1287, 845, 501, 123], ![36, -189, 49, -25, 22], ![-544, 732, 887, 399, 164]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI311N1 : Nat.card (O ⧸ I311N1) = 311 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI311N1)

lemma isPrimeI311N1 : Ideal.IsPrime I311N1 := prime_ideal_of_norm_prime hp311.out _ NI311N1
def MulI311N0 : IdealMulLeCertificate' Table 
  ![![-163, -574, 31, 717, 243]] ![![2093, 1216, -365, 147, -153]]
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

def I313N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![313, 0, 0, 0, 0]] i)))

def SI313N0: IdealEqSpanCertificate' Table ![![313, 0, 0, 0, 0]] 
 ![![313, 0, 0, 0, 0], ![0, 313, 0, 0, 0], ![0, 0, 313, 0, 0], ![0, 0, 0, 313, 0], ![0, 0, 0, 0, 313]] where
  M :=![![![313, 0, 0, 0, 0], ![0, 313, 0, 0, 0], ![0, 0, 313, 0, 0], ![0, 0, 0, 313, 0], ![0, 0, 0, 0, 313]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P313P0 : CertificateIrreducibleZModOfList' 313 5 2 8 [95, 72, 127, 210, 58, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [250, 199, 236, 118, 230], [161, 290, 57, 254, 79], [85, 60, 247, 246, 61], [72, 76, 86, 8, 256], [0, 1]]
 g := ![![[228, 267, 21, 292, 304], [202, 92, 292, 208], [245, 94, 292, 97], [295, 34, 219, 166, 11], [197, 33, 300, 310, 50], [213, 19, 24, 255, 1], [], []], ![[198, 226, 94, 29, 199, 249, 310, 103], [121, 126, 23, 238], [181, 148, 151, 137], [68, 107, 307, 46, 271, 13, 8, 309], [224, 105, 205, 132, 172, 306, 259, 99], [90, 40, 143, 32, 147, 125, 301, 161], [263, 233, 66, 287], [286, 87, 270, 3]], ![[288, 14, 134, 219, 80, 224, 87, 169], [183, 286, 250, 196], [206, 120, 74, 226], [91, 301, 30, 152, 14, 175, 11, 304], [307, 82, 42, 215, 207, 260, 195, 96], [269, 269, 35, 288, 276, 143, 142, 99], [261, 302, 15, 3], [24, 262, 231, 294]], ![[166, 207, 248, 173, 22, 234, 280, 184], [30, 278, 104, 305], [221, 123, 298, 96], [299, 202, 64, 158, 88, 132, 18, 172], [226, 58, 293, 306, 37, 131, 176, 188], [141, 124, 87, 198, 298, 269, 10, 219], [54, 208, 84, 158], [311, 189, 116, 278]], ![[283, 134, 38, 262, 139, 134, 281, 13], [276, 2, 121, 274], [270, 180, 180, 27], [104, 33, 298, 80, 93, 186, 138, 87], [192, 31, 275, 65, 141, 274, 262, 76], [225, 178, 173, 297, 141, 154, 142, 58], [180, 87, 295, 29], [271, 1, 11, 119]]]
 h' := ![![[250, 199, 236, 118, 230], [254, 159, 190, 228, 75], [254, 239, 194, 192, 55], [145, 100, 118, 77, 262], [65, 102, 136, 82, 295], [110, 74, 288, 146, 26], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[161, 290, 57, 254, 79], [53, 241, 99, 131, 72], [103, 18, 312, 309, 267], [205, 173, 70, 82, 78], [205, 25, 290, 52, 29], [103, 271, 93, 110, 169], [11, 143, 194, 215, 167], [274, 218, 160, 120, 247], [250, 199, 236, 118, 230]], ![[85, 60, 247, 246, 61], [149, 155, 154, 220, 302], [257, 256, 162, 169, 14], [128, 35, 70, 179, 126], [193, 1, 151, 305, 232], [138, 128, 156, 219, 21], [257, 296, 224, 1, 142], [166, 93, 66, 46, 230], [161, 290, 57, 254, 79]], ![[72, 76, 86, 8, 256], [99, 11, 166, 158, 93], [142, 29, 113, 216, 260], [127, 301, 62, 62, 224], [303, 304, 211, 31, 306], [76, 48, 163, 237, 124], [210, 253, 65, 102, 235], [216, 214, 245, 282, 285], [85, 60, 247, 246, 61]], ![[0, 1], [222, 60, 17, 202, 84], [280, 84, 158, 53, 30], [175, 17, 306, 226, 249], [12, 194, 151, 156, 77], [51, 105, 239, 227, 286], [134, 247, 143, 308, 81], [97, 101, 154, 178, 177], [72, 76, 86, 8, 256]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [98, 98, 188, 10], [], [], []]
 b := ![[], [267, 304, 149, 253, 68], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI313N0 : CertifiedPrimeIdeal' SI313N0 313 where
  n := 5
  hpos := by decide
  P := [95, 72, 127, 210, 58, 1]
  hirr := P313P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11300673131, 27285437586, -24910196396, -65060231958, 5588881676]
  a := ![3, -64, 1, -1, 2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![36104387, 87173922, -79585292, -207860166, 17855852]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI313N0 : Ideal.IsPrime I313N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI313N0 B_one_repr
lemma NI313N0 : Nat.card (O ⧸ I313N0) = 3004150512793 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI313N0

def PBC313 : ContainsPrimesAboveP 313 ![I313N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI313N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![313, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 313 (by decide) 𝕀

instance hp317 : Fact (Nat.Prime 317) := {out := by norm_num}

def I317N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3465931, 5792753, -1839870, 841235, -697097]] i)))

def SI317N0: IdealEqSpanCertificate' Table ![![3465931, 5792753, -1839870, 841235, -697097]] 
 ![![317, 0, 0, 0, 0], ![0, 317, 0, 0, 0], ![0, 0, 317, 0, 0], ![42, 179, 109, 1, 0], ![237, 169, 237, 0, 1]] where
  M :=![![![3465931, 5792753, -1839870, 841235, -697097], ![-4182582, -6990524, 2220296, -1015179, 841235], ![5047410, 8435943, -2679397, 1225083, -1015179], ![-3538884, -5914684, 1878596, -858943, 711770], ![-1298622, -2170443, 689358, -315201, 261188]]]
  hmulB := by decide  
  f := ![![![491, 255, -112, 37, -47]], ![![-282, -214, 70, 63, 37]], ![![222, 273, -215, -435, 63]], ![![-18, 7, -49, -109, 36]], ![![381, 277, -205, -258, 31]]]
  g := ![![![420650, -85107, 226112, 841235, -697097], ![-507627, 102706, -272864, -1015179, 841235], ![612591, -123939, 329287, 1225083, -1015179], ![-429504, 86899, -230871, -858943, 711770], ![-157608, 31892, -84717, -315201, 261188]]]
  hle1 := by decide   
  hle2 := by decide  


def P317P0 : CertificateIrreducibleZModOfList' 317 3 2 8 [13, 279, 169, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [251, 80, 97], [214, 236, 220], [0, 1]]
 g := ![![[127, 261, 43], [272, 283], [142, 37, 156], [152, 247, 149], [45, 13, 104], [140, 141, 6], [148, 1], []], ![[186, 36, 92, 2], [198, 274], [106, 257, 40, 147], [57, 311, 60, 14], [28, 27, 254, 210], [74, 284, 71, 188], [250, 221], [255, 216]], ![[209, 27, 273, 285], [196, 39], [307, 91, 59, 174], [99, 228, 236, 33], [252, 10, 126, 305], [224, 267, 7, 315], [132, 60], [132, 216]]]
 h' := ![![[251, 80, 97], [234, 85, 186], [56, 247, 261], [243, 211, 182], [49, 23, 222], [82, 167, 65], [295, 222, 69], [0, 0, 1], [0, 1]], ![[214, 236, 220], [269, 121, 153], [270, 24, 282], [161, 187, 19], [125, 14, 99], [299, 311, 156], [95, 143, 95], [90, 126, 236], [251, 80, 97]], ![[0, 1], [30, 111, 295], [291, 46, 91], [307, 236, 116], [186, 280, 313], [153, 156, 96], [158, 269, 153], [17, 191, 80], [214, 236, 220]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38, 222], []]
 b := ![[], [214, 278, 50], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI317N0 : CertifiedPrimeIdeal' SI317N0 317 where
  n := 3
  hpos := by decide
  P := [13, 279, 169, 1]
  hirr := P317P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-63198, -159466, 83560, 235862, 17210]
  a := ![1, -3, -2, -1, -3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-44316, -142862, -93704, 235862, 17210]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI317N0 : Ideal.IsPrime I317N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI317N0 B_one_repr
lemma NI317N0 : Nat.card (O ⧸ I317N0) = 31855013 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI317N0

def I317N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![491, 255, -112, 37, -47]] i)))

def SI317N1: IdealEqSpanCertificate' Table ![![491, 255, -112, 37, -47]] 
 ![![317, 0, 0, 0, 0], ![0, 317, 0, 0, 0], ![181, 300, 1, 0, 0], ![211, 149, 0, 1, 0], ![156, 4, 0, 0, 1]] where
  M :=![![![491, 255, -112, 37, -47], ![-282, -214, 70, 63, 37], ![222, 273, -215, -435, 63], ![-48, 58, 76, 31, -104], ![-546, -1161, 684, 1893, -218]]]
  hmulB := by decide  
  f := ![![![3465931, 5792753, -1839870, 841235, -697097]], ![![-4182582, -6990524, 2220296, -1015179, 841235]], ![![-1963387, -3281492, 1042249, -476546, 394892]], ![![329867, 551319, -175110, 80063, -66346]], ![![1648758, 2755637, -875234, 400179, -331612]]]
  g := ![![![64, 90, -112, 37, -47], ![-101, -97, 70, 63, 37], ![382, 408, -215, -435, 63], ![-13, -85, 76, 31, -104], ![-1545, -1538, 684, 1893, -218]]]
  hle1 := by decide   
  hle2 := by decide  


def P317P1 : CertificateIrreducibleZModOfList' 317 2 2 8 [284, 170, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [147, 316], [0, 1]]
 g := ![![[235, 96], [141], [310, 131], [65, 53], [136, 53], [150, 194], [53], [1]], ![[82, 221], [141], [230, 186], [248, 264], [2, 264], [138, 123], [53], [1]]]
 h' := ![![[147, 316], [3, 276], [86, 211], [243, 173], [50, 170], [195, 147], [302, 58], [33, 147], [0, 1]], ![[0, 1], [316, 41], [37, 106], [314, 144], [314, 147], [248, 170], [269, 259], [86, 170], [147, 316]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [269]]
 b := ![[], [179, 293]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI317N1 : CertifiedPrimeIdeal' SI317N1 317 where
  n := 2
  hpos := by decide
  P := [284, 170, 1]
  hirr := P317P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3077, 9320, -1817, -9092, 2733]
  a := ![1, 19, 3, -1, 6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![5754, 5988, -1817, -9092, 2733]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI317N1 : Ideal.IsPrime I317N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI317N1 B_one_repr
lemma NI317N1 : Nat.card (O ⧸ I317N1) = 100489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI317N1
def MulI317N0 : IdealMulLeCertificate' Table 
  ![![3465931, 5792753, -1839870, 841235, -697097]] ![![491, 255, -112, 37, -47]]
  ![![317, 0, 0, 0, 0]] where
 M := ![![![317, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC317 : ContainsPrimesAboveP 317 ![I317N0, I317N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI317N0
    exact isPrimeI317N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 317 (by decide) (𝕀 ⊙ MulI317N0)
instance hp331 : Fact (Nat.Prime 331) := {out := by norm_num}

def I331N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19, -38, 54, 118, -40]] i)))

def SI331N0: IdealEqSpanCertificate' Table ![![-19, -38, 54, 118, -40]] 
 ![![331, 0, 0, 0, 0], ![0, 331, 0, 0, 0], ![49, 226, 1, 0, 0], ![171, 154, 0, 1, 0], ![298, 148, 0, 0, 1]] where
  M :=![![![-19, -38, 54, 118, -40], ![-240, -619, 166, 690, 118], ![708, 1530, -1283, -3198, 690], ![336, 1078, 328, -155, -878], ![-3552, -8070, 5430, 14574, -2099]]]
  hmulB := by decide  
  f := ![![![-269809, -451422, 143354, -65570, 54316]], ![![325896, 544931, -173054, 79146, -65570]], ![![181385, 303254, -96305, 44044, -36490]], ![![13071, 21714, -6898, 3151, -2614]], ![![-96886, -162250, 51522, -23570, 19521]]]
  g := ![![![-33, -74, 54, 118, -40], ![-488, -489, 166, 690, 118], ![1223, 2060, -1283, -3198, 690], ![823, 244, 328, -155, -878], ![-6454, -9574, 5430, 14574, -2099]]]
  hle1 := by decide   
  hle2 := by decide  


def P331P0 : CertificateIrreducibleZModOfList' 331 2 2 8 [253, 184, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [147, 330], [0, 1]]
 g := ![![[91, 157], [131, 186], [179], [40, 238], [109], [173], [9, 94], [1]], ![[0, 174], [0, 145], [179], [271, 93], [109], [173], [256, 237], [1]]]
 h' := ![![[147, 330], [288, 275], [81, 67], [141, 29], [108, 301], [199, 42], [40, 175], [78, 147], [0, 1]], ![[0, 1], [0, 56], [0, 264], [101, 302], [1, 30], [84, 289], [278, 156], [172, 184], [147, 330]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [150]]
 b := ![[], [280, 75]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI331N0 : CertifiedPrimeIdeal' SI331N0 331 where
  n := 2
  hpos := by decide
  P := [253, 184, 1]
  hirr := P331P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1972, 3982, -3848, -8382, 1255]
  a := ![-1, 0, -2, 2, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3776, 5978, -3848, -8382, 1255]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI331N0 : Ideal.IsPrime I331N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI331N0 B_one_repr
lemma NI331N0 : Nat.card (O ⧸ I331N0) = 109561 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI331N0

def I331N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-361, -568, 196, -78, 72]] i)))

def SI331N1: IdealEqSpanCertificate' Table ![![-361, -568, 196, -78, 72]] 
 ![![331, 0, 0, 0, 0], ![0, 331, 0, 0, 0], ![233, 223, 1, 0, 0], ![271, 190, 0, 1, 0], ![137, 69, 0, 0, 1]] where
  M :=![![![-361, -568, 196, -78, 72], ![432, 719, -190, 114, -78], ![-468, -738, 347, -78, 114], ![348, 576, -186, 83, -70], ![156, 288, 4, 66, -13]]]
  hmulB := by decide  
  f := ![![![-43, -56, 16, 42, 12]], ![![72, 137, -98, -246, 42]], ![![19, 55, -55, -138, 36]], ![![5, 30, -42, -103, 34]], ![![-5, -1, -14, -30, 17]]]
  g := ![![![-105, -104, 196, -78, 72], ![74, 81, -190, 114, -78], ![-229, -215, 347, -78, 114], ![93, 94, -186, 83, -70], ![-51, -37, 4, 66, -13]]]
  hle1 := by decide   
  hle2 := by decide  


def P331P1 : CertificateIrreducibleZModOfList' 331 2 2 8 [156, 101, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [230, 330], [0, 1]]
 g := ![![[181, 87], [219, 123], [6], [25, 67], [290], [302], [169, 271], [1]], ![[0, 244], [43, 208], [6], [209, 264], [290], [302], [271, 60], [1]]]
 h' := ![![[230, 330], [260, 114], [276, 192], [72, 240], [89, 27], [106, 271], [116, 77], [175, 230], [0, 1]], ![[0, 1], [0, 217], [82, 139], [326, 91], [10, 304], [208, 60], [283, 254], [115, 101], [230, 330]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [271]]
 b := ![[], [140, 301]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI331N1 : CertifiedPrimeIdeal' SI331N1 331 where
  n := 2
  hpos := by decide
  P := [156, 101, 1]
  hirr := P331P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-684, -2288, 90, 1446, 712]
  a := ![0, 0, -6, -10, -4]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1544, -1046, 90, 1446, 712]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI331N1 : Ideal.IsPrime I331N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI331N1 B_one_repr
lemma NI331N1 : Nat.card (O ⧸ I331N1) = 109561 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI331N1

def I331N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-431, -694, 222, -100, 84]] i)))

def SI331N2: IdealEqSpanCertificate' Table ![![-431, -694, 222, -100, 84]] 
 ![![331, 0, 0, 0, 0], ![213, 1, 0, 0, 0], ![309, 0, 1, 0, 0], ![130, 0, 0, 1, 0], ![151, 0, 0, 0, 1]] where
  M :=![![![-431, -694, 222, -100, 84], ![504, 829, -264, 120, -100], ![-600, -996, 317, -144, 120], ![420, 698, -222, 101, -84], ![156, 258, -82, 36, -31]]]
  hmulB := by decide  
  f := ![![![-5, 66, 126, 92, 12]], ![![-3, 43, 82, 60, 8]], ![![-3, 66, 119, 84, 12]], ![![-2, 26, 50, 37, 4]], ![![-5, 24, 64, 56, 5]]]
  g := ![![![239, -694, 222, -100, 84], ![-287, 829, -264, 120, -100], ![345, -996, 317, -144, 120], ![-242, 698, -222, 101, -84], ![-89, 258, -82, 36, -31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI331N2 : Nat.card (O ⧸ I331N2) = 331 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI331N2)

lemma isPrimeI331N2 : Ideal.IsPrime I331N2 := prime_ideal_of_norm_prime hp331.out _ NI331N2
def MulI331N0 : IdealMulLeCertificate' Table 
  ![![-19, -38, 54, 118, -40]] ![![-361, -568, 196, -78, 72]]
  ![![-5, 66, 126, 92, 12]] where
 M := ![![![-5, 66, 126, 92, 12]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI331N1 : IdealMulLeCertificate' Table 
  ![![-5, 66, 126, 92, 12]] ![![-431, -694, 222, -100, 84]]
  ![![331, 0, 0, 0, 0]] where
 M := ![![![331, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC331 : ContainsPrimesAboveP 331 ![I331N0, I331N1, I331N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI331N0
    exact isPrimeI331N1
    exact isPrimeI331N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 331 (by decide) (𝕀 ⊙ MulI331N0 ⊙ MulI331N1)
instance hp337 : Fact (Nat.Prime 337) := {out := by norm_num}

def I337N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-140363, -233949, 74344, -33955, 28165]] i)))

def SI337N0: IdealEqSpanCertificate' Table ![![-140363, -233949, 74344, -33955, 28165]] 
 ![![337, 0, 0, 0, 0], ![0, 337, 0, 0, 0], ![0, 0, 337, 0, 0], ![173, 149, 183, 1, 0], ![296, 126, 153, 0, 1]] where
  M :=![![![-140363, -233949, 74344, -33955, 28165], ![168990, 282112, -89622, 40959, -33955], ![-203730, -340335, 108107, -49419, 40959], ![142824, 238610, -75792, 34649, -28716], ![52446, 87579, -27820, 12717, -10540]]]
  hmulB := by decide  
  f := ![![![1, 5, 14, 11, 11]], ![![66, 166, -8, -147, 11]], ![![66, 231, 245, 195, -147]], ![![65, 200, 137, 48, -69]], ![![56, 172, 119, 40, -51]]]
  g := ![![![-7724, 3788, 5872, -33955, 28165], ![9299, -4577, -7092, 40959, -33955], ![-11211, 5526, 8561, -49419, 40959], ![7859, -3875, -6003, 34649, -28716], ![2885, -1422, -2203, 12717, -10540]]]
  hle1 := by decide   
  hle2 := by decide  


def P337P0 : CertificateIrreducibleZModOfList' 337 3 2 8 [139, 185, 126, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [316, 255, 13], [232, 81, 324], [0, 1]]
 g := ![![[5, 18, 323], [77, 246], [62, 32], [66, 123], [266, 113, 328], [42, 287], [189, 211, 1], []], ![[25, 51, 118, 155], [203, 283], [57, 252], [140, 78], [325, 24, 175, 94], [59, 12], [209, 159, 74, 32], [164, 169]], ![[72, 303, 89, 54], [43, 164], [201, 52], [167, 39], [291, 81, 287, 110], [118, 150], [162, 157, 61, 208], [190, 169]]]
 h' := ![![[316, 255, 13], [271, 74, 266], [223, 173, 120], [42, 3, 233], [96, 100, 125], [116, 22, 107], [15, 73, 31], [0, 0, 1], [0, 1]], ![[232, 81, 324], [0, 220, 266], [217, 319, 174], [273, 326, 40], [47, 43, 304], [32, 135, 191], [34, 78, 90], [224, 163, 81], [316, 255, 13]], ![[0, 1], [33, 43, 142], [142, 182, 43], [28, 8, 64], [177, 194, 245], [215, 180, 39], [21, 186, 216], [117, 174, 255], [232, 81, 324]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50, 60], []]
 b := ![[], [26, 109, 125], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI337N0 : CertifiedPrimeIdeal' SI337N0 337 where
  n := 3
  hpos := by decide
  P := [139, 185, 126, 1]
  hirr := P337P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-815903, -2020929, 1030218, 3088365, -145059]
  a := ![13, -1, -2, 1, -6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1460432, -1317240, -1608150, 3088365, -145059]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI337N0 : Ideal.IsPrime I337N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI337N0 B_one_repr
lemma NI337N0 : Nat.card (O ⧸ I337N0) = 38272753 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI337N0

def I337N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, -13, 3, 14, 2]] i)))

def SI337N1: IdealEqSpanCertificate' Table ![![-5, -13, 3, 14, 2]] 
 ![![337, 0, 0, 0, 0], ![68, 1, 0, 0, 0], ![94, 0, 1, 0, 0], ![11, 0, 0, 1, 0], ![53, 0, 0, 0, 1]] where
  M :=![![![-5, -13, 3, 14, 2], ![12, 25, -26, -60, 14], ![84, 222, -49, -228, -60], ![-102, -247, 115, 359, -8], ![-270, -741, 67, 606, 275]]]
  hmulB := by decide  
  f := ![![![1879, -14217, 3489, -2590, 1396]], ![![404, -2801, 684, -512, 274]], ![![478, -4056, 1001, -736, 400]], ![![95, -400, 94, -75, 38]], ![![305, -2214, 542, -404, 217]]]
  g := ![![![1, -13, 3, 14, 2], ![2, 25, -26, -60, 14], ![-14, 222, -49, -228, -60], ![7, -247, 115, 359, -8], ![67, -741, 67, 606, 275]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI337N1 : Nat.card (O ⧸ I337N1) = 337 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI337N1)

lemma isPrimeI337N1 : Ideal.IsPrime I337N1 := prime_ideal_of_norm_prime hp337.out _ NI337N1

def I337N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-41, -24, 7, -3, 3]] i)))

def SI337N2: IdealEqSpanCertificate' Table ![![-41, -24, 7, -3, 3]] 
 ![![337, 0, 0, 0, 0], ![185, 1, 0, 0, 0], ![149, 0, 1, 0, 0], ![274, 0, 0, 1, 0], ![157, 0, 0, 0, 1]] where
  M :=![![![-41, -24, 7, -3, 3], ![18, 4, -12, -3, -3], ![-18, -27, -17, -9, -3], ![6, 3, -1, 1, 0], ![0, -12, -21, -15, -2]]]
  hmulB := by decide  
  f := ![![![-1817, -3018, 959, -429, 363]], ![![-991, -1646, 523, -234, 198]], ![![-811, -1347, 428, -192, 162]], ![![-1472, -2445, 777, -347, 294]], ![![-845, -1404, 446, -198, 169]]]
  g := ![![![11, -24, 7, -3, 3], ![7, 4, -12, -3, -3], ![31, -27, -17, -9, -3], ![-2, 3, -1, 1, 0], ![29, -12, -21, -15, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI337N2 : Nat.card (O ⧸ I337N2) = 337 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI337N2)

lemma isPrimeI337N2 : Ideal.IsPrime I337N2 := prime_ideal_of_norm_prime hp337.out _ NI337N2
def MulI337N0 : IdealMulLeCertificate' Table 
  ![![-140363, -233949, 74344, -33955, 28165]] ![![-5, -13, 3, 14, 2]]
  ![![-1817, -3018, 959, -429, 363]] where
 M := ![![![-1817, -3018, 959, -429, 363]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI337N1 : IdealMulLeCertificate' Table 
  ![![-1817, -3018, 959, -429, 363]] ![![-41, -24, 7, -3, 3]]
  ![![337, 0, 0, 0, 0]] where
 M := ![![![337, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC337 : ContainsPrimesAboveP 337 ![I337N0, I337N1, I337N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI337N0
    exact isPrimeI337N1
    exact isPrimeI337N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 337 (by decide) (𝕀 ⊙ MulI337N0 ⊙ MulI337N1)
instance hp347 : Fact (Nat.Prime 347) := {out := by norm_num}

def I347N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![347, 0, 0, 0, 0]] i)))

def SI347N0: IdealEqSpanCertificate' Table ![![347, 0, 0, 0, 0]] 
 ![![347, 0, 0, 0, 0], ![0, 347, 0, 0, 0], ![0, 0, 347, 0, 0], ![0, 0, 0, 347, 0], ![0, 0, 0, 0, 347]] where
  M :=![![![347, 0, 0, 0, 0], ![0, 347, 0, 0, 0], ![0, 0, 347, 0, 0], ![0, 0, 0, 347, 0], ![0, 0, 0, 0, 347]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P347P0 : CertificateIrreducibleZModOfList' 347 5 2 8 [321, 27, 62, 346, 112, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [74, 158, 188, 214, 317], [306, 207, 182, 152, 223], [133, 230, 172, 115, 297], [69, 98, 152, 213, 204], [0, 1]]
 g := ![![[163, 293, 78, 261, 159], [320, 131, 14, 45, 225], [281, 85, 208, 113], [295, 48, 86, 194, 75], [206, 111, 160, 106, 297], [116, 93, 198, 52], [1], []], ![[186, 116, 119, 304, 182, 145, 163, 91], [59, 274, 82, 48, 251, 269, 189, 190], [85, 295, 21, 75], [214, 115, 252, 212, 143, 102, 277, 58], [148, 323, 72, 128, 120, 261, 323, 2], [104, 264, 109, 74], [150, 76, 70, 266, 3, 149, 12, 195], [187, 89, 176, 206]], ![[281, 65, 199, 189, 76, 192, 261, 334], [260, 194, 195, 257, 234, 73, 286, 215], [292, 254, 217, 3], [31, 104, 287, 164, 64, 173, 246, 20], [298, 191, 262, 221, 220, 227, 118, 322], [205, 100, 330, 67], [135, 148, 5, 94, 140, 184, 257, 106], [147, 4, 176, 108]], ![[146, 194, 151, 328, 10, 34, 244, 297], [327, 203, 246, 201, 74, 232, 74, 11], [268, 132, 215, 329], [16, 183, 54, 219, 12, 253, 5, 287], [122, 167, 115, 4, 153, 238, 206, 36], [132, 254, 43, 202], [93, 330, 195, 88, 335, 190, 261, 213], [22, 71, 327, 71]], ![[84, 151, 341, 316, 280, 38, 86, 204], [163, 93, 225, 74, 31, 62, 97, 153], [16, 207, 315, 73], [129, 63, 158, 43, 96, 317, 189, 103], [260, 5, 287, 178, 225, 109, 321, 155], [275, 306, 269, 99], [144, 244, 99, 47, 331, 71, 307, 179], [229, 33, 66, 323]]]
 h' := ![![[74, 158, 188, 214, 317], [339, 95, 65, 121, 165], [274, 284, 197, 26, 332], [36, 122, 255, 115, 68], [151, 110, 167, 83, 219], [222, 311, 237, 2, 188], [26, 320, 285, 1, 235], [0, 0, 1], [0, 1]], ![[306, 207, 182, 152, 223], [66, 320, 128, 63, 203], [271, 241, 115, 172, 332], [181, 51, 125, 121, 128], [155, 236, 6, 149, 194], [224, 123, 66, 153, 78], [264, 239, 256, 51, 215], [275, 176, 339, 297, 127], [74, 158, 188, 214, 317]], ![[133, 230, 172, 115, 297], [33, 129, 84, 269, 324], [135, 103, 132, 138, 279], [164, 329, 16, 324, 252], [207, 64, 216, 84, 121], [220, 38, 82, 202, 95], [147, 304, 186, 68, 226], [298, 328, 30, 114, 286], [306, 207, 182, 152, 223]], ![[69, 98, 152, 213, 204], [63, 321, 120, 79, 1], [121, 99, 80, 28, 319], [176, 156, 10, 68, 321], [120, 233, 345, 230, 293], [61, 3, 89, 311, 203], [170, 186, 214, 164, 195], [217, 319, 120, 146, 184], [133, 230, 172, 115, 297]], ![[0, 1], [311, 176, 297, 162, 1], [52, 314, 170, 330, 126], [32, 36, 288, 66, 272], [329, 51, 307, 148, 214], [330, 219, 220, 26, 130], [193, 339, 100, 63, 170], [305, 218, 204, 137, 97], [69, 98, 152, 213, 204]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [101, 340, 47, 239], [], [], []]
 b := ![[], [209, 155, 125, 269, 274], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI347N0 : CertifiedPrimeIdeal' SI347N0 347 where
  n := 5
  hpos := by decide
  P := [321, 27, 62, 346, 112, 1]
  hirr := P347P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![899461129, 2275768964, -751526354, -2784207938, -263079438]
  a := ![-1, -3, 1, -1, 2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2592107, 6558412, -2165782, -8023654, -758154]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI347N0 : Ideal.IsPrime I347N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI347N0 B_one_repr
lemma NI347N0 : Nat.card (O ⧸ I347N0) = 5030919566507 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI347N0

def PBC347 : ContainsPrimesAboveP 347 ![I347N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI347N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![347, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 347 (by decide) 𝕀

instance hp349 : Fact (Nat.Prime 349) := {out := by norm_num}

def I349N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-65281, -34306, 16083, -2525, 5655]] i)))

def SI349N0: IdealEqSpanCertificate' Table ![![-65281, -34306, 16083, -2525, 5655]] 
 ![![349, 0, 0, 0, 0], ![0, 349, 0, 0, 0], ![307, 157, 1, 0, 0], ![73, 227, 0, 1, 0], ![288, 172, 0, 0, 1]] where
  M :=![![![-65281, -34306, 16083, -2525, 5655], ![33930, 19544, -6152, 2283, -2525], ![-15150, -3945, 8905, 1689, 2283], ![9858, 5155, -2461, 367, -860], ![9264, 8478, 2367, 2403, 70]]]
  hmulB := by decide  
  f := ![![![83, -40, -25, 601, 51]], ![![306, 848, -920, -2871, 601]], ![![221, 373, -440, -785, 307]], ![![203, 511, -590, -1699, 402]], ![![192, 308, -473, -867, 374]]]
  g := ![![![-18473, -8478, 16083, -2525, 5655], ![7115, 2583, -6152, 2283, -2525], ![-10114, -6241, 8905, 1689, 2283], ![2826, 1307, -2461, 367, -860], ![-2616, -2638, 2367, 2403, 70]]]
  hle1 := by decide   
  hle2 := by decide  


def P349P0 : CertificateIrreducibleZModOfList' 349 2 2 8 [215, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 348], [0, 1]]
 g := ![![[], [124], [0, 115], [0, 320], [], [219], [], [1]], ![[], [124], [0, 234], [0, 29], [], [219], [], [1]]]
 h' := ![![[0, 348], [213], [0, 54], [0, 302], [0, 202], [30], [0, 157], [134], [0, 1]], ![[0, 1], [213], [0, 295], [0, 47], [0, 147], [30], [0, 192], [134], [0, 348]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [237]]
 b := ![[], [0, 293]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI349N0 : CertifiedPrimeIdeal' SI349N0 349 where
  n := 2
  hpos := by decide
  P := [215, 0, 1]
  hirr := P349P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![686, 1162, -281, -1450, 89]
  a := ![3, 0, 3, -4, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![479, 1029, -281, -1450, 89]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI349N0 : Ideal.IsPrime I349N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI349N0 B_one_repr
lemma NI349N0 : Nat.card (O ⧸ I349N0) = 121801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI349N0

def I349N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -2, 1, 1, 1]] i)))

def SI349N1: IdealEqSpanCertificate' Table ![![-1, -2, 1, 1, 1]] 
 ![![349, 0, 0, 0, 0], ![96, 1, 0, 0, 0], ![207, 0, 1, 0, 0], ![249, 0, 0, 1, 0], ![84, 0, 0, 0, 1]] where
  M :=![![![-1, -2, 1, 1, 1], ![6, 14, -4, -15, 1], ![6, 21, 13, 3, -15], ![-18, -47, 13, 55, 8], ![0, -18, -43, -63, 64]]]
  hmulB := by decide  
  f := ![![![84227, 44784, -19867, 3607, -7123]], ![![23046, 12254, -5436, 987, -1949]], ![![50019, 26595, -11798, 2142, -4230]], ![![60057, 31933, -14166, 2572, -5079]], ![![20244, 10764, -4775, 867, -1712]]]
  g := ![![![-1, -2, 1, 1, 1], ![9, 14, -4, -15, 1], ![-12, 21, 13, 3, -15], ![-36, -47, 13, 55, 8], ![60, -18, -43, -63, 64]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI349N1 : Nat.card (O ⧸ I349N1) = 349 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI349N1)

lemma isPrimeI349N1 : Ideal.IsPrime I349N1 := prime_ideal_of_norm_prime hp349.out _ NI349N1

def I349N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8783, 4681, -2075, 378, -744]] i)))

def SI349N2: IdealEqSpanCertificate' Table ![![8783, 4681, -2075, 378, -744]] 
 ![![349, 0, 0, 0, 0], ![132, 1, 0, 0, 0], ![26, 0, 1, 0, 0], ![113, 0, 0, 1, 0], ![107, 0, 0, 0, 1]] where
  M :=![![![8783, 4681, -2075, 378, -744], ![-4464, -2377, 1054, -192, 378], ![2268, 1206, -535, 96, -192], ![-1326, -705, 313, -55, 112], ![-1038, -555, 245, -42, 89]]]
  hmulB := by decide  
  f := ![![![-2113, -5983, -5693, -2826, -978]], ![![-816, -2311, -2200, -1092, -378]], ![![-206, -584, -557, -276, -96]], ![![-683, -1934, -1840, -913, -316]], ![![-689, -1952, -1860, -924, -319]]]
  g := ![![![-1485, 4681, -2075, 378, -744], ![754, -2377, 1054, -192, 378], ![-382, 1206, -535, 96, -192], ![223, -705, 313, -55, 112], ![175, -555, 245, -42, 89]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI349N2 : Nat.card (O ⧸ I349N2) = 349 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI349N2)

lemma isPrimeI349N2 : Ideal.IsPrime I349N2 := prime_ideal_of_norm_prime hp349.out _ NI349N2

def I349N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-35, -57, 19, -12, 6]] i)))

def SI349N3: IdealEqSpanCertificate' Table ![![-35, -57, 19, -12, 6]] 
 ![![349, 0, 0, 0, 0], ![313, 1, 0, 0, 0], ![100, 0, 1, 0, 0], ![201, 0, 0, 1, 0], ![261, 0, 0, 0, 1]] where
  M :=![![![-35, -57, 19, -12, 6], ![36, 55, -12, 42, -12], ![-72, -144, 25, 18, 42], ![78, 165, -55, -119, -18], ![54, 159, 51, 12, -131]]]
  hmulB := by decide  
  f := ![![![2381101, 1269867, -562723, 102612, -201780]], ![![2132017, 1137028, -503857, 91878, -180672]], ![![684028, 364800, -161655, 29478, -57966]], ![![1370319, 730806, -323846, 59053, -116124]], ![![1779903, 949242, -420642, 76704, -150833]]]
  g := ![![![48, -57, 19, -12, 6], ![-61, 55, -12, 42, -12], ![80, -144, 25, 18, 42], ![-50, 165, -55, -119, -18], ![-66, 159, 51, 12, -131]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI349N3 : Nat.card (O ⧸ I349N3) = 349 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI349N3)

lemma isPrimeI349N3 : Ideal.IsPrime I349N3 := prime_ideal_of_norm_prime hp349.out _ NI349N3
def MulI349N0 : IdealMulLeCertificate' Table 
  ![![-65281, -34306, 16083, -2525, 5655]] ![![-1, -2, 1, 1, 1]]
  ![![1393, 4906, 5032, 2418, 888]] where
 M := ![![![1393, 4906, 5032, 2418, 888]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI349N1 : IdealMulLeCertificate' Table 
  ![![1393, 4906, 5032, 2418, 888]] ![![8783, 4681, -2075, 378, -744]]
  ![![-2381101, -1269867, 562723, -102612, 201780]] where
 M := ![![![-2381101, -1269867, 562723, -102612, 201780]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI349N2 : IdealMulLeCertificate' Table 
  ![![-2381101, -1269867, 562723, -102612, 201780]] ![![-35, -57, 19, -12, 6]]
  ![![349, 0, 0, 0, 0]] where
 M := ![![![-349, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC349 : ContainsPrimesAboveP 349 ![I349N0, I349N1, I349N2, I349N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI349N0
    exact isPrimeI349N1
    exact isPrimeI349N2
    exact isPrimeI349N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 349 (by decide) (𝕀 ⊙ MulI349N0 ⊙ MulI349N1 ⊙ MulI349N2)
instance hp353 : Fact (Nat.Prime 353) := {out := by norm_num}

def I353N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![353, 0, 0, 0, 0]] i)))

def SI353N0: IdealEqSpanCertificate' Table ![![353, 0, 0, 0, 0]] 
 ![![353, 0, 0, 0, 0], ![0, 353, 0, 0, 0], ![0, 0, 353, 0, 0], ![0, 0, 0, 353, 0], ![0, 0, 0, 0, 353]] where
  M :=![![![353, 0, 0, 0, 0], ![0, 353, 0, 0, 0], ![0, 0, 353, 0, 0], ![0, 0, 0, 353, 0], ![0, 0, 0, 0, 353]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P353P0 : CertificateIrreducibleZModOfList' 353 5 2 8 [71, 111, 330, 321, 161, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [62, 309, 15, 331, 275], [42, 216, 68, 274, 137], [307, 58, 105, 109, 254], [134, 122, 165, 345, 40], [0, 1]]
 g := ![![[198, 182, 210, 246, 44], [250, 196, 14, 84], [33, 340, 115, 176], [79, 193, 123, 306], [67, 308, 88, 323], [218, 284, 250, 171, 152], [1], []], ![[91, 223, 73, 245, 95, 259, 334, 111], [270, 272, 72, 261], [275, 227, 138, 311], [223, 63, 227, 231], [97, 241, 24, 17], [79, 242, 174, 201, 279, 312, 228, 92], [282, 285, 302, 331, 280, 185, 14, 197], [216, 248, 306, 83]], ![[40, 124, 103, 335, 128, 180, 24, 106], [12, 23, 284, 306], [124, 327, 148, 187], [7, 126, 258, 338], [200, 7, 285, 116], [178, 250, 46, 187, 247, 82, 175, 348], [108, 68, 104, 199, 342, 9, 136, 279], [337, 97, 111, 60]], ![[30, 142, 151, 21, 241, 312, 37, 11], [40, 79, 167, 303], [157, 275, 281, 196], [4, 298, 238, 262], [0, 281, 15, 330], [22, 293, 84, 136, 278, 265, 46, 140], [3, 11, 83, 249, 23, 58, 108, 34], [165, 299, 253, 270]], ![[337, 35, 153, 320, 203, 25, 264, 268], [192, 146, 343, 315], [41, 144, 344, 41], [11, 13, 270, 92], [195, 183, 184, 58], [188, 108, 263, 57, 249, 74, 20, 211], [14, 127, 150, 168, 301, 120, 288, 326], [108, 165, 156, 188]]]
 h' := ![![[62, 309, 15, 331, 275], [209, 302, 197, 288, 188], [130, 194, 197, 212, 310], [167, 180, 192, 89, 23], [277, 269, 293, 262, 134], [54, 215, 95, 322, 327], [282, 242, 23, 32, 192], [0, 0, 1], [0, 1]], ![[42, 216, 68, 274, 137], [99, 28, 255, 56, 300], [81, 178, 88, 308, 203], [292, 247, 111, 128, 283], [79, 86, 166, 0, 256], [214, 194, 236, 118, 82], [200, 333, 96, 326, 272], [157, 262, 105, 126, 186], [62, 309, 15, 331, 275]], ![[307, 58, 105, 109, 254], [55, 247, 234, 197, 116], [298, 112, 155, 313, 219], [173, 349, 156, 150, 295], [252, 48, 35, 316, 53], [156, 289, 267, 206, 100], [179, 108, 312, 351, 148], [76, 325, 170, 112, 168], [42, 216, 68, 274, 137]], ![[134, 122, 165, 345, 40], [279, 72, 189, 186, 339], [171, 171, 272, 331, 123], [166, 283, 258, 338, 339], [34, 109, 246, 191, 209], [73, 2, 34, 319, 75], [295, 70, 239, 185, 160], [285, 304, 3, 238, 101], [307, 58, 105, 109, 254]], ![[0, 1], [229, 57, 184, 332, 116], [190, 51, 347, 248, 204], [180, 0, 342, 1, 119], [31, 194, 319, 290, 54], [314, 6, 74, 94, 122], [188, 306, 36, 165, 287], [51, 168, 74, 230, 251], [134, 122, 165, 345, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [214, 99, 20, 87], [], [], []]
 b := ![[], [330, 22, 231, 183, 69], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI353N0 : CertifiedPrimeIdeal' SI353N0 353 where
  n := 5
  hpos := by decide
  P := [71, 111, 330, 321, 161, 1]
  hirr := P353P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![48870512081, 125072048809, -36991159460, -145687678057, -19158776715]
  a := ![1, 1, 1, -1, 4]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![138443377, 354311753, -104790820, -412712969, -54274155]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI353N0 : Ideal.IsPrime I353N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI353N0 B_one_repr
lemma NI353N0 : Nat.card (O ⧸ I353N0) = 5481173216993 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI353N0

def PBC353 : ContainsPrimesAboveP 353 ![I353N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI353N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![353, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 353 (by decide) 𝕀

instance hp359 : Fact (Nat.Prime 359) := {out := by norm_num}

def I359N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10897, 5846, -2526, 492, -914]] i)))

def SI359N0: IdealEqSpanCertificate' Table ![![10897, 5846, -2526, 492, -914]] 
 ![![359, 0, 0, 0, 0], ![0, 359, 0, 0, 0], ![0, 0, 359, 0, 0], ![0, 0, 0, 359, 0], ![199, 157, 251, 166, 1]] where
  M :=![![![10897, 5846, -2526, 492, -914], ![-5484, -2813, 1432, -180, 492], ![2952, 1896, -305, 276, -180], ![-1656, -906, 390, -41, 136], ![-1200, -438, 626, 168, 187]]]
  hmulB := by decide  
  f := ![![![-49, -82, 26, -12, 10]], ![![60, 101, -32, 12, -12]], ![![-72, -120, 41, -12, 12]], ![![48, 78, -26, 17, -8]], ![![-29, -49, 17, -2, 5]]]
  g := ![![![537, 416, 632, 424, -914], ![-288, -223, -340, -228, 492], ![108, 84, 125, 84, -180], ![-80, -62, -94, -63, 136], ![-107, -83, -129, -86, 187]]]
  hle1 := by decide   
  hle2 := by decide  


def P359P0 : CertificateIrreducibleZModOfList' 359 4 2 8 [218, 239, 89, 283, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [342, 55, 202, 189], [125, 246, 10, 232], [327, 57, 147, 297], [0, 1]]
 g := ![![[117, 135, 353, 243], [346, 331, 150, 133], [57, 233, 63, 50], [32, 259, 292], [63, 99, 320], [240, 332, 217, 18], [76, 1], []], ![[282, 77, 246, 223, 153, 271], [280, 230, 46, 33, 271, 293], [149, 319, 160, 102, 69, 215], [281, 260, 54], [281, 236, 264], [310, 194, 286, 249, 173, 83], [95, 217, 215, 0, 338, 174], [177, 286, 180]], ![[27, 36, 250, 202, 187, 332], [113, 323, 352, 198, 5, 232], [134, 125, 244, 302, 192, 117], [97, 202, 141], [177, 222, 235], [258, 264, 213, 250, 251, 61], [218, 220, 35, 255, 269, 236], [230, 151, 333]], ![[27, 177, 51, 282, 93, 69], [246, 120, 224, 62, 132, 294], [138, 295, 97, 99, 103, 204], [342, 93, 298], [74, 81, 275], [10, 109, 22, 184, 216, 22], [231, 165, 19, 125, 91, 240], [116, 358, 254]]]
 h' := ![![[342, 55, 202, 189], [321, 171, 159, 328], [139, 294, 352, 301], [74, 268, 14, 264], [128, 86, 146, 322], [94, 266, 239, 252], [305, 286, 177, 302], [0, 0, 1], [0, 1]], ![[125, 246, 10, 232], [114, 45, 148, 330], [344, 142, 173, 329], [266, 134, 270, 218], [146, 234, 28, 316], [71, 172, 323, 56], [43, 326, 20, 44], [116, 102, 255, 262], [342, 55, 202, 189]], ![[327, 57, 147, 297], [318, 221, 165, 296], [52, 43, 150, 1], [176, 157, 275, 266], [44, 15, 95, 315], [335, 309, 152, 275], [94, 305, 110, 38], [308, 178, 278, 298], [125, 246, 10, 232]], ![[0, 1], [57, 281, 246, 123], [159, 239, 43, 87], [125, 159, 159, 329], [356, 24, 90, 124], [232, 330, 4, 135], [101, 160, 52, 334], [148, 79, 184, 158], [327, 57, 147, 297]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [58, 197, 306], []]
 b := ![[], [], [120, 350, 53, 107], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI359N0 : CertifiedPrimeIdeal' SI359N0 359 where
  n := 4
  hpos := by decide
  P := [218, 239, 89, 283, 1]
  hirr := P359P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-18226, -87029, 61454, 173091, -25945]
  a := ![4, 0, 0, 1, 0]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![14331, 11104, 18311, 12479, -25945]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI359N0 : Ideal.IsPrime I359N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI359N0 B_one_repr
lemma NI359N0 : Nat.card (O ⧸ I359N0) = 16610312161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI359N0

def I359N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![49, 82, -26, 12, -10]] i)))

def SI359N1: IdealEqSpanCertificate' Table ![![49, 82, -26, 12, -10]] 
 ![![359, 0, 0, 0, 0], ![193, 1, 0, 0, 0], ![87, 0, 1, 0, 0], ![30, 0, 0, 1, 0], ![131, 0, 0, 0, 1]] where
  M :=![![![49, 82, -26, 12, -10], ![-60, -101, 32, -12, 12], ![72, 120, -41, 12, -12], ![-48, -78, 26, -17, 8], ![-24, -42, 22, 24, -5]]]
  hmulB := by decide  
  f := ![![![-10897, -5846, 2526, -492, 914]], ![![-5843, -3135, 1354, -264, 490]], ![![-2649, -1422, 613, -120, 222]], ![![-906, -486, 210, -41, 76]], ![![-3973, -2132, 920, -180, 333]]]
  g := ![![![-35, 82, -26, 12, -10], ![43, -101, 32, -12, 12], ![-51, 120, -41, 12, -12], ![34, -78, 26, -17, 8], ![17, -42, 22, 24, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI359N1 : Nat.card (O ⧸ I359N1) = 359 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI359N1)

lemma isPrimeI359N1 : Ideal.IsPrime I359N1 := prime_ideal_of_norm_prime hp359.out _ NI359N1
def MulI359N0 : IdealMulLeCertificate' Table 
  ![![10897, 5846, -2526, 492, -914]] ![![49, 82, -26, 12, -10]]
  ![![359, 0, 0, 0, 0]] where
 M := ![![![-359, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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


lemma PB1556I7_primes (p : ℕ) :
  p ∈ Set.range ![311, 313, 317, 331, 337, 347, 349, 353, 359] ↔ Nat.Prime p ∧ 307 < p ∧ p ≤ 359 := by
  rw [← List.mem_ofFn']
  convert primes_range 307 359 (by omega)

def PB1556I7 : PrimesBelowBoundCertificateInterval O 307 359 1556 where
  m := 9
  g := ![2, 1, 2, 3, 3, 1, 4, 1, 2]
  P := ![311, 313, 317, 331, 337, 347, 349, 353, 359]
  hP := PB1556I7_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I311N0, I311N1]
    · exact ![I313N0]
    · exact ![I317N0, I317N1]
    · exact ![I331N0, I331N1, I331N2]
    · exact ![I337N0, I337N1, I337N2]
    · exact ![I347N0]
    · exact ![I349N0, I349N1, I349N2, I349N3]
    · exact ![I353N0]
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
    · exact ![3004150512793]
    · exact ![31855013, 100489]
    · exact ![109561, 109561, 331]
    · exact ![38272753, 337, 337]
    · exact ![5030919566507]
    · exact ![121801, 349, 349, 349]
    · exact ![5481173216993]
    · exact ![16610312161, 359]
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
    · dsimp ; intro j
      fin_cases j
      exact NI317N0
      exact NI317N1
    · dsimp ; intro j
      fin_cases j
      exact NI331N0
      exact NI331N1
      exact NI331N2
    · dsimp ; intro j
      fin_cases j
      exact NI337N0
      exact NI337N1
      exact NI337N2
    · dsimp ; intro j
      fin_cases j
      exact NI347N0
    · dsimp ; intro j
      fin_cases j
      exact NI349N0
      exact NI349N1
      exact NI349N2
      exact NI349N3
    · dsimp ; intro j
      fin_cases j
      exact NI353N0
    · dsimp ; intro j
      fin_cases j
      exact NI359N0
      exact NI359N1
  β := ![I311N1, I331N2, I337N1, I337N2, I349N1, I349N2, I349N3, I359N1]
  Il := ![[I311N1], [], [], [I331N2], [I337N1, I337N2], [], [I349N1, I349N2, I349N3], [], [I359N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
