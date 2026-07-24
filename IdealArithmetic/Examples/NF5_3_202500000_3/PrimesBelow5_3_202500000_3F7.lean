
import IdealArithmetic.Examples.NF5_3_202500000_3.RI5_3_202500000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp311 : Fact (Nat.Prime 311) := {out := by norm_num}

def I311N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 13, 8, -9, -22]] i)))

def SI311N0: IdealEqSpanCertificate' Table ![![5, 13, 8, -9, -22]] 
 ![![311, 0, 0, 0, 0], ![0, 311, 0, 0, 0], ![0, 0, 311, 0, 0], ![286, 206, 28, 1, 0], ![10, 212, 73, 0, 1]] where
  M :=![![![5, 13, 8, -9, -22], ![60, 9, 66, -52, -124], ![384, 106, 365, -292, -816], ![330, 254, 62, -201, -314], ![114, -26, 208, -112, -393]]]
  hmulB := by decide  
  f := ![![![25, 33, 44, -29, -80]], ![![84, 47, 58, -40, -108]], ![![144, 114, 119, -84, -224]], ![![92, 72, 90, -61, -166]], ![![92, 60, 69, -48, -129]]]
  g := ![![![9, 21, 6, -9, -22], ![52, 119, 34, -52, -124], ![296, 750, 219, -292, -816], ![196, 348, 92, -201, -314], ![116, 342, 103, -112, -393]]]
  hle1 := by decide   
  hle2 := by decide  


def P311P0 : CertificateIrreducibleZModOfList' 311 3 2 8 [103, 138, 285, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [163, 253, 162], [174, 57, 149], [0, 1]]
 g := ![![[89, 157, 234], [180, 224, 278], [221, 126, 4], [117, 10], [132, 241, 60], [123, 231, 214], [26, 1], []], ![[178, 165, 166, 245], [300, 143, 41, 235], [123, 289, 227, 108], [40, 270], [210, 109, 161, 256], [282, 203, 63, 3], [135, 139], [189, 120]], ![[14, 267, 259, 227], [220, 30, 208, 177], [79, 57, 52, 171], [48, 24], [12, 248, 178, 281], [197, 254, 39, 119], [74, 254], [202, 120]]]
 h' := ![![[163, 253, 162], [120, 161, 168], [251, 96, 281], [47, 161, 2], [88, 72, 53], [82, 309, 252], [121, 41, 227], [0, 0, 1], [0, 1]], ![[174, 57, 149], [68, 283, 204], [13, 78, 158], [64, 51, 72], [102, 31, 68], [277, 86, 45], [203, 120, 299], [260, 185, 57], [163, 253, 162]], ![[0, 1], [28, 178, 250], [4, 137, 183], [40, 99, 237], [132, 208, 190], [182, 227, 14], [160, 150, 96], [140, 126, 253], [174, 57, 149]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [208, 49], []]
 b := ![[], [67, 298, 136], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI311N0 : CertifiedPrimeIdeal' SI311N0 311 where
  n := 3
  hpos := by decide
  P := [103, 138, 285, 1]
  hirr := P311P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![149485045, 37782793, 149513406, -121720141, -320894712]
  a := ![153, 6, 189, -140, -391]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![122734381, 299491353, 86762030, -121720141, -320894712]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI311N0 : Ideal.IsPrime I311N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI311N0 B_one_repr
lemma NI311N0 : Nat.card (O ⧸ I311N0) = 30080231 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI311N0

def I311N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![25, 33, 44, -29, -80]] i)))

def SI311N1: IdealEqSpanCertificate' Table ![![25, 33, 44, -29, -80]] 
 ![![311, 0, 0, 0, 0], ![0, 311, 0, 0, 0], ![222, 255, 1, 0, 0], ![307, 254, 0, 1, 0], ![166, 5, 0, 0, 1]] where
  M :=![![![25, 33, 44, -29, -80], ![84, 47, 58, -40, -108], ![144, 114, 119, -84, -224], ![126, 80, 126, -85, -226], ![42, 44, 36, -26, -71]]]
  hmulB := by decide  
  f := ![![![5, 13, 8, -9, -22]], ![![60, 9, 66, -52, -124]], ![![54, 17, 61, -50, -120]], ![![55, 21, 62, -52, -124]], ![![4, 7, 6, -6, -15]]]
  g := ![![![40, -11, 44, -29, -80], ![56, -13, 58, -40, -108], ![118, -25, 119, -84, -224], ![115, -30, 126, -85, -226], ![38, -7, 36, -26, -71]]]
  hle1 := by decide   
  hle2 := by decide  


def P311P1 : CertificateIrreducibleZModOfList' 311 2 2 8 [250, 165, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [146, 310], [0, 1]]
 g := ![![[293, 260], [68, 89], [49, 117], [178], [173, 267], [157, 70], [168], [1]], ![[0, 51], [0, 222], [26, 194], [178], [280, 44], [114, 241], [168], [1]]]
 h' := ![![[146, 310], [105, 142], [190, 20], [103, 257], [290, 235], [247, 189], [285, 44], [61, 146], [0, 1]], ![[0, 1], [0, 169], [0, 291], [305, 54], [79, 76], [162, 122], [178, 267], [229, 165], [146, 310]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [157]]
 b := ![[], [23, 234]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI311N1 : CertifiedPrimeIdeal' SI311N1 311 where
  n := 2
  hpos := by decide
  P := [250, 165, 1]
  hirr := P311P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-327074, 160502, -879177, 550327, 1346162]
  a := ![-183, -72, -226, 103, 468]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-635251, 250279, -879177, 550327, 1346162]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI311N1 : Ideal.IsPrime I311N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI311N1 B_one_repr
lemma NI311N1 : Nat.card (O ⧸ I311N1) = 96721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI311N1
def MulI311N0 : IdealMulLeCertificate' Table 
  ![![5, 13, 8, -9, -22]] ![![25, 33, 44, -29, -80]]
  ![![311, 0, 0, 0, 0]] where
 M := ![![![311, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I313N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 3, 17, -10, -38]] i)))

def SI313N0: IdealEqSpanCertificate' Table ![![19, 3, 17, -10, -38]] 
 ![![313, 0, 0, 0, 0], ![0, 313, 0, 0, 0], ![0, 0, 313, 0, 0], ![306, 156, 106, 1, 0], ![59, 33, 227, 0, 1]] where
  M :=![![![19, 3, 17, -10, -38], ![-96, 18, -155, 94, 296], ![168, -143, 524, -262, -824], ![-180, 187, -691, 405, 984], ![120, -141, 475, -252, -691]]]
  hmulB := by decide  
  f := ![![![67, -23, -51, 30, 90]], ![![0, 46, 67, -42, -120]], ![![72, 31, 16, -10, -24]], ![![90, 11, -11, 5, 20]], ![![65, 23, 9, -6, -13]]]
  g := ![![![17, 9, 31, -10, -38], ![-148, -78, -247, 94, 296], ![412, 217, 688, -262, -824], ![-582, -305, -853, 405, 984], ![377, 198, 588, -252, -691]]]
  hle1 := by decide   
  hle2 := by decide  


def P313P0 : CertificateIrreducibleZModOfList' 313 3 2 8 [70, 158, 223, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [124, 141, 95], [279, 171, 218], [0, 1]]
 g := ![![[34, 190, 263], [167, 163], [70, 115], [159, 205, 24], [219, 174, 280], [14, 274, 230], [90, 1], []], ![[292, 60, 144, 101], [3, 217], [229, 83], [14, 63, 49, 229], [130, 227, 187, 283], [297, 149, 110, 267], [81, 132], [200, 261]], ![[189, 65, 41, 37], [10, 140], [148, 50], [183, 163, 254, 296], [94, 20, 251, 282], [27, 13, 280, 138], [208, 162], [77, 261]]]
 h' := ![![[124, 141, 95], [242, 189, 24], [59, 54, 199], [138, 15, 179], [7, 284, 201], [272, 240, 210], [273, 108, 117], [0, 0, 1], [0, 1]], ![[279, 171, 218], [49, 155, 149], [131, 279, 34], [93, 165, 108], [51, 88, 3], [45, 303, 179], [3, 80, 219], [124, 122, 171], [124, 141, 95]], ![[0, 1], [185, 282, 140], [131, 293, 80], [141, 133, 26], [67, 254, 109], [30, 83, 237], [145, 125, 290], [148, 191, 141], [279, 171, 218]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [293, 178], []]
 b := ![[], [241, 289, 265], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI313N0 : CertifiedPrimeIdeal' SI313N0 313 where
  n := 3
  hpos := by decide
  P := [70, 158, 223, 1]
  hirr := P313P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3232154, 947602, 3141214, -2674486, -6685470]
  a := ![38, -1, 47, -37, -97]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3885200, 2040856, 5764340, -2674486, -6685470]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI313N0 : Ideal.IsPrime I313N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI313N0 B_one_repr
lemma NI313N0 : Nat.card (O ⧸ I313N0) = 30664297 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI313N0

def I313N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-67, 23, 51, -30, -90]] i)))

def SI313N1: IdealEqSpanCertificate' Table ![![-67, 23, 51, -30, -90]] 
 ![![313, 0, 0, 0, 0], ![0, 313, 0, 0, 0], ![172, 101, 1, 0, 0], ![78, 307, 0, 1, 0], ![27, 212, 0, 0, 1]] where
  M :=![![![-67, 23, 51, -30, -90], ![0, -46, -67, 42, 120], ![-72, -31, -16, 10, 24], ![-36, -19, -15, 3, 16], ![-48, -1, 17, -8, -29]]]
  hmulB := by decide  
  f := ![![![-19, -3, -17, 10, 38]], ![![96, -18, 155, -94, -296]], ![![20, -7, 39, -24, -72]], ![![90, -19, 150, -91, -284]], ![![63, -12, 102, -62, -195]]]
  g := ![![![-13, 74, 51, -30, -90], ![16, -101, -67, 42, 120], ![4, -21, -16, 10, 24], ![6, -9, -15, 3, 16], ![-5, 22, 17, -8, -29]]]
  hle1 := by decide   
  hle2 := by decide  


def P313P1 : CertificateIrreducibleZModOfList' 313 2 2 8 [63, 259, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [54, 312], [0, 1]]
 g := ![![[178, 26], [98], [142], [136, 310], [214, 158], [182, 181], [99], [1]], ![[17, 287], [98], [142], [287, 3], [295, 155], [253, 132], [99], [1]]]
 h' := ![![[54, 312], [199, 85], [48, 99], [196, 237], [290, 116], [115, 285], [236, 107], [250, 54], [0, 1]], ![[0, 1], [94, 228], [73, 214], [161, 76], [294, 197], [168, 28], [67, 206], [36, 259], [54, 312]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [133]]
 b := ![[], [239, 223]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI313N1 : CertifiedPrimeIdeal' SI313N1 313 where
  n := 2
  hpos := by decide
  P := [63, 259, 1]
  hirr := P313P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-775833, -249207, -658887, 604518, 1513178]
  a := ![-259, 5, -320, 250, 662]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![78417, -1406014, -658887, 604518, 1513178]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI313N1 : Ideal.IsPrime I313N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI313N1 B_one_repr
lemma NI313N1 : Nat.card (O ⧸ I313N1) = 97969 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI313N1
def MulI313N0 : IdealMulLeCertificate' Table 
  ![![19, 3, 17, -10, -38]] ![![-67, 23, 51, -30, -90]]
  ![![313, 0, 0, 0, 0]] where
 M := ![![![-313, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC313 : ContainsPrimesAboveP 313 ![I313N0, I313N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI313N0
    exact isPrimeI313N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 313 (by decide) (𝕀 ⊙ MulI313N0)
instance hp317 : Fact (Nat.Prime 317) := {out := by norm_num}

def I317N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3481, -2460, -2916, 1988, 5370]] i)))

def SI317N0: IdealEqSpanCertificate' Table ![![-3481, -2460, -2916, 1988, 5370]] 
 ![![317, 0, 0, 0, 0], ![0, 317, 0, 0, 0], ![0, 0, 317, 0, 0], ![228, 98, 174, 1, 0], ![64, 206, 257, 0, 1]] where
  M :=![![![-3481, -2460, -2916, 1988, 5370], ![-7128, -5003, -6000, 4084, 11056], ![-14352, -10240, -11887, 8128, 21936], ![-11124, -7778, -9512, 6439, 17384], ![-4920, -3550, -3988, 2746, 7417]]]
  hmulB := by decide  
  f := ![![![907, -624, -1164, 704, 2066]], ![![-552, 401, 752, -460, -1344]], ![![432, -224, -403, 224, 688]], ![![720, -448, -826, 487, 1448]], ![![176, -48, -75, 26, 105]]]
  g := ![![![-2525, -4112, -5454, 1988, 5370], ![-5192, -8463, -11224, 4084, 11056], ![-10320, -16800, -22283, 8128, 21936], ![-8176, -13312, -17658, 6439, 17384], ![-3488, -5680, -7533, 2746, 7417]]]
  hle1 := by decide   
  hle2 := by decide  


def P317P0 : CertificateIrreducibleZModOfList' 317 3 2 8 [147, 221, 204, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [115, 155, 220], [315, 161, 97], [0, 1]]
 g := ![![[10, 297, 193], [215, 61], [300, 65, 221], [92, 305, 225], [88, 3, 306], [98, 65, 306], [113, 1], []], ![[228, 271, 211, 189], [191, 227], [104, 307, 177, 211], [172, 74, 296, 229], [64, 1, 25, 270], [203, 167, 158, 102], [27, 244], [44, 216]], ![[175, 145, 91, 242], [237, 94], [116, 169, 119, 30], [204, 38, 43, 265], [289, 171, 2, 299], [157, 285, 142, 72], [148, 250], [167, 216]]]
 h' := ![![[115, 155, 220], [196, 210, 142], [280, 262, 78], [107, 52, 236], [61, 309, 302], [176, 132, 132], [190, 240, 185], [0, 0, 1], [0, 1]], ![[315, 161, 97], [189, 294, 273], [170, 184, 141], [206, 28, 301], [177, 243, 263], [26, 182, 206], [8, 101, 165], [100, 197, 161], [115, 155, 220]], ![[0, 1], [118, 130, 219], [243, 188, 98], [241, 237, 97], [215, 82, 69], [29, 3, 296], [227, 293, 284], [181, 120, 155], [315, 161, 97]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [147, 293], []]
 b := ![[], [85, 12, 271], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI317N0 : CertifiedPrimeIdeal' SI317N0 317 where
  n := 3
  hpos := by decide
  P := [147, 221, 204, 1]
  hirr := P317P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1501083207, 404763480, 1393958188, -1139034032, -3137179434]
  a := ![385, 23, 476, -339, -984]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1457351187, 2392079060, 3172999982, -1139034032, -3137179434]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI317N0 : Ideal.IsPrime I317N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI317N0 B_one_repr
lemma NI317N0 : Nat.card (O ⧸ I317N0) = 31855013 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI317N0

def I317N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-25, 26, 51, -33, -94]] i)))

def SI317N1: IdealEqSpanCertificate' Table ![![-25, 26, 51, -33, -94]] 
 ![![317, 0, 0, 0, 0], ![124, 1, 0, 0, 0], ![157, 0, 1, 0, 0], ![31, 0, 0, 1, 0], ![92, 0, 0, 0, 1]] where
  M :=![![![-25, 26, 51, -33, -94], ![60, -2, 7, -14, -28], ![168, 67, 180, -154, -392], ![390, 133, 359, -317, -798], ![-42, 3, 1, 6, 9]]]
  hmulB := by decide  
  f := ![![![985, 658, 899, -599, -1620]], ![![392, 262, 357, -238, -644]], ![![497, 335, 451, -301, -812]], ![![113, 69, 110, -72, -198]], ![![286, 195, 257, -172, -463]]]
  g := ![![![-5, 26, 51, -33, -94], ![7, -2, 7, -14, -28], ![14, 67, 180, -154, -392], ![34, 133, 359, -317, -798], ![-5, 3, 1, 6, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI317N1 : Nat.card (O ⧸ I317N1) = 317 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI317N1)

lemma isPrimeI317N1 : Ideal.IsPrime I317N1 := prime_ideal_of_norm_prime hp317.out _ NI317N1

def I317N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13, 8, 15, -9, -26]] i)))

def SI317N2: IdealEqSpanCertificate' Table ![![-13, 8, 15, -9, -26]] 
 ![![317, 0, 0, 0, 0], ![162, 1, 0, 0, 0], ![67, 0, 1, 0, 0], ![198, 0, 0, 1, 0], ![118, 0, 0, 0, 1]] where
  M :=![![![-13, 8, 15, -9, -26], ![12, -6, -3, 2, 4], ![-24, 9, -32, 18, 56], ![6, -15, 49, -25, -70], ![-18, 13, -27, 14, 41]]]
  hmulB := by decide  
  f := ![![![-683, -444, -569, 401, 1072]], ![![-354, -230, -295, 208, 556]], ![![-157, -101, -131, 93, 248]], ![![-444, -285, -371, 263, 702]], ![![-256, -167, -213, 150, 401]]]
  g := ![![![8, 8, 15, -9, -26], ![1, -6, -3, 2, 4], ![-30, 9, -32, 18, 56], ![39, -15, 49, -25, -70], ![-25, 13, -27, 14, 41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI317N2 : Nat.card (O ⧸ I317N2) = 317 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI317N2)

lemma isPrimeI317N2 : Ideal.IsPrime I317N2 := prime_ideal_of_norm_prime hp317.out _ NI317N2
def MulI317N0 : IdealMulLeCertificate' Table 
  ![![-3481, -2460, -2916, 1988, 5370]] ![![-25, 26, 51, -33, -94]]
  ![![-683, -444, -569, 401, 1072]] where
 M := ![![![-683, -444, -569, 401, 1072]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI317N1 : IdealMulLeCertificate' Table 
  ![![-683, -444, -569, 401, 1072]] ![![-13, 8, 15, -9, -26]]
  ![![317, 0, 0, 0, 0]] where
 M := ![![![317, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC317 : ContainsPrimesAboveP 317 ![I317N0, I317N1, I317N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI317N0
    exact isPrimeI317N1
    exact isPrimeI317N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 317 (by decide) (𝕀 ⊙ MulI317N0 ⊙ MulI317N1)
instance hp331 : Fact (Nat.Prime 331) := {out := by norm_num}

def I331N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![331, 0, 0, 0, 0]] i)))

def SI331N0: IdealEqSpanCertificate' Table ![![331, 0, 0, 0, 0]] 
 ![![331, 0, 0, 0, 0], ![0, 331, 0, 0, 0], ![0, 0, 331, 0, 0], ![0, 0, 0, 331, 0], ![0, 0, 0, 0, 331]] where
  M :=![![![331, 0, 0, 0, 0], ![0, 331, 0, 0, 0], ![0, 0, 331, 0, 0], ![0, 0, 0, 331, 0], ![0, 0, 0, 0, 331]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P331P0 : CertificateIrreducibleZModOfList' 331 5 2 8 [310, 262, 115, 160, 25, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [281, 118, 176, 102, 145], [78, 136, 16, 163, 90], [168, 178, 8, 322, 118], [110, 229, 131, 75, 309], [0, 1]]
 g := ![![[171, 187, 62, 42, 281], [309, 215, 168, 9, 280], [124, 257, 88, 281], [277, 308, 157, 104, 316], [288, 197, 38, 281], [264, 167, 319, 294], [1], []], ![[29, 309, 63, 140, 272, 263, 140, 10], [44, 78, 281, 243, 93, 241, 79, 116], [230, 21, 1, 296], [151, 260, 193, 3, 194, 262, 241, 243], [328, 66, 13, 194], [33, 199, 229, 150], [250, 168, 299, 324, 145, 318, 330, 309], [20, 41, 124, 172]], ![[180, 26, 25, 326, 160, 167, 85, 250], [55, 279, 40, 306, 266, 0, 182, 97], [329, 254, 103, 296], [173, 316, 93, 250, 124, 164, 258, 60], [247, 233, 280, 19], [321, 131, 310, 316], [118, 220, 99, 302, 313, 262, 43, 204], [146, 37, 284, 156]], ![[10, 309, 104, 271, 137, 79, 146, 320], [160, 11, 43, 5, 124, 241, 130, 45], [96, 216, 241, 302], [232, 298, 29, 14, 113, 191, 2, 43], [101, 138, 123, 156], [279, 140, 183, 163], [165, 167, 206, 149, 264, 141, 135, 258], [150, 92, 305, 22]], ![[330, 192, 50, 329, 87, 27, 111, 221], [39, 326, 304, 272, 162, 118, 72, 327], [103, 242, 170, 132], [125, 143, 286, 104, 8, 137, 117, 237], [58, 87, 285, 223], [145, 305, 11, 183], [88, 117, 91, 189, 163, 175, 78, 107], [254, 253, 157, 153]]]
 h' := ![![[281, 118, 176, 102, 145], [200, 216, 141, 104, 287], [308, 5, 146, 263, 131], [190, 249, 203, 111, 287], [157, 84, 222, 101, 115], [27, 127, 40, 89, 287], [21, 69, 216, 171, 306], [0, 0, 1], [0, 1]], ![[78, 136, 16, 163, 90], [329, 32, 71, 113, 246], [37, 236, 264, 62, 304], [145, 53, 26, 86, 222], [217, 48, 257, 191, 295], [131, 2, 220, 286, 288], [10, 240, 283, 303, 124], [272, 40, 119, 172, 313], [281, 118, 176, 102, 145]], ![[168, 178, 8, 322, 118], [9, 50, 123, 76, 112], [239, 102, 66, 244, 317], [287, 261, 270, 207, 222], [5, 147, 308, 33, 80], [86, 187, 319, 22, 130], [222, 42, 147, 137, 216], [213, 291, 141, 212, 24], [78, 136, 16, 163, 90]], ![[110, 229, 131, 75, 309], [195, 248, 97, 218, 250], [183, 227, 16, 235, 11], [22, 75, 106, 186, 77], [276, 220, 208, 186, 196], [97, 68, 275, 259, 241], [14, 262, 267, 25, 297], [260, 263, 85, 322, 38], [168, 178, 8, 322, 118]], ![[0, 1], [277, 116, 230, 151, 98], [254, 92, 170, 189, 230], [210, 24, 57, 72, 185], [306, 163, 329, 151, 307], [322, 278, 139, 6, 47], [315, 49, 80, 26, 50], [222, 68, 316, 287, 287], [110, 229, 131, 75, 309]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [288, 89, 243, 314], [], [], []]
 b := ![[], [71, 155, 77, 305, 201], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI331N0 : CertifiedPrimeIdeal' SI331N0 331 where
  n := 5
  hpos := by decide
  P := [310, 262, 115, 160, 25, 1]
  hirr := P331P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![194704709412190, -49867399242976, 360854310069440, -205669424825168, -655127506802432]
  a := ![-162, -18, -200, 126, 414]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![588231750490, -150656795296, 1090194290240, -621357778928, -1979237180672]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI331N0 : Ideal.IsPrime I331N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI331N0 B_one_repr
lemma NI331N0 : Nat.card (O ⧸ I331N0) = 3973195810651 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI331N0

def PBC331 : ContainsPrimesAboveP 331 ![I331N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI331N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![331, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 331 (by decide) 𝕀

instance hp337 : Fact (Nat.Prime 337) := {out := by norm_num}

def I337N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1531, 416, 272, -232, -542]] i)))

def SI337N0: IdealEqSpanCertificate' Table ![![1531, 416, 272, -232, -542]] 
 ![![337, 0, 0, 0, 0], ![0, 337, 0, 0, 0], ![0, 0, 337, 0, 0], ![185, 288, 147, 1, 0], ![84, 60, 240, 0, 1]] where
  M :=![![![1531, 416, 272, -232, -542], ![1848, 1725, 2184, -1460, -4000], ![4560, 2952, 3425, -2352, -6320], ![3492, 2322, 2744, -1877, -5072], ![1728, 890, 936, -662, -1739]]]
  hmulB := by decide  
  f := ![![![-77, -28, -64, 60, 146]], ![![-408, -115, -392, 332, 848]], ![![-1776, -616, -1487, 1360, 3408]], ![![-1177, -386, -1029, 919, 2314]], ![![-1356, -466, -1144, 1042, 2613]]]
  g := ![![![267, 296, 488, -232, -542], ![1804, 1965, 3492, -1460, -4000], ![2880, 3144, 5537, -2352, -6320], ![2305, 2514, 4439, -1877, -5072], ![802, 878, 1530, -662, -1739]]]
  hle1 := by decide   
  hle2 := by decide  


def P337P0 : CertificateIrreducibleZModOfList' 337 3 2 8 [73, 154, 254, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [73, 112, 231], [10, 224, 106], [0, 1]]
 g := ![![[336, 51, 328], [51, 252], [236, 295], [120, 131], [299, 84, 50], [267, 290], [332, 83, 1], []], ![[302, 194, 104, 38], [333, 253], [279, 107], [219, 78], [7, 36, 167, 34], [52, 262], [49, 149, 247, 215], [292, 115]], ![[18, 248, 265, 174], [42, 128], [297, 216], [82, 6], [258, 53, 200, 280], [22, 52], [223, 177, 304, 199], [80, 115]]]
 h' := ![![[73, 112, 231], [131, 138, 230], [22, 324, 297], [20, 284, 162], [78, 322, 145], [165, 96, 207], [28, 103, 210], [0, 0, 1], [0, 1]], ![[10, 224, 106], [92, 44, 159], [275, 228, 169], [146, 252, 118], [102, 135, 33], [127, 49, 133], [57, 336, 63], [189, 59, 224], [73, 112, 231]], ![[0, 1], [329, 155, 285], [332, 122, 208], [67, 138, 57], [18, 217, 159], [196, 192, 334], [96, 235, 64], [326, 278, 112], [10, 224, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [250, 254], []]
 b := ![[], [27, 147, 155], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI337N0 : CertifiedPrimeIdeal' SI337N0 337 where
  n := 3
  hpos := by decide
  P := [73, 154, 254, 1]
  hirr := P337P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1370515922, -444828249, -1207259779, 1076838246, 2704742622]
  a := ![-163, 3, -201, 170, 418]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1269388640, -1403141841, -2399527333, 1076838246, 2704742622]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI337N0 : Ideal.IsPrime I337N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI337N0 B_one_repr
lemma NI337N0 : Nat.card (O ⧸ I337N0) = 38272753 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI337N0

def I337N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![77, 28, 64, -60, -146]] i)))

def SI337N1: IdealEqSpanCertificate' Table ![![77, 28, 64, -60, -146]] 
 ![![337, 0, 0, 0, 0], ![0, 337, 0, 0, 0], ![248, 43, 1, 0, 0], ![60, 211, 0, 1, 0], ![132, 172, 0, 0, 1]] where
  M :=![![![77, 28, 64, -60, -146], ![408, 115, 392, -332, -848], ![1776, 616, 1487, -1360, -3408], ![3828, 1230, 3448, -3067, -7608], ![-216, -50, -248, 206, 483]]]
  hmulB := by decide  
  f := ![![![-1531, -416, -272, 232, 542]], ![![-1848, -1725, -2184, 1460, 4000]], ![![-1376, -535, -489, 364, 928]], ![![-1440, -1161, -1424, 961, 2616]], ![![-1548, -1046, -1224, 838, 2259]]]
  g := ![![![21, 104, 64, -60, -146], ![104, 591, 392, -332, -848], ![488, 2403, 1487, -1360, -3408], ![1000, 5367, 3448, -3067, -7608], ![-44, -344, -248, 206, 483]]]
  hle1 := by decide   
  hle2 := by decide  


def P337P1 : CertificateIrreducibleZModOfList' 337 2 2 8 [33, 87, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [250, 336], [0, 1]]
 g := ![![[309, 319], [149], [274], [220], [132, 94], [16], [8, 155], [1]], ![[190, 18], [149], [274], [220], [42, 243], [16], [3, 182], [1]]]
 h' := ![![[250, 336], [311, 251], [298, 254], [105, 73], [25, 54], [83, 46], [73, 333], [304, 250], [0, 1]], ![[0, 1], [42, 86], [105, 83], [157, 264], [45, 283], [125, 291], [84, 4], [122, 87], [250, 336]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [161]]
 b := ![[], [216, 249]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI337N1 : CertifiedPrimeIdeal' SI337N1 337 where
  n := 2
  hpos := by decide
  P := [33, 87, 1]
  hirr := P337P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2473, 2909, -4245, 1724, 1816]
  a := ![-47, -7, -58, 36, 120]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2113, -1456, -4245, 1724, 1816]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI337N1 : Ideal.IsPrime I337N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI337N1 B_one_repr
lemma NI337N1 : Nat.card (O ⧸ I337N1) = 113569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI337N1
def MulI337N0 : IdealMulLeCertificate' Table 
  ![![1531, 416, 272, -232, -542]] ![![77, 28, 64, -60, -146]]
  ![![337, 0, 0, 0, 0]] where
 M := ![![![-337, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I347N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![56257, 39685, 47144, -32143, -86880]] i)))

def SI347N0: IdealEqSpanCertificate' Table ![![56257, 39685, 47144, -32143, -86880]] 
 ![![347, 0, 0, 0, 0], ![0, 347, 0, 0, 0], ![0, 0, 347, 0, 0], ![0, 0, 0, 347, 0], ![344, 322, 310, 330, 1]] where
  M :=![![![56257, 39685, 47144, -32143, -86880], ![114588, 80807, 96040, -65488, -176996], ![233616, 164608, 195831, -133576, -361024], ![180930, 127384, 151552, -103521, -279614], ![79878, 56318, 67000, -45650, -123439]]]
  hmulB := by decide  
  f := ![![![-199, 137, 256, -155, -454]], ![![132, -87, -152, 92, 268]], ![![-96, 64, 61, -40, -112]], ![![-18, 10, 112, -65, -182]], ![![-178, 122, 274, -166, -475]]]
  g := ![![![86291, 80735, 77752, 82531, -86880], ![175796, 164477, 158400, 168136, -176996], ![358576, 335488, 323093, 342952, -361024], ![277718, 259836, 250236, 265617, -279614], ![122602, 114708, 110470, 117260, -123439]]]
  hle1 := by decide   
  hle2 := by decide  


def P347P0 : CertificateIrreducibleZModOfList' 347 4 2 8 [101, 158, 21, 68, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [301, 102, 102, 119], [274, 22, 186, 305], [51, 222, 59, 270], [0, 1]]
 g := ![![[265, 93, 78, 74], [292, 39, 276, 4], [215, 49, 137], [265, 27, 190, 241], [26, 193, 34, 10], [186, 270, 136], [279, 1], []], ![[3, 220, 79, 332, 155, 116], [92, 301, 193, 223, 217, 156], [214, 137, 71], [160, 207, 222, 126, 71, 181], [79, 304, 232, 233, 72, 34], [325, 258, 89], [173, 311, 88, 205, 305, 172], [65, 310, 281]], ![[165, 206, 305, 181, 9, 238], [46, 255, 282, 15, 215, 5], [314, 205, 244], [108, 106, 138, 114, 9, 216], [62, 235, 233, 35, 154, 5], [325, 282, 259], [258, 133, 101, 74, 115, 195], [287, 101, 29]], ![[176, 86, 259, 285, 202, 197], [30, 108, 334, 63, 148, 36], [136, 268, 241], [142, 44, 123, 263, 71, 267], [111, 221, 67, 290, 271, 75], [146, 292, 140], [109, 63, 183, 106, 141, 30], [1, 325, 30]]]
 h' := ![![[301, 102, 102, 119], [3, 22, 206, 132], [180, 143, 210, 345], [301, 111, 63, 22], [150, 245, 234, 289], [278, 10, 222, 222], [275, 233, 229, 92], [0, 0, 1], [0, 1]], ![[274, 22, 186, 305], [268, 56, 330, 161], [261, 193, 103, 36], [19, 218, 67, 50], [53, 250, 121, 172], [322, 257, 268, 146], [23, 323, 137, 175], [62, 45, 22, 336], [301, 102, 102, 119]], ![[51, 222, 59, 270], [170, 20, 194, 259], [186, 313, 68, 331], [143, 196, 217, 217], [46, 137, 215, 326], [325, 91, 112, 16], [78, 172, 59, 134], [285, 231, 117, 242], [274, 22, 186, 305]], ![[0, 1], [319, 249, 311, 142], [188, 45, 313, 329], [229, 169, 0, 58], [141, 62, 124, 254], [186, 336, 92, 310], [59, 313, 269, 293], [71, 71, 207, 116], [51, 222, 59, 270]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [125, 196, 1], []]
 b := ![[], [], [268, 172, 305, 157], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI347N0 : CertifiedPrimeIdeal' SI347N0 347 where
  n := 4
  hpos := by decide
  P := [101, 158, 21, 68, 1]
  hirr := P347P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-289927072273, -95915905286, -254277983728, 228443439806, 568790306698]
  a := ![-165, -7, -203, 151, 422]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-564708335955, -528087592686, -508873985764, -540266160722, 568790306698]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI347N0 : Ideal.IsPrime I347N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI347N0 B_one_repr
lemma NI347N0 : Nat.card (O ⧸ I347N0) = 14498327281 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI347N0

def I347N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-199, 137, 256, -155, -454]] i)))

def SI347N1: IdealEqSpanCertificate' Table ![![-199, 137, 256, -155, -454]] 
 ![![347, 0, 0, 0, 0], ![208, 1, 0, 0, 0], ![111, 0, 1, 0, 0], ![150, 0, 0, 1, 0], ![297, 0, 0, 0, 1]] where
  M :=![![![-199, 137, 256, -155, -454], ![132, -87, -152, 92, 268], ![-96, 64, 61, -40, -112], ![-18, 10, 112, -65, -182], ![-114, 80, 88, -56, -165]]]
  hmulB := by decide  
  f := ![![![56257, 39685, 47144, -32143, -86880]], ![![34052, 24021, 28536, -19456, -52588]], ![![18669, 13169, 15645, -10667, -28832]], ![![24840, 17522, 20816, -14193, -38362]], ![![48381, 34129, 40544, -27643, -74717]]]
  g := ![![![291, 137, 256, -155, -454], ![-168, -87, -152, 92, 268], ![55, 64, 61, -40, -112], ![142, 10, 112, -65, -182], ![89, 80, 88, -56, -165]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI347N1 : Nat.card (O ⧸ I347N1) = 347 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI347N1)

lemma isPrimeI347N1 : Ideal.IsPrime I347N1 := prime_ideal_of_norm_prime hp347.out _ NI347N1
def MulI347N0 : IdealMulLeCertificate' Table 
  ![![56257, 39685, 47144, -32143, -86880]] ![![-199, 137, 256, -155, -454]]
  ![![347, 0, 0, 0, 0]] where
 M := ![![![347, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC347 : ContainsPrimesAboveP 347 ![I347N0, I347N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI347N0
    exact isPrimeI347N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 347 (by decide) (𝕀 ⊙ MulI347N0)
instance hp349 : Fact (Nat.Prime 349) := {out := by norm_num}

def I349N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4939, 3410, 4030, -2752, -7430]] i)))

def SI349N0: IdealEqSpanCertificate' Table ![![4939, 3410, 4030, -2752, -7430]] 
 ![![349, 0, 0, 0, 0], ![0, 349, 0, 0, 0], ![0, 0, 349, 0, 0], ![61, 148, 21, 1, 0], ![34, 246, 117, 0, 1]] where
  M :=![![![4939, 3410, 4030, -2752, -7430], ![9912, 7043, 8370, -5704, -15424], ![20256, 14266, 16939, -11548, -31200], ![15708, 11024, 13178, -8977, -24296], ![6936, 4876, 5746, -3922, -10579]]]
  hmulB := by decide  
  f := ![![![-185, -62, -166, 148, 370]], ![![-888, -277, -802, 704, 1776]], ![![-4032, -1322, -3541, 3164, 7936]], ![![-677, -216, -605, 535, 1346]], ![![-1994, -644, -1767, 1570, 3945]]]
  g := ![![![1219, 6414, 2668, -2752, -7430], ![2528, 13311, 5538, -5704, -15424], ![5116, 26930, 11203, -11548, -31200], ![3981, 20964, 8723, -8977, -24296], ![1736, 9134, 3799, -3922, -10579]]]
  hle1 := by decide   
  hle2 := by decide  


def P349P0 : CertificateIrreducibleZModOfList' 349 3 2 8 [248, 125, 128, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [168, 195, 339], [53, 153, 10], [0, 1]]
 g := ![![[247, 5, 68], [79, 42], [91, 346, 95], [301, 233, 95], [111, 265, 334], [343, 324], [205, 221, 1], []], ![[295, 175, 51, 197], [258, 139], [336, 9, 233, 40], [78, 200, 235, 62], [9, 177, 33, 193], [317, 345], [169, 113, 22, 89], [52, 100]], ![[48, 96, 237, 65], [59, 14], [102, 272, 250, 62], [95, 301, 27, 172], [151, 18, 15, 248], [89, 300], [68, 262, 182, 189], [32, 100]]]
 h' := ![![[168, 195, 339], [30, 33, 243], [117, 236, 33], [38, 321, 188], [43, 239, 161], [175, 149, 183], [114, 186, 331], [0, 0, 1], [0, 1]], ![[53, 153, 10], [166, 339, 204], [102, 197, 246], [191, 18, 77], [89, 294, 256], [190, 241, 334], [107, 348, 272], [321, 18, 153], [168, 195, 339]], ![[0, 1], [103, 326, 251], [135, 265, 70], [12, 10, 84], [84, 165, 281], [265, 308, 181], [1, 164, 95], [108, 331, 195], [53, 153, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [283, 185], []]
 b := ![[], [220, 33, 193], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI349N0 : CertifiedPrimeIdeal' SI349N0 349 where
  n := 3
  hpos := by decide
  P := [248, 125, 128, 1]
  hirr := P349P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-458589230, -132471963, -421838501, 356327202, 941100600]
  a := ![-241, -13, -298, 214, 616]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-155277848, -814841391, -338147507, 356327202, 941100600]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI349N0 : Ideal.IsPrime I349N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI349N0 B_one_repr
lemma NI349N0 : Nat.card (O ⧸ I349N0) = 42508549 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI349N0

def I349N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-185, -62, -166, 148, 370]] i)))

def SI349N1: IdealEqSpanCertificate' Table ![![-185, -62, -166, 148, 370]] 
 ![![349, 0, 0, 0, 0], ![0, 349, 0, 0, 0], ![58, 307, 1, 0, 0], ![171, 20, 0, 1, 0], ![9, 139, 0, 0, 1]] where
  M :=![![![-185, -62, -166, 148, 370], ![-888, -277, -802, 704, 1776], ![-4032, -1322, -3541, 3164, 7936], ![-8892, -2844, -7962, 7051, 17680], ![576, 168, 550, -474, -1183]]]
  hmulB := by decide  
  f := ![![![4939, 3410, 4030, -2752, -7430]], ![![9912, 7043, 8370, -5704, -15424]], ![![9598, 6803, 8081, -5508, -14892]], ![![3033, 2106, 2492, -1701, -4594]], ![![4095, 2907, 3454, -2354, -6365]]]
  g := ![![![-55, -10, -166, 148, 370], ![-260, -43, -802, 704, 1776], ![-1178, -231, -3541, 3164, 7936], ![-2613, -450, -7962, 7051, 17680], ![173, 15, 550, -474, -1183]]]
  hle1 := by decide   
  hle2 := by decide  


def P349P1 : CertificateIrreducibleZModOfList' 349 2 2 8 [278, 193, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [156, 348], [0, 1]]
 g := ![![[130, 279], [272], [135, 135], [266, 36], [278, 320], [272], [159, 255], [1]], ![[29, 70], [272], [255, 214], [298, 313], [291, 29], [272], [153, 94], [1]]]
 h' := ![![[156, 348], [186, 268], [162, 137], [40, 22], [194, 6], [100, 202], [121, 137], [71, 156], [0, 1]], ![[0, 1], [114, 81], [245, 212], [331, 327], [83, 343], [202, 147], [204, 212], [326, 193], [156, 348]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [269, 180]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI349N1 : CertifiedPrimeIdeal' SI349N1 349 where
  n := 2
  hpos := by decide
  P := [278, 193, 1]
  hirr := P349P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-164878, -52514, -141654, 129874, 324042]
  a := ![-127, -3, -157, 121, 325]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-48922, -12046, -141654, 129874, 324042]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI349N1 : Ideal.IsPrime I349N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI349N1 B_one_repr
lemma NI349N1 : Nat.card (O ⧸ I349N1) = 121801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI349N1
def MulI349N0 : IdealMulLeCertificate' Table 
  ![![4939, 3410, 4030, -2752, -7430]] ![![-185, -62, -166, 148, 370]]
  ![![349, 0, 0, 0, 0]] where
 M := ![![![349, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC349 : ContainsPrimesAboveP 349 ![I349N0, I349N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI349N0
    exact isPrimeI349N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 349 (by decide) (𝕀 ⊙ MulI349N0)
instance hp353 : Fact (Nat.Prime 353) := {out := by norm_num}

def I353N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, -45, 453, -258, -818]] i)))

def SI353N0: IdealEqSpanCertificate' Table ![![199, -45, 453, -258, -818]] 
 ![![353, 0, 0, 0, 0], ![0, 353, 0, 0, 0], ![0, 0, 353, 0, 0], ![0, 0, 0, 353, 0], ![222, 262, 163, 349, 1]] where
  M :=![![![199, -45, 453, -258, -818], ![-528, 350, -1523, 830, 2440], ![-600, -1271, 2040, -886, -1720], ![5892, 571, 6301, -3951, -14456], ![-2616, -769, -1625, 1192, 4997]]]
  hmulB := by decide  
  f := ![![![-73, -47, -55, 38, 102]], ![![-144, -102, -125, 86, 232]], ![![-312, -209, -260, 182, 488]], ![![-276, -173, -233, 169, 448]], ![![-570, -373, -478, 339, 905]]]
  g := ![![![515, 607, 379, 808, -818], ![-1536, -1810, -1131, -2410, 2440], ![1080, 1273, 800, 1698, -1720], ![9108, 10731, 6693, 14281, -14456], ![-3150, -3711, -2312, -4937, 4997]]]
  hle1 := by decide   
  hle2 := by decide  


def P353P0 : CertificateIrreducibleZModOfList' 353 4 2 8 [350, 159, 147, 73, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [315, 308, 271, 285], [268, 352, 102, 257], [50, 45, 333, 164], [0, 1]]
 g := ![![[105, 97, 48, 200], [48, 169, 352], [278, 95, 50], [260, 236, 319], [79, 158, 146], [209, 36, 321, 61], [280, 1], []], ![[75, 351, 237, 243, 332, 244], [112, 227, 109], [50, 77, 36], [343, 76, 98], [175, 278, 76], [28, 24, 154, 54, 247, 315], [52, 60, 254, 218, 237, 172], [339, 125, 35]], ![[229, 17, 269, 202, 220, 301], [144, 80, 256], [272, 292, 232], [287, 222, 292], [241, 246, 58], [42, 218, 182, 22, 70, 178], [137, 183, 160, 80, 259, 268], [283, 234, 38]], ![[308, 73, 70, 188, 24, 21], [172, 249, 8], [290, 83, 196], [51, 16, 213], [119, 62, 171], [131, 47, 72, 91, 198, 171], [57, 295, 251, 72, 79, 92], [275, 125, 68]]]
 h' := ![![[315, 308, 271, 285], [342, 148, 196, 95], [145, 316, 102, 42], [271, 51, 58, 224], [124, 137, 61, 242], [274, 12, 307, 128], [134, 314, 335, 240], [0, 0, 1], [0, 1]], ![[268, 352, 102, 257], [18, 73, 229, 11], [285, 185, 58, 314], [324, 95, 196, 6], [1, 21, 272, 243], [83, 201, 344, 147], [239, 141, 285, 190], [343, 20, 76, 220], [315, 308, 271, 285]], ![[50, 45, 333, 164], [235, 205, 338, 233], [266, 37, 57, 16], [266, 302, 228, 109], [153, 216, 199, 157], [146, 341, 1, 122], [197, 39, 94, 83], [308, 0, 337, 201], [268, 352, 102, 257]], ![[0, 1], [257, 280, 296, 14], [163, 168, 136, 334], [42, 258, 224, 14], [281, 332, 174, 64], [180, 152, 54, 309], [12, 212, 345, 193], [148, 333, 292, 285], [50, 45, 333, 164]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [294, 140, 141], []]
 b := ![[], [], [326, 338, 19, 189], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI353N0 : CertifiedPrimeIdeal' SI353N0 353 where
  n := 4
  hpos := by decide
  P := [350, 159, 147, 73, 1]
  hirr := P353P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8295782350, 5803474514, -23484903080, 12701839106, 37428443060]
  a := ![-85, -9, -108, 65, 218]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-23562068390, -27763310502, -17349351620, -36968342178, 37428443060]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI353N0 : Ideal.IsPrime I353N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI353N0 B_one_repr
lemma NI353N0 : Nat.card (O ⧸ I353N0) = 15527402881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI353N0

def I353N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 47, 55, -38, -102]] i)))

def SI353N1: IdealEqSpanCertificate' Table ![![73, 47, 55, -38, -102]] 
 ![![353, 0, 0, 0, 0], ![47, 1, 0, 0, 0], ![262, 0, 1, 0, 0], ![350, 0, 0, 1, 0], ![281, 0, 0, 0, 1]] where
  M :=![![![73, 47, 55, -38, -102], ![144, 102, 125, -86, -232], ![312, 209, 260, -182, -488], ![276, 173, 233, -169, -448], ![96, 67, 77, -52, -141]]]
  hmulB := by decide  
  f := ![![![-199, 45, -453, 258, 818]], ![![-25, 5, -56, 32, 102]], ![![-146, 37, -342, 194, 612]], ![![-214, 43, -467, 267, 852]], ![![-151, 38, -356, 202, 637]]]
  g := ![![![72, 47, 55, -38, -102], ![164, 102, 125, -86, -232], ![349, 209, 260, -182, -488], ![329, 173, 233, -169, -448], ![98, 67, 77, -52, -141]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI353N1 : Nat.card (O ⧸ I353N1) = 353 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI353N1)

lemma isPrimeI353N1 : Ideal.IsPrime I353N1 := prime_ideal_of_norm_prime hp353.out _ NI353N1
def MulI353N0 : IdealMulLeCertificate' Table 
  ![![199, -45, 453, -258, -818]] ![![73, 47, 55, -38, -102]]
  ![![353, 0, 0, 0, 0]] where
 M := ![![![-353, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I359N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8749, 5865, 6707, -4556, -12300]] i)))

def SI359N0: IdealEqSpanCertificate' Table ![![8749, 5865, 6707, -4556, -12300]] 
 ![![359, 0, 0, 0, 0], ![0, 359, 0, 0, 0], ![0, 0, 359, 0, 0], ![0, 0, 0, 359, 0], ![201, 56, 238, 354, 1]] where
  M :=![![![8749, 5865, 6707, -4556, -12300], ![16416, 12268, 14085, -9378, -25552], ![30984, 23705, 25446, -16406, -45112], ![16428, 15931, 13049, -6801, -20108], ![13260, 8865, 10841, -7542, -20247]]]
  hmulB := by decide  
  f := ![![![-37, 21, -95, 52, 156]], ![![0, -80, 177, -86, -208]], ![![600, 141, 462, -318, -1256]], ![![-1812, 261, -2911, 1697, 5572]], ![![-1407, 350, -2586, 1476, 4709]]]
  g := ![![![6911, 1935, 8173, 12116, -12300], ![14352, 4020, 16979, 25170, -25552], ![25344, 7103, 29978, 44438, -45112], ![11304, 3181, 13367, 19809, -20108], ![11373, 3183, 13453, 19944, -20247]]]
  hle1 := by decide   
  hle2 := by decide  


def P359P0 : CertificateIrreducibleZModOfList' 359 4 2 8 [249, 190, 283, 107, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [295, 171, 87, 99], [0, 144, 239, 42], [316, 43, 33, 218], [0, 1]]
 g := ![![[19, 200, 290, 75], [31, 51, 313, 330], [185, 121, 327, 306], [338, 280, 111], [265, 259, 20], [172, 267, 205, 292], [252, 1], []], ![[160, 177, 274, 260, 47, 300], [128, 237, 133, 297, 27, 82], [293, 141, 222, 104, 105, 111], [114, 352, 340], [181, 208, 202], [27, 53, 352, 230, 278, 246], [130, 207, 258, 292, 190, 72], [113, 285, 108]], ![[153, 24, 96, 138, 297, 61], [170, 162, 209, 28, 56, 280], [69, 26, 218, 95, 214, 161], [33, 87, 243], [277, 153, 237], [251, 21, 322, 43, 135, 57], [216, 251, 225, 89, 15, 63], [343, 58, 328]], ![[312, 14, 25, 112, 135, 325], [165, 74, 51, 151, 100, 179], [82, 111, 169, 242, 265, 93], [182, 89, 128], [133, 69, 110], [350, 104, 294, 35, 4, 171], [83, 284, 156, 3, 232, 130], [333, 195, 136]]]
 h' := ![![[295, 171, 87, 99], [179, 283, 355, 262], [246, 301, 90, 164], [150, 329, 263, 327], [32, 331, 259, 160], [252, 106, 18, 296], [77, 336, 294, 37], [0, 0, 1], [0, 1]], ![[0, 144, 239, 42], [135, 203, 37, 135], [305, 354, 76, 146], [29, 267, 122, 33], [43, 218, 125, 78], [202, 125, 205, 90], [58, 22, 139, 104], [12, 198, 219, 28], [295, 171, 87, 99]], ![[316, 43, 33, 218], [32, 346, 350, 299], [51, 22, 175, 192], [52, 163, 184, 73], [326, 140, 193, 328], [326, 304, 175, 157], [66, 343, 23, 229], [35, 86, 64, 67], [0, 144, 239, 42]], ![[0, 1], [211, 245, 335, 22], [333, 41, 18, 216], [60, 318, 149, 285], [12, 29, 141, 152], [222, 183, 320, 175], [245, 17, 262, 348], [66, 75, 75, 264], [316, 43, 33, 218]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [62, 115, 313], []]
 b := ![[], [], [345, 187, 26, 343], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI359N0 : CertifiedPrimeIdeal' SI359N0 359 where
  n := 4
  hpos := by decide
  P := [249, 190, 283, 107, 1]
  hirr := P359P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-27951615289, -9387790105, -24249011195, 21921484547, 54489752859]
  a := ![92, 5, 113, -85, -235]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-30586049972, -8525944151, -36191671843, -53669780021, 54489752859]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI359N0 : Ideal.IsPrime I359N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI359N0 B_one_repr
lemma NI359N0 : Nat.card (O ⧸ I359N0) = 16610312161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI359N0

def I359N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, -21, 95, -52, -156]] i)))

def SI359N1: IdealEqSpanCertificate' Table ![![37, -21, 95, -52, -156]] 
 ![![359, 0, 0, 0, 0], ![133, 1, 0, 0, 0], ![261, 0, 1, 0, 0], ![168, 0, 0, 1, 0], ![262, 0, 0, 0, 1]] where
  M :=![![![37, -21, 95, -52, -156], ![0, 80, -177, 86, 208], ![-600, -141, -462, 318, 1256], ![1812, -261, 2911, -1697, -5572], ![-972, 43, -1347, 806, 2737]]]
  hmulB := by decide  
  f := ![![![-8749, -5865, -6707, 4556, 12300]], ![![-3287, -2207, -2524, 1714, 4628]], ![![-6447, -4330, -4947, 3358, 9068]], ![![-4140, -2789, -3175, 2151, 5812]], ![![-6422, -4305, -4925, 3346, 9033]]]
  g := ![![![77, -21, 95, -52, -156], ![-93, 80, -177, 86, 208], ![-679, -141, -462, 318, 1256], ![2846, -261, 2911, -1697, -5572], ![-1414, 43, -1347, 806, 2737]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI359N1 : Nat.card (O ⧸ I359N1) = 359 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI359N1)

lemma isPrimeI359N1 : Ideal.IsPrime I359N1 := prime_ideal_of_norm_prime hp359.out _ NI359N1
def MulI359N0 : IdealMulLeCertificate' Table 
  ![![8749, 5865, 6707, -4556, -12300]] ![![37, -21, 95, -52, -156]]
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


lemma PB696I7_primes (p : ℕ) :
  p ∈ Set.range ![311, 313, 317, 331, 337, 347, 349, 353, 359] ↔ Nat.Prime p ∧ 307 < p ∧ p ≤ 359 := by
  rw [← List.mem_ofFn']
  convert primes_range 307 359 (by omega)

def PB696I7 : PrimesBelowBoundCertificateInterval O 307 359 696 where
  m := 9
  g := ![2, 2, 3, 1, 2, 2, 2, 2, 2]
  P := ![311, 313, 317, 331, 337, 347, 349, 353, 359]
  hP := PB696I7_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I311N0, I311N1]
    · exact ![I313N0, I313N1]
    · exact ![I317N0, I317N1, I317N2]
    · exact ![I331N0]
    · exact ![I337N0, I337N1]
    · exact ![I347N0, I347N1]
    · exact ![I349N0, I349N1]
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
    · exact ![30080231, 96721]
    · exact ![30664297, 97969]
    · exact ![31855013, 317, 317]
    · exact ![3973195810651]
    · exact ![38272753, 113569]
    · exact ![14498327281, 347]
    · exact ![42508549, 121801]
    · exact ![15527402881, 353]
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
      exact NI313N1
    · dsimp ; intro j
      fin_cases j
      exact NI317N0
      exact NI317N1
      exact NI317N2
    · dsimp ; intro j
      fin_cases j
      exact NI331N0
    · dsimp ; intro j
      fin_cases j
      exact NI337N0
      exact NI337N1
    · dsimp ; intro j
      fin_cases j
      exact NI347N0
      exact NI347N1
    · dsimp ; intro j
      fin_cases j
      exact NI349N0
      exact NI349N1
    · dsimp ; intro j
      fin_cases j
      exact NI353N0
      exact NI353N1
    · dsimp ; intro j
      fin_cases j
      exact NI359N0
      exact NI359N1
  β := ![I317N1, I317N2, I347N1, I353N1, I359N1]
  Il := ![[], [], [I317N1, I317N2], [], [], [I347N1], [], [I353N1], [I359N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
