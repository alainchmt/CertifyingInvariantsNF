
import IdealArithmetic.Examples.NF5_1_40500000_1.RI5_1_40500000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp367 : Fact (Nat.Prime 367) := {out := by norm_num}

def I367N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![367, 0, 0, 0, 0]] i)))

def SI367N0: IdealEqSpanCertificate' Table ![![367, 0, 0, 0, 0]] 
 ![![367, 0, 0, 0, 0], ![0, 367, 0, 0, 0], ![0, 0, 367, 0, 0], ![0, 0, 0, 367, 0], ![0, 0, 0, 0, 367]] where
  M :=![![![367, 0, 0, 0, 0], ![0, 367, 0, 0, 0], ![0, 0, 367, 0, 0], ![0, 0, 0, 367, 0], ![0, 0, 0, 0, 367]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P367P0 : CertificateIrreducibleZModOfList' 367 5 2 8 [235, 363, 143, 283, 202, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [308, 191, 311, 61, 235], [76, 168, 251, 157, 2], [263, 122, 282, 179, 300], [252, 252, 257, 337, 197], [0, 1]]
 g := ![![[247, 316, 2, 328, 170], [74, 288, 354, 8, 175], [231, 269, 285, 212, 236], [49, 11, 183, 179, 118], [21, 324, 27, 297], [22, 66, 323, 240, 67], [1], []], ![[230, 248, 338, 248, 38, 345, 322, 336], [325, 128, 36, 166, 208, 260, 129, 255], [287, 82, 334, 357, 269, 90, 361, 358], [159, 262, 111, 29, 227, 239, 193, 243], [244, 246, 105, 95], [292, 42, 298, 110, 209, 113, 89, 153], [204, 115, 242, 155, 217, 247, 248, 90], [12, 76, 293, 175]], ![[169, 240, 68, 16, 178, 264, 1, 357], [11, 234, 10, 43, 216, 34, 96, 117], [60, 340, 182, 166, 216, 361, 351, 329], [19, 356, 266, 254, 301, 336, 217, 72], [190, 281, 226, 66], [23, 362, 35, 194, 324, 255, 338, 213], [116, 366, 241, 76, 3, 183, 266, 137], [144, 326, 187, 4]], ![[134, 37, 305, 122, 242, 366, 235, 280], [292, 340, 247, 39, 6, 42, 123, 76], [362, 170, 244, 69, 18, 91, 18, 315], [334, 37, 139, 59, 240, 37, 139, 80], [51, 295, 359, 252], [176, 332, 91, 261, 310, 330, 16, 12], [154, 234, 342, 315, 87, 61, 326, 311], [112, 153, 315, 85]], ![[86, 16, 227, 312, 235, 40, 147, 109], [118, 258, 70, 114, 129, 352, 74, 194], [342, 360, 33, 191, 90, 293, 142, 363], [221, 34, 315, 126, 26, 355, 118, 363], [245, 182, 347, 53], [346, 34, 311, 353, 27, 227, 50, 180], [227, 31, 192, 335, 263, 138, 89, 305], [7, 340, 360, 274]]]
 h' := ![![[308, 191, 311, 61, 235], [226, 4, 219, 106, 212], [31, 59, 227, 209, 132], [229, 275, 77, 296, 128], [126, 235, 118, 180, 82], [335, 167, 73, 124, 60], [132, 4, 224, 84, 165], [0, 0, 1], [0, 1]], ![[76, 168, 251, 157, 2], [167, 273, 35, 246, 206], [93, 203, 218, 341, 335], [62, 281, 304, 39, 101], [362, 77, 225, 323, 322], [84, 22, 286, 88, 241], [245, 153, 94, 246, 62], [294, 20, 347, 135, 4], [308, 191, 311, 61, 235]], ![[263, 122, 282, 179, 300], [302, 52, 95, 308, 27], [91, 254, 219, 127, 232], [255, 301, 199, 36, 240], [308, 220, 318, 278, 361], [223, 253, 363, 149, 112], [40, 132, 298, 80, 335], [195, 148, 207, 86, 282], [76, 168, 251, 157, 2]], ![[252, 252, 257, 337, 197], [256, 110, 243, 175, 301], [336, 178, 89, 72, 264], [58, 79, 133, 214, 310], [177, 235, 268, 306, 14], [61, 21, 298, 236, 282], [8, 295, 19, 245, 147], [277, 39, 20, 23, 84], [263, 122, 282, 179, 300]], ![[0, 1], [108, 295, 142, 266, 355], [90, 40, 348, 352, 138], [23, 165, 21, 149, 322], [131, 334, 172, 14, 322], [247, 271, 81, 137, 39], [273, 150, 99, 79, 25], [203, 160, 159, 123, 364], [252, 252, 257, 337, 197]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [314, 346, 231, 176], [], [], []]
 b := ![[], [131, 93, 172, 154, 246], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI367N0 : CertifiedPrimeIdeal' SI367N0 367 where
  n := 5
  hpos := by decide
  P := [235, 363, 143, 283, 202, 1]
  hirr := P367P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-811807303, 1133984859, -297570573, 967993328, -176554892]
  a := ![-11, -7, 13, -19, -44]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2212009, 3089877, -810819, 2637584, -481076]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI367N0 : Ideal.IsPrime I367N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI367N0 B_one_repr
lemma NI367N0 : Nat.card (O ⧸ I367N0) = 6657793506607 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI367N0

def PBC367 : ContainsPrimesAboveP 367 ![I367N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI367N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![367, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 367 (by decide) 𝕀

instance hp373 : Fact (Nat.Prime 373) := {out := by norm_num}

def I373N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-62, -19, 8, -26, -37]] i)))

def SI373N0: IdealEqSpanCertificate' Table ![![-62, -19, 8, -26, -37]] 
 ![![373, 0, 0, 0, 0], ![0, 373, 0, 0, 0], ![285, 227, 1, 0, 0], ![58, 210, 0, 1, 0], ![204, 23, 0, 0, 1]] where
  M :=![![![-62, -19, 8, -26, -37], ![-163, -48, 22, -72, -97], ![-435, -125, 71, -190, -285], ![-42, -3, 5, -7, -18], ![-120, -38, 20, -54, -79]]]
  hmulB := by decide  
  f := ![![![8, -11, 8, -18, -15]], ![![-81, 30, 28, -4, -99]], ![![-44, 10, 23, -16, -71]], ![![-44, 15, 17, -5, -58]], ![![-1, -4, 6, -10, -14]]]
  g := ![![![18, 12, 8, -26, -37], ![47, 33, 22, -72, -97], ![130, 81, 71, -190, -285], ![7, 2, 5, -7, -18], ![36, 23, 20, -54, -79]]]
  hle1 := by decide   
  hle2 := by decide  


def P373P0 : CertificateIrreducibleZModOfList' 373 2 2 8 [132, 95, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [278, 372], [0, 1]]
 g := ![![[207, 256], [343], [71, 235], [55], [350, 265], [363, 280], [241, 73], [1]], ![[132, 117], [343], [126, 138], [55], [166, 108], [246, 93], [20, 300], [1]]]
 h' := ![![[278, 372], [201, 357], [326, 340], [293, 261], [52, 146], [201, 57], [266, 186], [241, 278], [0, 1]], ![[0, 1], [229, 16], [104, 33], [116, 112], [356, 227], [8, 316], [127, 187], [314, 95], [278, 372]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [182]]
 b := ![[], [33, 91]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI373N0 : CertifiedPrimeIdeal' SI373N0 373 where
  n := 2
  hpos := by decide
  P := [132, 95, 1]
  hirr := P373P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![41833, 10246, 7669, -3970, -32477]
  a := ![-49, -56, 48, -106, -199]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![12632, -402, 7669, -3970, -32477]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI373N0 : Ideal.IsPrime I373N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI373N0 B_one_repr
lemma NI373N0 : Nat.card (O ⧸ I373N0) = 139129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI373N0

def I373N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![62, -6, -1, -32, -15]] i)))

def SI373N1: IdealEqSpanCertificate' Table ![![62, -6, -1, -32, -15]] 
 ![![373, 0, 0, 0, 0], ![90, 1, 0, 0, 0], ![106, 0, 1, 0, 0], ![120, 0, 0, 1, 0], ![219, 0, 0, 0, 1]] where
  M :=![![![62, -6, -1, -32, -15], ![-109, 25, 75, -136, -211], ![-905, 130, 222, -80, -455], ![-98, 0, -46, 175, 178], ![-194, 28, 48, -18, -99]]]
  hmulB := by decide  
  f := ![![![-3312, -794, 355, -1230, -1649]], ![![-819, -199, 89, -306, -411]], ![![-999, -238, 108, -370, -503]], ![![-1070, -256, 114, -397, -530]], ![![-1960, -470, 211, -728, -980]]]
  g := ![![![21, -6, -1, -32, -15], ![140, 25, 75, -136, -211], ![196, 130, 222, -80, -455], ![-148, 0, -46, 175, 178], ![43, 28, 48, -18, -99]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI373N1 : Nat.card (O ⧸ I373N1) = 373 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI373N1)

lemma isPrimeI373N1 : Ideal.IsPrime I373N1 := prime_ideal_of_norm_prime hp373.out _ NI373N1

def I373N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, 4, 0, 2, -4]] i)))

def SI373N2: IdealEqSpanCertificate' Table ![![-3, 4, 0, 2, -4]] 
 ![![373, 0, 0, 0, 0], ![191, 1, 0, 0, 0], ![73, 0, 1, 0, 0], ![226, 0, 0, 1, 0], ![25, 0, 0, 0, 1]] where
  M :=![![![-3, 4, 0, 2, -4], ![-8, -1, -6, -2, 28], ![80, -40, 33, -10, -100], ![-28, 24, -8, 11, 8], ![48, -32, 16, -12, -35]]]
  hmulB := by decide  
  f := ![![![529, 52, -120, 210, 372]], ![![275, 27, -62, 108, 192]], ![![109, 12, -23, 40, 72]], ![![318, 32, -72, 127, 224]], ![![37, 4, -8, 14, 25]]]
  g := ![![![-3, 4, 0, 2, -4], ![1, -1, -6, -2, 28], ![27, -40, 33, -10, -100], ![-18, 24, -8, 11, 8], ![23, -32, 16, -12, -35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI373N2 : Nat.card (O ⧸ I373N2) = 373 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI373N2)

lemma isPrimeI373N2 : Ideal.IsPrime I373N2 := prime_ideal_of_norm_prime hp373.out _ NI373N2

def I373N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-41, -11, 5, -16, -22]] i)))

def SI373N3: IdealEqSpanCertificate' Table ![![-41, -11, 5, -16, -22]] 
 ![![373, 0, 0, 0, 0], ![238, 1, 0, 0, 0], ![52, 0, 1, 0, 0], ![210, 0, 0, 1, 0], ![98, 0, 0, 0, 1]] where
  M :=![![![-41, -11, 5, -16, -22], ![-98, -32, 15, -42, -62], ![-270, -65, 32, -100, -150], ![-16, -5, 1, -7, -4], ![-76, -18, 10, -28, -47]]]
  hmulB := by decide  
  f := ![![![-93, 1, -75, 230, 262]], ![![-56, 0, -49, 148, 170]], ![![-2, -1, -12, 30, 38]], ![![-54, 1, -41, 127, 144]], ![![-22, 0, -20, 60, 69]]]
  g := ![![![21, -11, 5, -16, -22], ![58, -32, 15, -42, -62], ![132, -65, 32, -100, -150], ![8, -5, 1, -7, -4], ![38, -18, 10, -28, -47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI373N3 : Nat.card (O ⧸ I373N3) = 373 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI373N3)

lemma isPrimeI373N3 : Ideal.IsPrime I373N3 := prime_ideal_of_norm_prime hp373.out _ NI373N3
def MulI373N0 : IdealMulLeCertificate' Table 
  ![![-62, -19, 8, -26, -37]] ![![62, -6, -1, -32, -15]]
  ![![713, -99, -167, 44, 334]] where
 M := ![![![713, -99, -167, 44, 334]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI373N1 : IdealMulLeCertificate' Table 
  ![![713, -99, -167, 44, 334]] ![![-3, 4, 0, 2, -4]]
  ![![93, -1, 75, -230, -262]] where
 M := ![![![93, -1, 75, -230, -262]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI373N2 : IdealMulLeCertificate' Table 
  ![![93, -1, 75, -230, -262]] ![![-41, -11, 5, -16, -22]]
  ![![373, 0, 0, 0, 0]] where
 M := ![![![-373, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC373 : ContainsPrimesAboveP 373 ![I373N0, I373N1, I373N2, I373N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI373N0
    exact isPrimeI373N1
    exact isPrimeI373N2
    exact isPrimeI373N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 373 (by decide) (𝕀 ⊙ MulI373N0 ⊙ MulI373N1 ⊙ MulI373N2)
instance hp379 : Fact (Nat.Prime 379) := {out := by norm_num}

def I379N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2587, -737, 325, -1040, -1404]] i)))

def SI379N0: IdealEqSpanCertificate' Table ![![-2587, -737, 325, -1040, -1404]] 
 ![![379, 0, 0, 0, 0], ![0, 379, 0, 0, 0], ![0, 0, 379, 0, 0], ![0, 0, 0, 379, 0], ![251, 166, 277, 99, 1]] where
  M :=![![![-2587, -737, 325, -1040, -1404], ![-6292, -2002, 979, -2678, -4108], ![-17680, -4075, 1924, -6460, -9100], ![-876, -451, 131, -495, -384], ![-5136, -1014, 550, -1760, -2755]]]
  hmulB := by decide  
  f := ![![![-37, 5, 7, 2, -12]], ![![-32, 0, -13, 52, 52]], ![![260, -45, -104, 130, 260]], ![![120, -13, -11, -39, 0]], ![![183, -33, -80, 109, 205]]]
  g := ![![![923, 613, 1027, 364, -1404], ![2704, 1794, 3005, 1066, -4108], ![5980, 3975, 6656, 2360, -9100], ![252, 167, 281, 99, -384], ![1811, 1204, 2015, 715, -2755]]]
  hle1 := by decide   
  hle2 := by decide  


def P379P0 : CertificateIrreducibleZModOfList' 379 4 2 8 [194, 286, 326, 266, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [143, 15, 95, 271], [290, 9, 286, 158], [59, 354, 377, 329], [0, 1]]
 g := ![![[263, 250, 323, 19], [14, 110, 304, 94], [174, 331, 218], [183, 261, 178, 173], [262, 226, 36, 4], [107, 206, 59, 306], [113, 1], []], ![[341, 278, 154, 307, 334, 305], [152, 136, 234, 295, 122, 352], [51, 236, 376], [116, 107, 50, 197, 368, 270], [91, 89, 229, 317, 347, 234], [377, 365, 242, 353, 47, 351], [70, 232, 27, 157, 365, 307], [196, 195, 294]], ![[79, 255, 174, 374, 351, 357], [109, 47, 367, 185, 212, 272], [62, 9, 301], [296, 249, 193, 183, 220, 133], [139, 185, 19, 20, 133, 241], [48, 287, 2, 321, 157, 73], [129, 247, 75, 274, 26, 15], [245, 209, 329]], ![[45, 72, 197, 110, 35, 350], [367, 67, 249, 20, 292, 120], [374, 332, 313], [193, 295, 43, 61, 281, 164], [63, 311, 221, 116, 199, 216], [225, 99, 308, 45, 275, 146], [263, 170, 260, 356, 339, 64], [28, 345, 226]]]
 h' := ![![[143, 15, 95, 271], [316, 146, 263, 34], [191, 171, 240, 138], [124, 364, 373, 225], [337, 219, 145, 141], [87, 117, 104, 377], [60, 82, 18, 315], [0, 0, 1], [0, 1]], ![[290, 9, 286, 158], [210, 156, 156, 96], [55, 254, 16, 189], [190, 363, 299, 103], [88, 280, 284, 313], [70, 79, 347, 151], [168, 87, 169, 82], [238, 227, 19, 330], [143, 15, 95, 271]], ![[59, 354, 377, 329], [119, 305, 356, 194], [248, 363, 24, 37], [155, 53, 259, 148], [290, 255, 298, 223], [18, 283, 345, 258], [319, 331, 348, 298], [186, 345, 12, 145], [290, 9, 286, 158]], ![[0, 1], [122, 151, 362, 55], [157, 349, 99, 15], [361, 357, 206, 282], [82, 4, 31, 81], [305, 279, 341, 351], [215, 258, 223, 63], [323, 186, 347, 283], [59, 354, 377, 329]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [325, 48, 111], []]
 b := ![[], [], [372, 71, 161, 184], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI379N0 : CertifiedPrimeIdeal' SI379N0 379 where
  n := 4
  hpos := by decide
  P := [194, 286, 326, 266, 1]
  hirr := P379P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1355313, -140698, 717730, -241419, -2120348]
  a := ![-4, -4, 5, -9, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1400665, 928330, 1551594, 553227, -2120348]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI379N0 : Ideal.IsPrime I379N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI379N0 B_one_repr
lemma NI379N0 : Nat.card (O ⧸ I379N0) = 20632736881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI379N0

def I379N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-37, 5, 7, 2, -12]] i)))

def SI379N1: IdealEqSpanCertificate' Table ![![-37, 5, 7, 2, -12]] 
 ![![379, 0, 0, 0, 0], ![348, 1, 0, 0, 0], ![176, 0, 1, 0, 0], ![220, 0, 0, 1, 0], ![319, 0, 0, 0, 1]] where
  M :=![![![-37, 5, 7, 2, -12], ![-32, 0, -13, 52, 52], ![260, -45, -104, 130, 260], ![120, -13, -11, -39, 0], ![56, -10, -22, 28, 55]]]
  hmulB := by decide  
  f := ![![![-2587, -737, 325, -1040, -1404]], ![![-2392, -682, 301, -962, -1300]], ![![-1248, -353, 156, -500, -676]], ![![-1504, -429, 189, -605, -816]], ![![-2191, -623, 275, -880, -1189]]]
  g := ![![![1, 5, 7, 2, -12], ![-68, 0, -13, 52, 52], ![-204, -45, -104, 130, 260], ![40, -13, -11, -39, 0], ![-43, -10, -22, 28, 55]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI379N1 : Nat.card (O ⧸ I379N1) = 379 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI379N1)

lemma isPrimeI379N1 : Ideal.IsPrime I379N1 := prime_ideal_of_norm_prime hp379.out _ NI379N1
def MulI379N0 : IdealMulLeCertificate' Table 
  ![![-2587, -737, 325, -1040, -1404]] ![![-37, 5, 7, 2, -12]]
  ![![379, 0, 0, 0, 0]] where
 M := ![![![379, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC379 : ContainsPrimesAboveP 379 ![I379N0, I379N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI379N0
    exact isPrimeI379N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 379 (by decide) (𝕀 ⊙ MulI379N0)
instance hp383 : Fact (Nat.Prime 383) := {out := by norm_num}

def I383N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1899, -282, -502, 274, 1072]] i)))

def SI383N0: IdealEqSpanCertificate' Table ![![1899, -282, -502, 274, 1072]] 
 ![![383, 0, 0, 0, 0], ![0, 383, 0, 0, 0], ![146, 60, 1, 0, 0], ![273, 153, 0, 1, 0], ![368, 336, 0, 0, 1]] where
  M :=![![![1899, -282, -502, 274, 1072], ![3764, -337, -32, -2054, -1024], ![-7180, 1550, 4801, -8530, -13360], ![-7596, 998, 1394, 597, -2304], ![-1504, 316, 1020, -1844, -2825]]]
  hmulB := by decide  
  f := ![![![-47525803, -13622274, 6387906, -19194650, -27651824]], ![![-121344772, -34780923, 16309852, -49008538, -70601728]], ![![-37935446, -10873398, 5098873, -15321310, -22071888]], ![![-82398765, -23617873, 11075152, -33279087, -47941872]], ![![-152348416, -43667468, 20477028, -61530244, -88640505]]]
  g := ![![![-1029, -972, -502, 274, 1072], ![2470, 1723, -32, -2054, -1024], ![17068, 14380, 4801, -8530, -13360], ![1237, 1567, 1394, 597, -2304], ![3636, 3056, 1020, -1844, -2825]]]
  hle1 := by decide   
  hle2 := by decide  


def P383P0 : CertificateIrreducibleZModOfList' 383 2 2 8 [4, 350, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 382], [0, 1]]
 g := ![![[279, 96], [52, 204], [101, 147], [50, 261], [38, 313], [309, 192], [54, 323], [1]], ![[0, 287], [273, 179], [356, 236], [237, 122], [26, 70], [134, 191], [372, 60], [1]]]
 h' := ![![[33, 382], [175, 192], [362, 232], [183, 347], [231, 294], [296, 167], [167, 123], [379, 33], [0, 1]], ![[0, 1], [0, 191], [358, 151], [144, 36], [358, 89], [62, 216], [13, 260], [319, 350], [33, 382]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [121]]
 b := ![[], [55, 252]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI383N0 : CertifiedPrimeIdeal' SI383N0 383 where
  n := 2
  hpos := by decide
  P := [4, 350, 1]
  hirr := P383P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![16795, 15696, -9349, 23662, 34200]
  a := ![36, 27, -39, 62, 143]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-46119, -37950, -9349, 23662, 34200]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI383N0 : Ideal.IsPrime I383N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI383N0 B_one_repr
lemma NI383N0 : Nat.card (O ⧸ I383N0) = 146689 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI383N0

def I383N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5538, 1587, -744, 2236, 3221]] i)))

def SI383N1: IdealEqSpanCertificate' Table ![![5538, 1587, -744, 2236, 3221]] 
 ![![383, 0, 0, 0, 0], ![0, 383, 0, 0, 0], ![62, 102, 1, 0, 0], ![57, 77, 0, 1, 0], ![315, 136, 0, 0, 1]] where
  M :=![![![5538, 1587, -744, 2236, 3221], ![14135, 4054, -1900, 5710, 8225], ![36095, 10345, -4851, 14580, 21005], ![2150, 615, -289, 869, 1250], ![10264, 2942, -1380, 4146, 5975]]]
  hmulB := by decide  
  f := ![![![140, -31, -8, -8, -3]], ![![-25, 92, -10, -110, -55]], ![![15, 19, -3, -32, -17]], ![![15, 14, -3, -23, -12]], ![![106, 7, -10, -46, -22]]]
  g := ![![![-2847, -1391, -744, 2236, 3221], ![-7270, -3552, -1900, 5710, 8225], ![-18566, -9071, -4851, 14580, 21005], ![-1105, -540, -289, 869, 1250], ![-5281, -2580, -1380, 4146, 5975]]]
  hle1 := by decide   
  hle2 := by decide  


def P383P1 : CertificateIrreducibleZModOfList' 383 2 2 8 [222, 145, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [238, 382], [0, 1]]
 g := ![![[168, 261], [373, 16], [44, 73], [101, 72], [130, 28], [348, 69], [91, 343], [1]], ![[240, 122], [351, 367], [183, 310], [2, 311], [283, 355], [301, 314], [146, 40], [1]]]
 h' := ![![[238, 382], [305, 294], [190, 379], [175, 235], [248, 56], [110, 315], [97, 158], [161, 238], [0, 1]], ![[0, 1], [188, 89], [4, 4], [187, 148], [171, 327], [12, 68], [167, 225], [121, 145], [238, 382]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [279]]
 b := ![[], [60, 331]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI383N1 : CertifiedPrimeIdeal' SI383N1 383 where
  n := 2
  hpos := by decide
  P := [222, 145, 1]
  hirr := P383P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4301, -293, 5586, -2756, -18461]
  a := ![-21, -9, 26, -28, -83]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![14678, 5621, 5586, -2756, -18461]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI383N1 : Ideal.IsPrime I383N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI383N1 B_one_repr
lemma NI383N1 : Nat.card (O ⧸ I383N1) = 146689 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI383N1

def I383N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4104, -1177, 552, -1658, -2389]] i)))

def SI383N2: IdealEqSpanCertificate' Table ![![-4104, -1177, 552, -1658, -2389]] 
 ![![383, 0, 0, 0, 0], ![221, 1, 0, 0, 0], ![183, 0, 1, 0, 0], ![288, 0, 0, 1, 0], ![116, 0, 0, 0, 1]] where
  M :=![![![-4104, -1177, 552, -1658, -2389], ![-10483, -3002, 1408, -4232, -6097], ![-26755, -7675, 3597, -10810, -15565], ![-1590, -457, 215, -643, -930], ![-7610, -2182, 1022, -3074, -4423]]]
  hmulB := by decide  
  f := ![![![3010, -371, -400, -598, 419]], ![![1737, -213, -226, -358, 226]], ![![1365, -166, -167, -308, 144]], ![![2242, -277, -301, -437, 322]], ![![896, -110, -116, -186, 115]]]
  g := ![![![2375, -1177, 552, -1658, -2389], ![6061, -3002, 1408, -4232, -6097], ![15483, -7675, 3597, -10810, -15565], ![922, -457, 215, -643, -930], ![4402, -2182, 1022, -3074, -4423]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI383N2 : Nat.card (O ⧸ I383N2) = 383 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI383N2)

lemma isPrimeI383N2 : Ideal.IsPrime I383N2 := prime_ideal_of_norm_prime hp383.out _ NI383N2
def MulI383N0 : IdealMulLeCertificate' Table 
  ![![1899, -282, -502, 274, 1072]] ![![5538, 1587, -744, 2236, 3221]]
  ![![3010, -371, -400, -598, 419]] where
 M := ![![![3010, -371, -400, -598, 419]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI383N1 : IdealMulLeCertificate' Table 
  ![![3010, -371, -400, -598, 419]] ![![-4104, -1177, 552, -1658, -2389]]
  ![![383, 0, 0, 0, 0]] where
 M := ![![![383, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC383 : ContainsPrimesAboveP 383 ![I383N0, I383N1, I383N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI383N0
    exact isPrimeI383N1
    exact isPrimeI383N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 383 (by decide) (𝕀 ⊙ MulI383N0 ⊙ MulI383N1)
instance hp389 : Fact (Nat.Prime 389) := {out := by norm_num}

def I389N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-78301, 14354, 35036, -48454, -90600]] i)))

def SI389N0: IdealEqSpanCertificate' Table ![![-78301, 14354, 35036, -48454, -90600]] 
 ![![389, 0, 0, 0, 0], ![0, 389, 0, 0, 0], ![0, 0, 389, 0, 0], ![0, 0, 0, 389, 0], ![18, 41, 232, 299, 1]] where
  M :=![![![-78301, 14354, 35036, -48454, -90600], ![-368708, 48425, 69116, 23798, -115832], ![-299900, 670, -138801, 530890, 537880], ![451896, -70514, -139970, 116143, 321264], ![-66750, 576, -29170, 113576, 114029]]]
  hmulB := by decide  
  f := ![![![-11968289, -3430458, 1608648, -4833734, -6963480]], ![![-30557908, -8758783, 4107264, -12341682, -17779432]], ![![-78021660, -22363270, 10486831, -31511270, -45395160]], ![![-4641848, -1330486, 623906, -1874741, -2700752]], ![![-53931692, -15458385, 7248916, -21781849, -31378947]]]
  g := ![![![3991, 9586, 54124, 69514, -90600], ![4412, 12333, 69260, 89094, -115832], ![-25660, -56690, -321149, -412070, 537880], ![-13704, -34042, -191962, -246637, 321264], ![-5448, -12017, -68082, -87355, 114029]]]
  hle1 := by decide   
  hle2 := by decide  


def P389P0 : CertificateIrreducibleZModOfList' 389 4 2 8 [22, 304, 156, 356, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [229, 254, 303, 86], [0, 127, 71, 144], [193, 7, 15, 159], [0, 1]]
 g := ![![[78, 340, 150, 220], [18, 6, 302], [277, 360, 313, 277], [300, 293, 303], [247, 321, 187], [24, 332, 370], [155, 33, 1], []], ![[79, 60, 174, 100, 205, 340], [27, 370, 129], [386, 184, 196, 375, 111, 78], [229, 171, 220], [340, 284, 256], [21, 247, 331], [167, 137, 268], [298, 197, 99, 5, 63, 41]], ![[115, 313, 89, 377, 90, 122], [190, 101, 323], [42, 74, 42, 200, 289, 196], [93, 19, 323], [83, 70, 345], [62, 44, 298], [196, 261, 179], [39, 191, 314, 5, 333, 20]], ![[50, 226, 204, 323, 117, 287], [80, 358, 276], [380, 370, 295, 319, 98, 121], [285, 242, 236], [241, 6, 383], [91, 322, 159], [243, 133, 20], [352, 80, 21, 387, 227, 142]]]
 h' := ![![[229, 254, 303, 86], [166, 360, 31, 61], [130, 388, 232, 334], [215, 263, 239, 351], [352, 112, 306, 260], [362, 364, 24, 24], [91, 1, 387, 52], [0, 0, 0, 1], [0, 1]], ![[0, 127, 71, 144], [281, 55, 315, 184], [252, 305, 81, 353], [83, 131, 10, 244], [381, 98, 310, 328], [380, 86, 377, 16], [8, 355, 77, 254], [227, 7, 229, 291], [229, 254, 303, 86]], ![[193, 7, 15, 159], [20, 81, 10, 192], [243, 150, 267, 174], [175, 120, 250, 323], [306, 267, 120, 215], [24, 150, 97, 68], [143, 350, 376, 197], [309, 280, 131, 314], [0, 127, 71, 144]], ![[0, 1], [198, 282, 33, 341], [205, 324, 198, 306], [348, 264, 279, 249], [86, 301, 42, 364], [254, 178, 280, 281], [356, 72, 327, 275], [373, 102, 29, 172], [193, 7, 15, 159]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [336, 247, 309], []]
 b := ![[], [], [23, 295, 218, 87], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI389N0 : CertifiedPrimeIdeal' SI389N0 389 where
  n := 4
  hpos := by decide
  P := [22, 304, 156, 356, 1]
  hirr := P389P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![182512150, -179440576, 29545024, -73457408, 60160512]
  a := ![12, -4, -14, -2, 48]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2314594, -6802112, -35803840, -46430464, 60160512]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI389N0 : Ideal.IsPrime I389N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI389N0 B_one_repr
lemma NI389N0 : Nat.card (O ⧸ I389N0) = 22898045041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI389N0

def I389N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11968289, -3430458, 1608648, -4833734, -6963480]] i)))

def SI389N1: IdealEqSpanCertificate' Table ![![-11968289, -3430458, 1608648, -4833734, -6963480]] 
 ![![389, 0, 0, 0, 0], ![334, 1, 0, 0, 0], ![87, 0, 1, 0, 0], ![117, 0, 0, 1, 0], ![314, 0, 0, 0, 1]] where
  M :=![![![-11968289, -3430458, 1608648, -4833734, -6963480], ![-30557908, -8758783, 4107264, -12341682, -17779432], ![-78021660, -22363270, 10486831, -31511270, -45395160], ![-4641848, -1330486, 623906, -1874741, -2700752], ![-22187086, -6359464, 2982150, -8960888, -12909063]]]
  hmulB := by decide  
  f := ![![![-78301, 14354, 35036, -48454, -90600]], ![![-68178, 12449, 30260, -41542, -78088]], ![![-18283, 3212, 7479, -9472, -18880]], ![![-22389, 4136, 10178, -14275, -26424]], ![![-63376, 11588, 28206, -38820, -72839]]]
  g := ![![![9629645, -3430458, 1608648, -4833734, -6963480], ![24586792, -8758783, 4107264, -12341682, -17779432], ![62775977, -22363270, 10486831, -31511270, -45395160], ![3734811, -1330486, 623906, -1874741, -2700752], ![17851662, -6359464, 2982150, -8960888, -12909063]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI389N1 : Nat.card (O ⧸ I389N1) = 389 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI389N1)

lemma isPrimeI389N1 : Ideal.IsPrime I389N1 := prime_ideal_of_norm_prime hp389.out _ NI389N1
def MulI389N0 : IdealMulLeCertificate' Table 
  ![![-78301, 14354, 35036, -48454, -90600]] ![![-11968289, -3430458, 1608648, -4833734, -6963480]]
  ![![389, 0, 0, 0, 0]] where
 M := ![![![389, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC389 : ContainsPrimesAboveP 389 ![I389N0, I389N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI389N0
    exact isPrimeI389N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 389 (by decide) (𝕀 ⊙ MulI389N0)


lemma PB397I8_primes (p : ℕ) :
  p ∈ Set.range ![367, 373, 379, 383, 389] ↔ Nat.Prime p ∧ 359 < p ∧ p ≤ 396 := by
  rw [← List.mem_ofFn']
  convert primes_range 359 396 (by omega)

def PB397I8 : PrimesBelowBoundCertificateInterval O 359 396 397 where
  m := 5
  g := ![1, 4, 2, 3, 2]
  P := ![367, 373, 379, 383, 389]
  hP := PB397I8_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I367N0]
    · exact ![I373N0, I373N1, I373N2, I373N3]
    · exact ![I379N0, I379N1]
    · exact ![I383N0, I383N1, I383N2]
    · exact ![I389N0, I389N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC367
    · exact PBC373
    · exact PBC379
    · exact PBC383
    · exact PBC389
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![6657793506607]
    · exact ![139129, 373, 373, 373]
    · exact ![20632736881, 379]
    · exact ![146689, 146689, 383]
    · exact ![22898045041, 389]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI367N0
    · dsimp ; intro j
      fin_cases j
      exact NI373N0
      exact NI373N1
      exact NI373N2
      exact NI373N3
    · dsimp ; intro j
      fin_cases j
      exact NI379N0
      exact NI379N1
    · dsimp ; intro j
      fin_cases j
      exact NI383N0
      exact NI383N1
      exact NI383N2
    · dsimp ; intro j
      fin_cases j
      exact NI389N0
      exact NI389N1
  β := ![I373N1, I373N2, I373N3, I379N1, I383N2, I389N1]
  Il := ![[], [I373N1, I373N2, I373N3], [I379N1], [I383N2], [I389N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
