
import IdealArithmetic.Examples.NF5_3_480000000_1.RI5_3_480000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp467 : Fact (Nat.Prime 467) := {out := by norm_num}

def I467N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![108337, -331118, -555206, 2339, 141307]] i)))

def SI467N0: IdealEqSpanCertificate' Table ![![108337, -331118, -555206, 2339, 141307]] 
 ![![467, 0, 0, 0, 0], ![0, 467, 0, 0, 0], ![0, 0, 467, 0, 0], ![0, 0, 0, 467, 0], ![455, 41, 31, 207, 1]] where
  M :=![![![108337, -331118, -555206, 2339, 141307], ![1130456, 257327, -666914, -123602, 148324], ![593296, 664382, 380929, -85979, -111241], ![-1010192, 123336, 1083818, 96376, -258751], ![-254384, 130974, 410894, 20273, -100844]]]
  hmulB := by decide  
  f := ![![![-1693, -336, -502, -763, -355]], ![![-2840, -3207, 854, -2726, -2644]], ![![-10576, -6240, -481, -7037, -5411]], ![![-20224, -13934, 370, -14538, -11939]], ![![-11665, -7267, -281, -7965, -6287]]]
  g := ![![![-137444, -13115, -10569, -62630, 141307], ![-142092, -12471, -11274, -66010, 148324], ![109653, 11189, 8200, 49124, -111241], ![249939, 22981, 19497, 114899, -258751], ![97708, 9134, 7574, 44743, -100844]]]
  hle1 := by decide   
  hle2 := by decide  


def P467P0 : CertificateIrreducibleZModOfList' 467 4 2 8 [206, 238, 215, 463, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [378, 211, 83, 246], [343, 233, 138, 448], [217, 22, 246, 240], [0, 1]]
 g := ![![[243, 435, 381, 108], [158, 159, 71, 134], [52, 113, 371], [63, 287, 206], [363, 14, 276, 10], [262, 399, 199], [441, 268, 4, 1], []], ![[244, 30, 445, 316, 115, 85], [242, 117, 240, 33, 250, 98], [343, 270, 381], [257, 429, 389], [247, 260, 65, 249, 165, 316], [189, 450, 456], [455, 164, 294, 122, 129, 205], [317, 61, 70, 150, 369, 377]], ![[138, 208, 387, 226, 112, 280], [186, 391, 435, 191, 159, 12], [377, 184, 122], [465, 279, 225], [83, 258, 328, 412, 318, 156], [73, 202, 267], [27, 420, 419, 314, 400, 436], [427, 161, 186, 382, 131, 146]], ![[454, 312, 192, 237, 94, 442], [78, 273, 209, 308, 297, 278], [107, 145, 252], [124, 445, 52], [217, 170, 71, 143, 309, 403], [187, 418, 250], [135, 115, 338, 465, 143, 307], [438, 138, 45, 253, 56, 333]]]
 h' := ![![[378, 211, 83, 246], [142, 345, 154, 62], [385, 406, 207, 185], [193, 91, 237, 71], [409, 250, 351, 109], [60, 252, 310, 145], [219, 15, 291, 427], [0, 0, 0, 1], [0, 1]], ![[343, 233, 138, 448], [132, 414, 321, 296], [95, 147, 117, 184], [161, 141, 128, 349], [183, 423, 20, 217], [411, 254, 230, 457], [233, 296, 292, 108], [279, 65, 142, 120], [378, 211, 83, 246]], ![[217, 22, 246, 240], [297, 399, 177, 153], [216, 290, 419, 453], [274, 455, 85, 196], [80, 362, 441, 452], [300, 31, 276, 309], [366, 265, 401, 141], [438, 457, 42, 379], [343, 233, 138, 448]], ![[0, 1], [282, 243, 282, 423], [106, 91, 191, 112], [427, 247, 17, 318], [67, 366, 122, 156], [146, 397, 118, 23], [438, 358, 417, 258], [256, 412, 283, 434], [217, 22, 246, 240]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [357, 39, 259], []]
 b := ![[], [], [401, 39, 216, 284], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI467N0 : CertifiedPrimeIdeal' SI467N0 467 where
  n := 4
  hpos := by decide
  P := [206, 238, 215, 463, 1]
  hirr := P467P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-39965434, -32457255, 11709158, -12491426, -84501584]
  a := ![0, 1, 1, 0, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![82244658, 7349267, 5634386, 37428986, -84501584]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI467N0 : Ideal.IsPrime I467N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI467N0 B_one_repr
lemma NI467N0 : Nat.card (O ⧸ I467N0) = 47562811921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI467N0

def I467N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1693, 336, 502, 763, 355]] i)))

def SI467N1: IdealEqSpanCertificate' Table ![![1693, 336, 502, 763, 355]] 
 ![![467, 0, 0, 0, 0], ![312, 1, 0, 0, 0], ![363, 0, 1, 0, 0], ![190, 0, 0, 1, 0], ![419, 0, 0, 0, 1]] where
  M :=![![![1693, 336, 502, 763, 355], ![2840, 3207, -854, 2726, 2644], ![10576, 6240, 481, 7037, 5411], ![20224, 13934, -370, 14538, 11939], ![46576, 31544, -490, 33211, 26986]]]
  hmulB := by decide  
  f := ![![![-108337, 331118, 555206, -2339, -141307]], ![![-74800, 220667, 372358, -1298, -94724]], ![![-85481, 255956, 430747, -1634, -109600]], ![![-41914, 134452, 223566, -1158, -56937]], ![![-96657, 296804, 497260, -2142, -126567]]]
  g := ![![![-1240, 336, 502, 763, 355], ![-4954, 3207, -854, 2726, 2644], ![-12238, 6240, 481, 7037, 5411], ![-25605, 13934, -370, 14538, 11939], ![-58318, 31544, -490, 33211, 26986]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI467N1 : Nat.card (O ⧸ I467N1) = 467 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI467N1)

lemma isPrimeI467N1 : Ideal.IsPrime I467N1 := prime_ideal_of_norm_prime hp467.out _ NI467N1
def MulI467N0 : IdealMulLeCertificate' Table 
  ![![108337, -331118, -555206, 2339, 141307]] ![![1693, 336, 502, 763, 355]]
  ![![467, 0, 0, 0, 0]] where
 M := ![![![-467, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC467 : ContainsPrimesAboveP 467 ![I467N0, I467N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI467N0
    exact isPrimeI467N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 467 (by decide) (𝕀 ⊙ MulI467N0)
instance hp479 : Fact (Nat.Prime 479) := {out := by norm_num}

def I479N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4839, -1391, 2942, 891, -797]] i)))

def SI479N0: IdealEqSpanCertificate' Table ![![4839, -1391, 2942, 891, -797]] 
 ![![479, 0, 0, 0, 0], ![0, 479, 0, 0, 0], ![0, 0, 479, 0, 0], ![420, 441, 401, 1, 0], ![425, 41, 203, 0, 1]] where
  M :=![![![4839, -1391, 2942, 891, -797], ![-6376, 2905, -4564, -586, 1876], ![7504, -487, 3491, 2295, 59], ![3424, 3045, -500, 2843, 2534], ![10776, 5909, 774, 6914, 5197]]]
  hmulB := by decide  
  f := ![![![969, 681, 64, -125, -37]], ![![-296, 973, 1612, -6, -412]], ![![-1648, -369, 979, 173, -215]], ![![-804, 1181, 2357, 30, -591]], ![![135, 530, 609, -38, -159]]]
  g := ![![![-64, -755, -402, 891, -797], ![-1164, 385, -314, -586, 1876], ![-2049, -2119, -1939, 2295, 59], ![-4734, -2828, -3455, 2843, 2534], ![-10651, -6798, -7989, 6914, 5197]]]
  hle1 := by decide   
  hle2 := by decide  


def P479P0 : CertificateIrreducibleZModOfList' 479 3 2 8 [288, 183, 444, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [169, 131, 293], [345, 347, 186], [0, 1]]
 g := ![![[357, 174, 393], [57, 466, 14], [84, 303, 220], [318, 308, 345], [251, 381, 355], [206, 460], [305, 367, 267], [1]], ![[118, 87, 265, 291], [106, 48, 414, 257], [9, 225, 163, 165], [63, 101, 152, 292], [13, 17, 97, 327], [420, 384], [408, 140, 45, 276], [428, 287, 384, 30]], ![[442, 257, 201, 129], [318, 79, 153, 58], [242, 43, 83, 430], [241, 465, 421, 133], [148, 327, 108, 195], [300, 8], [189, 90, 388, 118], [268, 372, 250, 449]]]
 h' := ![![[169, 131, 293], [349, 145, 414], [237, 273, 400], [384, 399, 157], [41, 264, 102], [27, 61, 129], [296, 468, 287], [191, 296, 35], [0, 1]], ![[345, 347, 186], [97, 284, 291], [124, 170, 365], [265, 241, 383], [411, 401, 181], [390, 276, 366], [40, 239, 87], [244, 30, 199], [169, 131, 293]], ![[0, 1], [136, 50, 253], [3, 36, 193], [362, 318, 418], [250, 293, 196], [45, 142, 463], [15, 251, 105], [327, 153, 245], [345, 347, 186]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [258, 372], []]
 b := ![[], [28, 77, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI479N0 : CertifiedPrimeIdeal' SI479N0 479 where
  n := 3
  hpos := by decide
  P := [288, 183, 444, 1]
  hirr := P479P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-507728292, -355606182, 26341800, -336284068, -402153760]
  a := ![3, -2, 0, -3, -61]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![650619892, 343285954, 452011412, -336284068, -402153760]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI479N0 : Ideal.IsPrime I479N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI479N0 B_one_repr
lemma NI479N0 : Nat.card (O ⧸ I479N0) = 109902239 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI479N0

def I479N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-969, -681, -64, 125, 37]] i)))

def SI479N1: IdealEqSpanCertificate' Table ![![-969, -681, -64, 125, 37]] 
 ![![479, 0, 0, 0, 0], ![0, 479, 0, 0, 0], ![260, 78, 1, 0, 0], ![317, 34, 0, 1, 0], ![453, 157, 0, 0, 1]] where
  M :=![![![-969, -681, -64, 125, 37], ![296, -973, -1612, 6, 412], ![1648, 369, -979, -173, 215], ![712, 1445, 1348, -143, -358], ![480, 541, 318, -50, -101]]]
  hmulB := by decide  
  f := ![![![-4839, 1391, -2942, -891, 797]], ![![6376, -2905, 4564, 586, -1876]], ![![-1604, 283, -861, -393, 127]], ![![-2757, 708, -1622, -554, 389]], ![![-2509, 351, -1288, -665, 128]]]
  g := ![![![-85, -12, -64, 125, 37], ![482, 125, -1612, 6, 412], ![446, 102, -979, -173, 215], ![-297, -89, 1348, -143, -358], ![-43, -14, 318, -50, -101]]]
  hle1 := by decide   
  hle2 := by decide  


def P479P1 : CertificateIrreducibleZModOfList' 479 2 2 8 [97, 416, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [63, 478], [0, 1]]
 g := ![![[187, 400], [92, 25], [403, 194], [363, 115], [207, 241], [33], [389, 163], [63, 1]], ![[0, 79], [230, 454], [171, 285], [423, 364], [62, 238], [33], [120, 316], [126, 478]]]
 h' := ![![[63, 478], [177, 20], [187, 5], [235, 302], [39, 96], [320, 264], [108, 118], [116, 40], [0, 1]], ![[0, 1], [0, 459], [23, 474], [101, 177], [339, 383], [187, 215], [357, 361], [241, 439], [63, 478]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42]]
 b := ![[], [57, 21]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI479N1 : CertifiedPrimeIdeal' SI479N1 479 where
  n := 2
  hpos := by decide
  P := [97, 416, 1]
  hirr := P479P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2074, 1127, 296, 531, -981]
  a := ![1, 0, 1, -1, -6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![420, 238, 296, 531, -981]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI479N1 : Ideal.IsPrime I479N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI479N1 B_one_repr
lemma NI479N1 : Nat.card (O ⧸ I479N1) = 229441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI479N1
def MulI479N0 : IdealMulLeCertificate' Table 
  ![![4839, -1391, 2942, 891, -797]] ![![-969, -681, -64, 125, 37]]
  ![![479, 0, 0, 0, 0]] where
 M := ![![![-479, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC479 : ContainsPrimesAboveP 479 ![I479N0, I479N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI479N0
    exact isPrimeI479N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 479 (by decide) (𝕀 ⊙ MulI479N0)
instance hp487 : Fact (Nat.Prime 487) := {out := by norm_num}

def I487N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3105, -37007, 16368, -36121, 15841]] i)))

def SI487N0: IdealEqSpanCertificate' Table ![![-3105, -37007, 16368, -36121, 15841]] 
 ![![487, 0, 0, 0, 0], ![0, 487, 0, 0, 0], ![0, 0, 487, 0, 0], ![0, 0, 0, 487, 0], ![257, 307, 22, 66, 1]] where
  M :=![![![-3105, -37007, 16368, -36121, 15841], ![126728, 128589, -1772, 179744, -92522], ![-370088, -258699, -51155, -415471, 223355], ![830056, 491207, 157658, 848451, -465268], ![-1168512, -694893, -220304, -1197586, 656335]]]
  hmulB := by decide  
  f := ![![![585, 509, 174, -81, -59]], ![![-472, 545, 1180, 16, -302]], ![![-1208, -409, 529, 115, -127]], ![![-272, -987, -1114, 19, 260]], ![![-81, 459, 708, -25, -192]]]
  g := ![![![-8366, -10062, -682, -2221, 15841], ![49086, 58589, 4176, 12908, -92522], ![-118629, -141332, -10195, -31123, 223355], ![247236, 294309, 21342, 64797, -465268], ![-348761, -415174, -30102, -91408, 656335]]]
  hle1 := by decide   
  hle2 := by decide  


def P487P0 : CertificateIrreducibleZModOfList' 487 4 2 8 [407, 332, 416, 355, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [125, 2, 323, 362], [52, 117, 108, 40], [442, 367, 56, 85], [0, 1]]
 g := ![![[32, 260, 473, 475], [178, 397, 135, 1], [134, 472, 211, 304], [333, 133, 169], [284, 320, 33], [385, 411, 137, 279], [260, 450, 132, 1], []], ![[342, 466, 280, 444, 234, 464], [435, 129, 277, 314, 419, 336], [258, 58, 423, 41, 324, 311], [242, 159, 89], [329, 376, 61], [0, 254, 95, 232, 151, 168], [87, 1, 135, 180, 81, 76], [474, 178, 47, 410, 225, 232]], ![[124, 95, 53, 471, 182, 195], [425, 438, 356, 137, 181, 405], [439, 331, 230, 389, 197, 95], [221, 176, 442], [314, 190, 351], [359, 111, 268, 44, 177, 203], [395, 403, 173, 347, 9, 93], [71, 241, 316, 355, 243, 203]], ![[18, 281, 64, 17, 453, 351], [85, 227, 93, 457, 374, 38], [65, 445, 434, 256, 323, 235], [17, 46, 378], [165, 226, 475], [319, 400, 79, 102, 221, 36], [391, 114, 420, 481, 292, 134], [102, 230, 165, 462, 137, 18]]]
 h' := ![![[125, 2, 323, 362], [117, 459, 206, 44], [6, 444, 245, 1], [458, 310, 181, 257], [356, 71, 477, 13], [119, 426, 251, 153], [346, 328, 396, 124], [0, 0, 0, 1], [0, 1]], ![[52, 117, 108, 40], [346, 387, 30, 174], [341, 460, 17, 3], [268, 368, 452, 211], [43, 213, 211, 463], [316, 151, 329, 388], [451, 116, 316, 380], [189, 296, 67, 24], [125, 2, 323, 362]], ![[442, 367, 56, 85], [149, 299, 463, 312], [41, 96, 274, 83], [342, 55, 21, 395], [235, 405, 132, 429], [88, 345, 141, 389], [382, 448, 339, 40], [188, 32, 442, 307], [52, 117, 108, 40]], ![[0, 1], [364, 316, 275, 444], [57, 461, 438, 400], [404, 241, 320, 111], [273, 285, 154, 69], [173, 52, 253, 44], [197, 82, 410, 430], [312, 159, 465, 155], [442, 367, 56, 85]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [180, 461, 200], []]
 b := ![[], [], [99, 463, 455, 482], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI487N0 : CertifiedPrimeIdeal' SI487N0 487 where
  n := 4
  hpos := by decide
  P := [407, 332, 416, 355, 1]
  hirr := P487P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![50576048219, 36919023130, -5796836628, 28836503629, 57572771091]
  a := ![1, -4, -2, -5, 28]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-30278493064, -36217498361, -2612726490, -7743257471, 57572771091]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI487N0 : Ideal.IsPrime I487N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI487N0 B_one_repr
lemma NI487N0 : Nat.card (O ⧸ I487N0) = 56249134561 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI487N0

def I487N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![585, 509, 174, -81, -59]] i)))

def SI487N1: IdealEqSpanCertificate' Table ![![585, 509, 174, -81, -59]] 
 ![![487, 0, 0, 0, 0], ![288, 1, 0, 0, 0], ![410, 0, 1, 0, 0], ![230, 0, 0, 1, 0], ![281, 0, 0, 0, 1]] where
  M :=![![![585, 509, 174, -81, -59], ![-472, 545, 1180, 16, -302], ![-1208, -409, 529, 115, -127], ![-272, -987, -1114, 19, 260], ![-360, -455, -296, -54, 7]]]
  hmulB := by decide  
  f := ![![![-3105, -37007, 16368, -36121, 15841]], ![![-1576, -21621, 9676, -20992, 9178]], ![![-3374, -31687, 13675, -31263, 13795]], ![![238, -16469, 8054, -15317, 6526]], ![![-4191, -22780, 8992, -23301, 10488]]]
  g := ![![![-374, 509, 174, -81, -59], ![-1150, 545, 1180, 16, -302], ![-187, -409, 529, 115, -127], ![1362, -987, -1114, 19, 260], ![539, -455, -296, -54, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI487N1 : Nat.card (O ⧸ I487N1) = 487 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI487N1)

lemma isPrimeI487N1 : Ideal.IsPrime I487N1 := prime_ideal_of_norm_prime hp487.out _ NI487N1
def MulI487N0 : IdealMulLeCertificate' Table 
  ![![-3105, -37007, 16368, -36121, 15841]] ![![585, 509, 174, -81, -59]]
  ![![487, 0, 0, 0, 0]] where
 M := ![![![487, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC487 : ContainsPrimesAboveP 487 ![I487N0, I487N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI487N0
    exact isPrimeI487N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 487 (by decide) (𝕀 ⊙ MulI487N0)
instance hp491 : Fact (Nat.Prime 491) := {out := by norm_num}

def I491N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-383, -191, -40, -236, -168]] i)))

def SI491N0: IdealEqSpanCertificate' Table ![![-383, -191, -40, -236, -168]] 
 ![![491, 0, 0, 0, 0], ![0, 491, 0, 0, 0], ![316, 190, 1, 0, 0], ![353, 147, 0, 1, 0], ![457, 331, 0, 0, 1]] where
  M :=![![![-383, -191, -40, -236, -168], ![-1344, -1027, 90, -1020, -876], ![-3504, -2307, -7, -2466, -1968], ![-7200, -4929, 114, -5152, -4245], ![-16504, -11243, 212, -11813, -9586]]]
  hmulB := by decide  
  f := ![![![5867, 2183, -2294, -676, 468]], ![![3744, 6589, 5718, -636, -1560]], ![![5212, 3957, 751, -680, -306]], ![![5321, 3527, 58, -674, -129]], ![![7977, 6469, 1720, -1057, -616]]]
  g := ![![![351, 199, -40, -236, -168], ![1488, 859, 90, -1020, -876], ![3602, 2063, -7, -2466, -1968], ![7567, 4350, 114, -5152, -4245], ![17245, 9894, 212, -11813, -9586]]]
  hle1 := by decide   
  hle2 := by decide  


def P491P0 : CertificateIrreducibleZModOfList' 491 2 2 8 [282, 264, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [227, 490], [0, 1]]
 g := ![![[283, 148], [374, 206], [4], [383, 227], [489], [350, 1], [264, 101], [227, 1]], ![[0, 343], [0, 285], [4], [357, 264], [489], [86, 490], [114, 390], [454, 490]]]
 h' := ![![[227, 490], [97, 337], [50, 361], [14, 489], [154, 309], [482, 94], [184, 490], [307, 183], [0, 1]], ![[0, 1], [0, 154], [0, 130], [51, 2], [84, 182], [216, 397], [448, 1], [113, 308], [227, 490]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [354]]
 b := ![[], [287, 177]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI491N0 : CertifiedPrimeIdeal' SI491N0 491 where
  n := 2
  hpos := by decide
  P := [282, 264, 1]
  hirr := P491P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4685, -536, -274, -3768, 3888]
  a := ![-1, 7, 6, 9, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-743, -1388, -274, -3768, 3888]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI491N0 : Ideal.IsPrime I491N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI491N0 B_one_repr
lemma NI491N0 : Nat.card (O ⧸ I491N0) = 241081 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI491N0

def I491N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-89, 23, -53, -18, 13]] i)))

def SI491N1: IdealEqSpanCertificate' Table ![![-89, 23, -53, -18, 13]] 
 ![![491, 0, 0, 0, 0], ![0, 491, 0, 0, 0], ![323, 399, 1, 0, 0], ![256, 45, 0, 1, 0], ![267, 180, 0, 0, 1]] where
  M :=![![![-89, 23, -53, -18, 13], ![104, -59, 82, 3, -41], ![-164, -11, -62, -63, -16], ![-116, -92, 11, -88, -82], ![-332, -200, -13, -225, -167]]]
  hmulB := by decide  
  f := ![![![317, 196, -19, -42, -1]], ![![-8, 335, 476, -3, -127]], ![![201, 401, 375, -30, -104]], ![![164, 132, 33, -22, -12]], ![![169, 229, 164, -24, -47]]]
  g := ![![![37, 40, -53, -18, 13], ![-33, -52, 82, 3, -41], ![82, 62, -62, -63, -16], ![83, 29, 11, -88, -82], ![216, 92, -13, -225, -167]]]
  hle1 := by decide   
  hle2 := by decide  


def P491P1 : CertificateIrreducibleZModOfList' 491 2 2 8 [342, 397, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [94, 490], [0, 1]]
 g := ![![[373, 346], [226, 75], [379], [394, 314], [127], [283, 227], [217, 5], [94, 1]], ![[0, 145], [402, 416], [379], [450, 177], [127], [17, 264], [196, 486], [188, 490]]]
 h' := ![![[94, 490], [286, 185], [139, 417], [277, 88], [309, 455], [432, 451], [418, 309], [258, 147], [0, 1]], ![[0, 1], [0, 306], [57, 74], [202, 403], [362, 36], [109, 40], [4, 182], [328, 344], [94, 490]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [81]]
 b := ![[], [306, 286]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI491N1 : CertifiedPrimeIdeal' SI491N1 491 where
  n := 2
  hpos := by decide
  P := [342, 397, 1]
  hirr := P491P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10218, -11044, -2224, -20342, 9894]
  a := ![0, -12, 0, -22, 6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![6668, 22, -2224, -20342, 9894]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI491N1 : Ideal.IsPrime I491N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI491N1 B_one_repr
lemma NI491N1 : Nat.card (O ⧸ I491N1) = 241081 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI491N1

def I491N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 35, -16, 23, 27]] i)))

def SI491N2: IdealEqSpanCertificate' Table ![![13, 35, -16, 23, 27]] 
 ![![491, 0, 0, 0, 0], ![295, 1, 0, 0, 0], ![432, 0, 1, 0, 0], ![208, 0, 0, 1, 0], ![297, 0, 0, 0, 1]] where
  M :=![![![13, 35, -16, 23, 27], ![216, 109, 24, 134, 96], ![384, 293, -25, 293, 249], ![888, 601, -12, 633, 516], ![2000, 1373, -34, 1436, 1175]]]
  hmulB := by decide  
  f := ![![![-12745, -7533, -2570, -12957, 7143]], ![![-7541, -4458, -1522, -7667, 4227]], ![![-11472, -6779, -2311, -11663, 6429]], ![![-4880, -2887, -988, -4961, 2736]], ![![-8443, -4986, -1696, -8583, 4730]]]
  g := ![![![-33, 35, -16, 23, 27], ![-201, 109, 24, 134, 96], ![-428, 293, -25, 293, 249], ![-929, 601, -12, 633, 516], ![-2110, 1373, -34, 1436, 1175]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI491N2 : Nat.card (O ⧸ I491N2) = 491 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI491N2)

lemma isPrimeI491N2 : Ideal.IsPrime I491N2 := prime_ideal_of_norm_prime hp491.out _ NI491N2
def MulI491N0 : IdealMulLeCertificate' Table 
  ![![-383, -191, -40, -236, -168]] ![![-89, 23, -53, -18, 13]]
  ![![103935, 58212, 6705, 67409, 50900]] where
 M := ![![![103935, 58212, 6705, 67409, 50900]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI491N1 : IdealMulLeCertificate' Table 
  ![![103935, 58212, 6705, 67409, 50900]] ![![13, 35, -16, 23, 27]]
  ![![491, 0, 0, 0, 0]] where
 M := ![![![178158859, 122345907, -2973005, 127917775, 104654686]]]
 hmul := by decide  
 g := ![![![![362849, 249177, -6055, 260525, 213146]]]]
 hle2 := by decide  


def PBC491 : ContainsPrimesAboveP 491 ![I491N0, I491N1, I491N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI491N0
    exact isPrimeI491N1
    exact isPrimeI491N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 491 (by decide) (𝕀 ⊙ MulI491N0 ⊙ MulI491N1)
instance hp499 : Fact (Nat.Prime 499) := {out := by norm_num}

def I499N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![130470199, -42305188, 82408153, 21399180, -25214723]] i)))

def SI499N0: IdealEqSpanCertificate' Table ![![130470199, -42305188, 82408153, 21399180, -25214723]] 
 ![![499, 0, 0, 0, 0], ![0, 499, 0, 0, 0], ![0, 0, 499, 0, 0], ![0, 0, 0, 499, 0], ![25, 276, 271, 53, 1]] where
  M :=![![![130470199, -42305188, 82408153, 21399180, -25214723], ![-201717784, 65405557, -127408736, -33085935, 38982817], ![155931268, -50563250, 98491492, 25574091, -30137494], ![-19691084, 6377821, -12432973, -3233815, 3800981], ![40287172, -13076153, 25454849, 6601056, -7797218]]]
  hmulB := by decide  
  f := ![![![-86075, -32299, 33235, 9918, -6755]], ![![-54040, -96533, -84434, 9267, 22999]], ![![91996, -16373, -105800, -8571, 25400]], ![![128620, 109150, 34415, -17248, -11656]], ![![29531, -52242, -98845, -878, 24938]]]
  g := ![![![1524726, 13861640, 13858914, 2721001, -25214723], ![-2357291, -21430565, -21426357, -4206764, 38982817], ![1822382, 16567906, 16564634, 3252227, -30137494], ![-229891, -2089565, -2089176, -410192, 3800981], ![471378, 4286485, 4285573, 841390, -7797218]]]
  hle1 := by decide   
  hle2 := by decide  


def P499P0 : CertificateIrreducibleZModOfList' 499 4 2 8 [68, 51, 419, 374, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [368, 326, 119, 173], [383, 279, 282, 437], [372, 392, 98, 388], [0, 1]]
 g := ![![[112, 270, 309, 144], [162, 76, 171, 144], [465, 430, 104], [478, 85, 158], [67, 114, 308, 307], [156, 35, 490, 462], [28, 236, 125, 1], []], ![[407, 131, 261, 63, 300, 463], [14, 192, 495, 420, 339, 58], [160, 225, 167], [473, 394, 371], [398, 337, 280, 373, 297, 157], [421, 458, 375, 324, 418, 61], [419, 351, 78, 391, 225, 18], [485, 193, 219, 141, 213, 93]], ![[38, 211, 142, 150, 420, 199], [147, 409, 341, 27, 354, 181], [121, 79, 132], [18, 281, 100], [371, 302, 163, 113, 337, 296], [109, 50, 443, 142, 119, 352], [471, 148, 471, 63, 398, 73], [74, 384, 277, 280, 339, 194]], ![[107, 434, 366, 233, 307, 108], [367, 473, 399, 46, 96, 463], [388, 481, 308], [94, 304, 169], [18, 284, 381, 188, 300, 475], [117, 311, 458, 404, 313, 347], [284, 241, 381, 299, 13, 58], [130, 426, 81, 418, 165, 128]]]
 h' := ![![[368, 326, 119, 173], [461, 440, 51, 487], [266, 124, 68, 12], [164, 495, 106, 435], [434, 482, 3, 465], [370, 124, 301, 236], [92, 488, 167, 468], [0, 0, 0, 1], [0, 1]], ![[383, 279, 282, 437], [237, 86, 404, 386], [380, 221, 227, 353], [301, 196, 245, 243], [23, 406, 262, 37], [258, 262, 21, 36], [173, 43, 214, 412], [357, 157, 179, 43], [368, 326, 119, 173]], ![[372, 392, 98, 388], [257, 209, 207, 157], [252, 407, 7, 152], [220, 288, 123, 272], [461, 61, 412, 10], [378, 406, 411, 110], [99, 41, 184, 60], [433, 296, 70, 19], [383, 279, 282, 437]], ![[0, 1], [298, 263, 336, 467], [79, 246, 197, 481], [495, 19, 25, 48], [479, 49, 321, 486], [43, 206, 265, 117], [181, 426, 433, 58], [154, 46, 250, 436], [372, 392, 98, 388]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [91, 278, 201], []]
 b := ![[], [], [462, 110, 437, 462], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI499N0 : CertifiedPrimeIdeal' SI499N0 499 where
  n := 4
  hpos := by decide
  P := [68, 51, 419, 374, 1]
  hirr := P499P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-32850083, -4215412, -37012703, -78482939, 190498942]
  a := ![13, 5, 5, 6, -13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-9609867, -105374596, -103531515, -20390635, 190498942]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI499N0 : Ideal.IsPrime I499N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI499N0 B_one_repr
lemma NI499N0 : Nat.card (O ⧸ I499N0) = 62001498001 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI499N0

def I499N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-86075, -32299, 33235, 9918, -6755]] i)))

def SI499N1: IdealEqSpanCertificate' Table ![![-86075, -32299, 33235, 9918, -6755]] 
 ![![499, 0, 0, 0, 0], ![339, 1, 0, 0, 0], ![174, 0, 1, 0, 0], ![28, 0, 0, 1, 0], ![401, 0, 0, 0, 1]] where
  M :=![![![-86075, -32299, 33235, 9918, -6755], ![-54040, -96533, -84434, 9267, 22999], ![91996, -16373, -105800, -8571, 25400], ![128620, 109150, 34415, -17248, -11656], ![55108, 33958, -2941, -6879, -419]]]
  hmulB := by decide  
  f := ![![![130470199, -42305188, 82408153, 21399180, -25214723]], ![![88231823, -28609325, 55729369, 14471415, -17051720]], ![![45807106, -14853038, 28932886, 7513089, -8852704]], ![![7281512, -2361057, 4599189, 1194275, -1407237]], ![![104927529, -34022959, 66274798, 17209764, -20278359]]]
  g := ![![![15053, -32299, 33235, 9918, -6755], ![75912, -96533, -84434, 9267, 22999], ![28269, -16373, -105800, -8571, 25400], ![-75560, 109150, 34415, -17248, -11656], ![-21211, 33958, -2941, -6879, -419]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI499N1 : Nat.card (O ⧸ I499N1) = 499 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI499N1)

lemma isPrimeI499N1 : Ideal.IsPrime I499N1 := prime_ideal_of_norm_prime hp499.out _ NI499N1
def MulI499N0 : IdealMulLeCertificate' Table 
  ![![130470199, -42305188, 82408153, 21399180, -25214723]] ![![-86075, -32299, 33235, 9918, -6755]]
  ![![499, 0, 0, 0, 0]] where
 M := ![![![499, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC499 : ContainsPrimesAboveP 499 ![I499N0, I499N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI499N0
    exact isPrimeI499N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 499 (by decide) (𝕀 ⊙ MulI499N0)
instance hp503 : Fact (Nat.Prime 503) := {out := by norm_num}

def I503N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 243, -146, 141, 189]] i)))

def SI503N0: IdealEqSpanCertificate' Table ![![23, 243, -146, 141, 189]] 
 ![![503, 0, 0, 0, 0], ![0, 503, 0, 0, 0], ![8, 76, 1, 0, 0], ![398, 13, 0, 1, 0], ![404, 367, 0, 0, 1]] where
  M :=![![![23, 243, -146, 141, 189], ![1512, 681, 204, 890, 612], ![2448, 1943, -209, 1901, 1641], ![5808, 3931, -60, 4139, 3366], ![13048, 8979, -230, 9378, 7681]]]
  hmulB := by decide  
  f := ![![![-1631, -1321, -352, 209, 129]], ![![1032, -1547, -3060, -10, 756]], ![![136, -253, -471, 1, 117]], ![![-1262, -1080, -352, 165, 120]], ![![-556, -2188, -2514, 160, 655]]]
  g := ![![![-261, -119, -146, 141, 189], ![-1196, -499, 204, 890, 612], ![-2814, -1211, -209, 1901, 1641], ![-5966, -2546, -60, 4139, 3366], ![-13560, -5794, -230, 9378, 7681]]]
  hle1 := by decide   
  hle2 := by decide  


def P503P0 : CertificateIrreducibleZModOfList' 503 2 2 8 [119, 220, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [283, 502], [0, 1]]
 g := ![![[340, 397], [94, 263], [429, 394], [414], [326, 190], [46, 177], [453, 49], [283, 1]], ![[19, 106], [79, 240], [265, 109], [414], [275, 313], [340, 326], [236, 454], [63, 502]]]
 h' := ![![[283, 502], [383, 473], [255, 303], [476, 166], [440, 194], [59, 357], [417, 212], [24, 496], [0, 1]], ![[0, 1], [444, 30], [494, 200], [172, 337], [12, 309], [490, 146], [53, 291], [55, 7], [283, 502]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [199]]
 b := ![[], [382, 351]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI503N0 : CertifiedPrimeIdeal' SI503N0 503 where
  n := 2
  hpos := by decide
  P := [119, 220, 1]
  hirr := P503P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-100, -430, -25, -702, 144]
  a := ![-1, -2, 0, -3, 0]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![440, -84, -25, -702, 144]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI503N0 : Ideal.IsPrime I503N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI503N0 B_one_repr
lemma NI503N0 : Nat.card (O ⧸ I503N0) = 253009 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI503N0

def I503N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, -8, -12, 0, 4]] i)))

def SI503N1: IdealEqSpanCertificate' Table ![![1, -8, -12, 0, 4]] 
 ![![503, 0, 0, 0, 0], ![0, 503, 0, 0, 0], ![203, 344, 1, 0, 0], ![85, 474, 0, 1, 0], ![232, 24, 0, 0, 1]] where
  M :=![![![1, -8, -12, 0, 4], ![32, 9, -16, 4, 4], ![16, 16, 5, -4, 8], ![16, 28, 28, 33, -4], ![16, 20, 4, 8, 37]]]
  hmulB := by decide  
  f := ![![![887, -280, 564, 144, -172]], ![![-1376, 447, -848, -220, 260]], ![![-581, 192, -351, -92, 108]], ![![-1147, 374, -704, -183, 216]], ![![344, -108, 220, 56, -67]]]
  g := ![![![3, 8, -12, 0, 4], ![4, 7, -16, 4, 4], ![-5, 0, 5, -4, 8], ![-15, -50, 28, 33, -4], ![-20, -12, 4, 8, 37]]]
  hle1 := by decide   
  hle2 := by decide  


def P503P1 : CertificateIrreducibleZModOfList' 503 2 2 8 [20, 246, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [257, 502], [0, 1]]
 g := ![![[465, 380], [493, 310], [14, 56], [236], [153, 32], [16, 47], [382, 388], [257, 1]], ![[40, 123], [186, 193], [322, 447], [236], [329, 471], [23, 456], [1, 115], [11, 502]]]
 h' := ![![[257, 502], [200, 216], [223, 286], [62, 168], [461, 241], [183, 125], [408, 405], [393, 136], [0, 1]], ![[0, 1], [382, 287], [287, 217], [483, 335], [26, 262], [116, 378], [372, 98], [135, 367], [257, 502]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [450]]
 b := ![[], [10, 225]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI503N1 : CertifiedPrimeIdeal' SI503N1 503 where
  n := 2
  hpos := by decide
  P := [20, 246, 1]
  hirr := P503P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-577, -1833, 1555, -3505, 1107]
  a := ![3, -4, 7, -8, 0]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-547, 2183, 1555, -3505, 1107]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI503N1 : Ideal.IsPrime I503N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI503N1 B_one_repr
lemma NI503N1 : Nat.card (O ⧸ I503N1) = 253009 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI503N1

def I503N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-33, 25, 68, 3, -17]] i)))

def SI503N2: IdealEqSpanCertificate' Table ![![-33, 25, 68, 3, -17]] 
 ![![503, 0, 0, 0, 0], ![166, 1, 0, 0, 0], ![306, 0, 1, 0, 0], ![172, 0, 0, 1, 0], ![21, 0, 0, 0, 1]] where
  M :=![![![-33, 25, 68, 3, -17], ![-136, -53, 44, 14, -8], ![-32, -73, -67, 9, 17], ![136, 15, -104, -19, 26], ![48, -1, -42, 2, 7]]]
  hmulB := by decide  
  f := ![![![-10743, -7395, 190, -7721, -6325]], ![![-3646, -2509, 64, -2620, -2146]], ![![-6770, -4659, 119, -4865, -3985]], ![![-4172, -2869, 72, -2997, -2454]], ![![-1581, -1082, 24, -1133, -926]]]
  g := ![![![-50, 25, 68, 3, -17], ![-14, -53, 44, 14, -8], ![61, -73, -67, 9, 17], ![64, 15, -104, -19, 26], ![25, -1, -42, 2, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI503N2 : Nat.card (O ⧸ I503N2) = 503 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI503N2)

lemma isPrimeI503N2 : Ideal.IsPrime I503N2 := prime_ideal_of_norm_prime hp503.out _ NI503N2
def MulI503N0 : IdealMulLeCertificate' Table 
  ![![23, 243, -146, 141, 189]] ![![1, -8, -12, 0, 4]]
  ![![10743, 7395, -190, 7721, 6325]] where
 M := ![![![10743, 7395, -190, 7721, 6325]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI503N1 : IdealMulLeCertificate' Table 
  ![![10743, 7395, -190, 7721, 6325]] ![![-33, 25, 68, 3, -17]]
  ![![503, 0, 0, 0, 0]] where
 M := ![![![-503, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC503 : ContainsPrimesAboveP 503 ![I503N0, I503N1, I503N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI503N0
    exact isPrimeI503N1
    exact isPrimeI503N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 503 (by decide) (𝕀 ⊙ MulI503N0 ⊙ MulI503N1)
instance hp509 : Fact (Nat.Prime 509) := {out := by norm_num}

def I509N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1417, 270, 1652, 131, -397]] i)))

def SI509N0: IdealEqSpanCertificate' Table ![![-1417, 270, 1652, 131, -397]] 
 ![![509, 0, 0, 0, 0], ![0, 509, 0, 0, 0], ![505, 343, 1, 0, 0], ![354, 183, 0, 1, 0], ![264, 469, 0, 0, 1]] where
  M :=![![![-1417, 270, 1652, 131, -397], ![-3176, -1881, 278, 394, -4], ![-16, -1656, -2275, 67, 589], ![3944, 1234, -1862, -444, 397], ![1304, 184, -926, -139, 212]]]
  hmulB := by decide  
  f := ![![![1003, 784, -80, 767, 679]], ![![5432, 3551, 34, 3826, 2980]], ![![4679, 3187, -57, 3356, 2696]], ![![2702, 1857, -44, 1946, 1573]], ![![5640, 3757, -12, 4005, 3166]]]
  g := ![![![-1527, -794, 1652, 131, -397], ![-554, -329, 278, 394, -4], ![1905, 963, -2275, 67, 589], ![1958, 1051, -1862, -444, 397], ![908, 479, -926, -139, 212]]]
  hle1 := by decide   
  hle2 := by decide  


def P509P0 : CertificateIrreducibleZModOfList' 509 2 2 8 [2, 237, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [272, 508], [0, 1]]
 g := ![![[373, 258], [320], [1, 195], [217, 216], [0, 442], [47, 38], [145, 280], [272, 1]], ![[307, 251], [320], [105, 314], [434, 293], [100, 67], [203, 471], [464, 229], [35, 508]]]
 h' := ![![[272, 508], [382, 369], [507, 417], [75, 57], [0, 317], [415, 98], [219, 403], [474, 177], [0, 1]], ![[0, 1], [477, 140], [424, 92], [309, 452], [203, 192], [94, 411], [400, 106], [263, 332], [272, 508]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [506]]
 b := ![[], [204, 253]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI509N0 : CertifiedPrimeIdeal' SI509N0 509 where
  n := 2
  hpos := by decide
  P := [2, 237, 1]
  hirr := P509P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1040, -1490, -1685, -3187, 5798]
  a := ![1, -4, -4, -5, 10]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![879, -3064, -1685, -3187, 5798]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI509N0 : Ideal.IsPrime I509N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI509N0 B_one_repr
lemma NI509N0 : Nat.card (O ⧸ I509N0) = 259081 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI509N0

def I509N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3689, -2517, 53, -2634, -2151]] i)))

def SI509N1: IdealEqSpanCertificate' Table ![![-3689, -2517, 53, -2634, -2151]] 
 ![![509, 0, 0, 0, 0], ![0, 509, 0, 0, 0], ![168, 66, 1, 0, 0], ![110, 55, 0, 1, 0], ![436, 54, 0, 0, 1]] where
  M :=![![![-3689, -2517, 53, -2634, -2151], ![-17208, -11757, 234, -12317, -10053], ![-40212, -27461, 560, -28793, -23502], ![-85404, -58306, 1215, -61142, -49914], ![-194116, -132534, 2747, -138957, -113437]]]
  hmulB := by decide  
  f := ![![![-2821, -1466, -611, -2684, 1491]], ![![11928, 6707, 2436, 11899, -6561]], ![![564, 356, 104, 605, -330]], ![![782, 468, 151, 810, -444]], ![![-1296, -629, -293, -1184, 662]]]
  g := ![![![2387, 501, 53, -2634, -2151], ![11162, 2344, 234, -12317, -10053], ![26090, 5478, 560, -28793, -23502], ![55400, 11630, 1215, -61142, -49914], ![125910, 26433, 2747, -138957, -113437]]]
  hle1 := by decide   
  hle2 := by decide  


def P509P1 : CertificateIrreducibleZModOfList' 509 2 2 8 [419, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [490, 508], [0, 1]]
 g := ![![[62, 116], [115], [495, 376], [483, 479], [425, 407], [470, 207], [68, 310], [490, 1]], ![[403, 393], [115], [477, 133], [35, 30], [327, 102], [100, 302], [286, 199], [471, 508]]]
 h' := ![![[490, 508], [199, 484], [267, 290], [205, 365], [75, 315], [53, 173], [12, 35], [326, 451], [0, 1]], ![[0, 1], [165, 25], [356, 219], [396, 144], [198, 194], [329, 336], [365, 474], [410, 58], [490, 508]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48]]
 b := ![[], [228, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI509N1 : CertifiedPrimeIdeal' SI509N1 509 where
  n := 2
  hpos := by decide
  P := [419, 19, 1]
  hirr := P509P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![463, 0, -38, -7, 63]
  a := ![4, 1, -1, 2, 0]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-39, -1, -38, -7, 63]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI509N1 : Ideal.IsPrime I509N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI509N1 B_one_repr
lemma NI509N1 : Nat.card (O ⧸ I509N1) = 259081 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI509N1

def I509N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2715, -1662, -489, -2827, 1544]] i)))

def SI509N2: IdealEqSpanCertificate' Table ![![-2715, -1662, -489, -2827, 1544]] 
 ![![509, 0, 0, 0, 0], ![200, 1, 0, 0, 0], ![360, 0, 1, 0, 0], ![39, 0, 0, 1, 0], ![95, 0, 0, 0, 1]] where
  M :=![![![-2715, -1662, -489, -2827, 1544], ![12352, 7343, 2330, 12657, -6937], ![-27748, -16330, -5314, -28278, 15517], ![55892, 32729, 10783, 56806, -31190], ![-78924, -46223, -15223, -80221, 44045]]]
  hmulB := by decide  
  f := ![![![27057, 4539, -18195, -2921, 4108]], ![![10696, 1847, -7120, -1157, 1605]], ![![19100, 3239, -12796, -2064, 2887]], ![![1967, 287, -1382, -212, 313]], ![![5007, 829, -3382, -543, 762]]]
  g := ![![![922, -1662, -489, -2827, 1544], ![-4184, 7343, 2330, 12657, -6937], ![9391, -16330, -5314, -28278, 15517], ![-18908, 32729, 10783, 56806, -31190], ![26700, -46223, -15223, -80221, 44045]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI509N2 : Nat.card (O ⧸ I509N2) = 509 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI509N2)

lemma isPrimeI509N2 : Ideal.IsPrime I509N2 := prime_ideal_of_norm_prime hp509.out _ NI509N2
def MulI509N0 : IdealMulLeCertificate' Table 
  ![![-1417, 270, 1652, 131, -397]] ![![-3689, -2517, 53, -2634, -2151]]
  ![![27057, 4539, -18195, -2921, 4108]] where
 M := ![![![27057, 4539, -18195, -2921, 4108]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI509N1 : IdealMulLeCertificate' Table 
  ![![27057, 4539, -18195, -2921, 4108]] ![![-2715, -1662, -489, -2827, 1544]]
  ![![509, 0, 0, 0, 0]] where
 M := ![![![509, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC509 : ContainsPrimesAboveP 509 ![I509N0, I509N1, I509N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI509N0
    exact isPrimeI509N1
    exact isPrimeI509N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 509 (by decide) (𝕀 ⊙ MulI509N0 ⊙ MulI509N1)
instance hp521 : Fact (Nat.Prime 521) := {out := by norm_num}

def I521N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1417, -454, 901, 231, -276]] i)))

def SI521N0: IdealEqSpanCertificate' Table ![![1417, -454, 901, 231, -276]] 
 ![![521, 0, 0, 0, 0], ![0, 521, 0, 0, 0], ![0, 0, 521, 0, 0], ![477, 233, 90, 1, 0], ![194, 6, 342, 0, 1]] where
  M :=![![![1417, -454, 901, 231, -276], ![-2208, 707, -1370, -361, 417], ![1668, -566, 1068, 270, -333], ![-228, 47, -151, -52, 30], ![380, -185, 271, 29, -115]]]
  hmulB := by decide  
  f := ![![![-7, -13, -13, -5, 6]], ![![48, 15, -16, 21, -9]], ![![-36, -17, -6, -58, 27]], ![![9, -8, -20, -5, 6]], ![![-26, -16, -9, -40, 20]]]
  g := ![![![-106, -101, 143, 231, -276], ![171, 158, -214, -361, 417], ![-120, -118, 174, 270, -333], ![36, 23, -11, -52, 30], ![17, -12, 71, 29, -115]]]
  hle1 := by decide   
  hle2 := by decide  


def P521P0 : CertificateIrreducibleZModOfList' 521 3 2 9 [121, 361, 123, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 221, 113], [364, 299, 408], [0, 1]]
 g := ![![[60, 301, 416], [207, 471], [205, 323], [48, 37, 13], [503, 474], [207, 325], [412, 98], [398, 1], []], ![[498, 286, 149, 119], [45, 254], [498, 94], [432, 5, 455, 336], [383, 90], [421, 26], [342, 301], [36, 310], [158, 265]], ![[174, 154, 140, 29], [76, 11], [257, 441], [476, 44, 355, 155], [33, 202], [474, 419], [360, 4], [155, 388], [384, 265]]]
 h' := ![![[34, 221, 113], [294, 51, 50], [401, 252, 227], [444, 191, 140], [487, 44, 137], [262, 121, 60], [182, 192, 357], [295, 518, 180], [0, 0, 1], [0, 1]], ![[364, 299, 408], [48, 369, 394], [84, 195, 485], [352, 15, 402], [309, 109, 87], [437, 321, 353], [492, 374, 273], [359, 311, 339], [273, 428, 299], [34, 221, 113]], ![[0, 1], [326, 101, 77], [12, 74, 330], [156, 315, 500], [153, 368, 297], [394, 79, 108], [209, 476, 412], [322, 213, 2], [67, 93, 221], [364, 299, 408]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [357, 493], []]
 b := ![[], [78, 141, 240], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI521N0 : CertifiedPrimeIdeal' SI521N0 521 where
  n := 3
  hpos := by decide
  P := [121, 361, 123, 1]
  hirr := P521P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-23190, -112180, -102280, 5396, 31564]
  a := ![7, -1, -26, -1, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-16738, -2992, -21848, 5396, 31564]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI521N0 : Ideal.IsPrime I521N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI521N0 B_one_repr
lemma NI521N0 : Nat.card (O ⧸ I521N0) = 141420761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI521N0

def I521N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, -13, -13, -5, 6]] i)))

def SI521N1: IdealEqSpanCertificate' Table ![![-7, -13, -13, -5, 6]] 
 ![![521, 0, 0, 0, 0], ![0, 521, 0, 0, 0], ![95, 431, 1, 0, 0], ![214, 284, 0, 1, 0], ![383, 300, 0, 0, 1]] where
  M :=![![![-7, -13, -13, -5, 6], ![48, 15, -16, 21, -9], ![-36, -17, -6, -58, 27], ![84, 68, 49, 107, -69], ![-164, -90, -19, -160, 76]]]
  hmulB := by decide  
  f := ![![![1417, -454, 901, 231, -276]], ![![-2208, 707, -1370, -361, 417]], ![![-1565, 501, -967, -256, 294]], ![![-622, 199, -377, -102, 114]], ![![-229, 73, -126, -38, 37]]]
  g := ![![![0, 10, -13, -5, 6], ![1, 7, -16, 21, -9], ![5, 21, -6, -58, 27], ![-2, -59, 49, 107, -69], ![13, 59, -19, -160, 76]]]
  hle1 := by decide   
  hle2 := by decide  


def P521P1 : CertificateIrreducibleZModOfList' 521 2 2 9 [350, 366, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [155, 520], [0, 1]]
 g := ![![[7, 265], [261], [145], [222, 472], [197], [265], [370], [59], [1]], ![[444, 256], [261], [145], [442, 49], [197], [265], [370], [59], [1]]]
 h' := ![![[155, 520], [390, 113], [139, 136], [450, 183], [108, 439], [478, 459], [129, 408], [255, 156], [171, 155], [0, 1]], ![[0, 1], [191, 408], [379, 385], [160, 338], [423, 82], [246, 62], [328, 113], [469, 365], [230, 366], [155, 520]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61]]
 b := ![[], [111, 291]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI521N1 : CertifiedPrimeIdeal' SI521N1 521 where
  n := 2
  hpos := by decide
  P := [350, 366, 1]
  hirr := P521P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![837, 47, -1866, -307, 87]
  a := ![1, 0, -5, -1, 0]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![404, 1661, -1866, -307, 87]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI521N1 : Ideal.IsPrime I521N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI521N1 B_one_repr
lemma NI521N1 : Nat.card (O ⧸ I521N1) = 271441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI521N1
def MulI521N0 : IdealMulLeCertificate' Table 
  ![![1417, -454, 901, 231, -276]] ![![-7, -13, -13, -5, 6]]
  ![![521, 0, 0, 0, 0]] where
 M := ![![![521, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC521 : ContainsPrimesAboveP 521 ![I521N0, I521N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI521N0
    exact isPrimeI521N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 521 (by decide) (𝕀 ⊙ MulI521N0)
instance hp523 : Fact (Nat.Prime 523) := {out := by norm_num}

def I523N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![523, 0, 0, 0, 0]] i)))

def SI523N0: IdealEqSpanCertificate' Table ![![523, 0, 0, 0, 0]] 
 ![![523, 0, 0, 0, 0], ![0, 523, 0, 0, 0], ![0, 0, 523, 0, 0], ![0, 0, 0, 523, 0], ![0, 0, 0, 0, 523]] where
  M :=![![![523, 0, 0, 0, 0], ![0, 523, 0, 0, 0], ![0, 0, 523, 0, 0], ![0, 0, 0, 523, 0], ![0, 0, 0, 0, 523]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P523P0 : CertificateIrreducibleZModOfList' 523 5 2 9 [503, 0, 262, 495, 268, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [432, 222, 290, 308, 249], [247, 398, 307, 515, 7], [58, 196, 260, 73, 192], [41, 229, 189, 150, 75], [0, 1]]
 g := ![![[440, 329, 493, 401, 76], [182, 234, 334, 151, 400], [0, 43, 24, 331], [259, 346, 480, 398, 158], [232, 346, 366, 60], [92, 193, 161, 144], [80, 201, 255, 1], [], []], ![[176, 96, 439, 328, 69, 322, 482, 196], [215, 447, 90, 369, 307, 433, 371, 448], [31, 283, 475, 383], [44, 167, 455, 83, 384, 146, 303, 44], [261, 276, 364, 435], [46, 172, 305, 375], [452, 230, 403, 369], [410, 378, 84, 89], [361, 272, 110, 287]], ![[324, 306, 248, 322, 80, 246, 103, 462], [394, 80, 6, 474, 262, 395, 313, 256], [66, 510, 150, 280], [0, 31, 276, 62, 351, 378, 423, 194], [408, 57, 472, 310], [181, 21, 407, 160], [329, 94, 513, 240], [316, 471, 85, 448], [262, 295, 354, 49]], ![[474, 123, 13, 410, 98, 373, 100, 366], [152, 66, 292, 231, 56, 484, 211, 3], [241, 327, 383, 387], [283, 211, 85, 198, 68, 465, 237, 30], [352, 19, 230, 212], [226, 400, 488, 263], [237, 377, 356, 81], [84, 379, 111, 439], [33, 165, 231, 254]], ![[497, 199, 81, 209, 406, 5, 445, 51], [13, 71, 18, 204, 149, 508, 275, 517], [247, 226, 189, 191], [275, 20, 483, 10, 350, 329, 92, 498], [258, 204, 482, 183], [299, 142, 119, 74], [43, 395, 120, 308], [261, 371, 211, 68], [398, 208, 320, 395]]]
 h' := ![![[432, 222, 290, 308, 249], [502, 123, 441, 374, 434], [408, 195, 153, 415, 503], [473, 242, 500, 314, 78], [11, 246, 27, 175, 415], [186, 491, 179, 191, 462], [31, 359, 353, 329, 12], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[247, 398, 307, 515, 7], [155, 116, 73, 379, 366], [103, 12, 131, 425, 23], [23, 332, 385, 483, 365], [166, 452, 294, 226, 301], [77, 395, 367, 67, 459], [270, 67, 323, 484, 109], [512, 420, 158, 141, 328], [334, 77, 354, 29, 52], [432, 222, 290, 308, 249]], ![[58, 196, 260, 73, 192], [343, 499, 232, 111, 211], [145, 324, 265, 58, 126], [191, 415, 228, 254, 43], [230, 146, 512, 297, 352], [492, 151, 112, 407, 235], [321, 468, 499, 125, 238], [340, 1, 257, 285, 122], [351, 111, 73, 425, 441], [247, 398, 307, 515, 7]], ![[41, 229, 189, 150, 75], [508, 274, 79, 283, 103], [204, 16, 177, 56, 196], [406, 10, 109, 58, 424], [138, 324, 227, 178, 367], [233, 368, 18, 114, 475], [290, 279, 273, 75, 250], [84, 128, 415, 296, 9], [363, 409, 221, 465, 396], [58, 196, 260, 73, 192]], ![[0, 1], [497, 34, 221, 422, 455], [349, 499, 320, 92, 198], [330, 47, 347, 460, 136], [186, 401, 509, 170, 134], [507, 164, 370, 267, 461], [480, 396, 121, 33, 437], [265, 497, 216, 324, 63], [227, 449, 397, 127, 157], [41, 229, 189, 150, 75]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [233, 110, 240, 356], [], [], []]
 b := ![[], [12, 459, 294, 45, 154], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI523N0 : CertifiedPrimeIdeal' SI523N0 523 where
  n := 5
  hpos := by decide
  P := [503, 0, 262, 495, 268, 1]
  hirr := P523P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![291406396769, 199023753650, -4251015128, 208407899764, 171007870608]
  a := ![3, 4, 0, 9, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![557182403, 380542550, -8128136, 398485468, 326974896]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI523N0 : Ideal.IsPrime I523N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI523N0 B_one_repr
lemma NI523N0 : Nat.card (O ⧸ I523N0) = 39129873538843 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI523N0

def PBC523 : ContainsPrimesAboveP 523 ![I523N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI523N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![523, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 523 (by decide) 𝕀



lemma PB1072I10_primes (p : ℕ) :
  p ∈ Set.range ![467, 479, 487, 491, 499, 503, 509, 521, 523] ↔ Nat.Prime p ∧ 463 < p ∧ p ≤ 523 := by
  rw [← List.mem_ofFn']
  convert primes_range 463 523 (by omega)

def PB1072I10 : PrimesBelowBoundCertificateInterval O 463 523 1072 where
  m := 9
  g := ![2, 2, 2, 3, 2, 3, 3, 2, 1]
  P := ![467, 479, 487, 491, 499, 503, 509, 521, 523]
  hP := PB1072I10_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I467N0, I467N1]
    · exact ![I479N0, I479N1]
    · exact ![I487N0, I487N1]
    · exact ![I491N0, I491N1, I491N2]
    · exact ![I499N0, I499N1]
    · exact ![I503N0, I503N1, I503N2]
    · exact ![I509N0, I509N1, I509N2]
    · exact ![I521N0, I521N1]
    · exact ![I523N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC467
    · exact PBC479
    · exact PBC487
    · exact PBC491
    · exact PBC499
    · exact PBC503
    · exact PBC509
    · exact PBC521
    · exact PBC523
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![47562811921, 467]
    · exact ![109902239, 229441]
    · exact ![56249134561, 487]
    · exact ![241081, 241081, 491]
    · exact ![62001498001, 499]
    · exact ![253009, 253009, 503]
    · exact ![259081, 259081, 509]
    · exact ![141420761, 271441]
    · exact ![39129873538843]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI467N0
      exact NI467N1
    · dsimp ; intro j
      fin_cases j
      exact NI479N0
      exact NI479N1
    · dsimp ; intro j
      fin_cases j
      exact NI487N0
      exact NI487N1
    · dsimp ; intro j
      fin_cases j
      exact NI491N0
      exact NI491N1
      exact NI491N2
    · dsimp ; intro j
      fin_cases j
      exact NI499N0
      exact NI499N1
    · dsimp ; intro j
      fin_cases j
      exact NI503N0
      exact NI503N1
      exact NI503N2
    · dsimp ; intro j
      fin_cases j
      exact NI509N0
      exact NI509N1
      exact NI509N2
    · dsimp ; intro j
      fin_cases j
      exact NI521N0
      exact NI521N1
    · dsimp ; intro j
      fin_cases j
      exact NI523N0
  β := ![I467N1, I487N1, I491N2, I499N1, I503N2, I509N2]
  Il := ![[I467N1], [], [I487N1], [I491N2], [I499N1], [I503N2], [I509N2], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
