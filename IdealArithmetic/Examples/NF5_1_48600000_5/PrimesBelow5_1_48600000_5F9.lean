
import IdealArithmetic.Examples.NF5_1_48600000_5.RI5_1_48600000_5
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp421 : Fact (Nat.Prime 421) := {out := by norm_num}

def I421N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![421, 0, 0, 0, 0]] i)))

def SI421N0: IdealEqSpanCertificate' Table ![![421, 0, 0, 0, 0]] 
 ![![421, 0, 0, 0, 0], ![0, 421, 0, 0, 0], ![0, 0, 421, 0, 0], ![0, 0, 0, 421, 0], ![0, 0, 0, 0, 421]] where
  M :=![![![421, 0, 0, 0, 0], ![0, 421, 0, 0, 0], ![0, 0, 421, 0, 0], ![0, 0, 0, 421, 0], ![0, 0, 0, 0, 421]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P421P0 : CertificateIrreducibleZModOfList' 421 5 2 8 [117, 220, 37, 54, 341, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [250, 276, 205, 71, 145], [74, 382, 271, 127, 175], [90, 340, 100, 342, 117], [87, 264, 266, 302, 405], [0, 1]]
 g := ![![[131, 346, 337, 261, 375], [411, 288, 271, 341], [87, 188, 297, 350, 64], [410, 258, 196, 1], [223, 79, 74, 135], [380, 18, 379, 406, 119], [80, 1], []], ![[340, 382, 83, 265, 237, 383, 338, 145], [8, 215, 214, 114], [165, 392, 20, 234, 274, 216, 124, 378], [129, 384, 365, 388], [284, 283, 306, 401], [156, 256, 89, 217, 31, 252, 5, 369], [40, 282, 288, 246], [36, 2, 0, 321, 354, 132, 217, 164]], ![[51, 406, 396, 227, 193, 210, 25, 410], [66, 391, 72, 63], [59, 250, 257, 241, 402, 274, 308, 139], [104, 220, 84, 191], [198, 420, 246, 414], [396, 351, 96, 332, 187, 131, 254, 63], [367, 264, 329, 383], [122, 6, 227, 326, 69, 7, 342, 45]], ![[298, 171, 214, 42, 407, 402, 129, 264], [199, 318, 366, 187], [136, 201, 278, 1, 270, 161, 251, 57], [295, 123, 111, 49], [59, 13, 274, 357], [8, 143, 93, 14, 46, 93, 271, 259], [363, 109, 146, 230], [212, 120, 69, 75, 215, 296, 149, 129]], ![[354, 86, 173, 121, 324, 387, 279, 118], [400, 335, 370, 149], [132, 220, 125, 411, 247, 113, 380, 192], [16, 259, 149, 80], [114, 223, 13, 21], [157, 20, 264, 317, 193, 33, 323, 105], [418, 336, 25, 237], [66, 238, 388, 404, 53, 182, 244, 114]]]
 h' := ![![[250, 276, 205, 71, 145], [59, 362, 388, 299, 96], [346, 203, 219, 163, 45], [412, 48, 92, 386, 8], [202, 246, 104, 363, 420], [166, 99, 69, 75, 226], [323, 386, 188, 274, 31], [0, 0, 0, 1], [0, 1]], ![[74, 382, 271, 127, 175], [390, 168, 239, 154, 1], [399, 370, 240, 278, 249], [317, 15, 189, 410, 9], [153, 252, 311, 269, 202], [135, 132, 359, 33, 233], [388, 296, 256, 200, 414], [4, 104, 307, 83, 81], [250, 276, 205, 71, 145]], ![[90, 340, 100, 342, 117], [203, 313, 100, 20, 354], [79, 69, 208, 266, 399], [115, 261, 49, 346, 160], [235, 336, 287, 132, 255], [81, 356, 244, 186, 353], [24, 283, 13, 289, 252], [262, 314, 378, 6, 386], [74, 382, 271, 127, 175]], ![[87, 264, 266, 302, 405], [140, 113, 15, 168, 410], [302, 174, 199, 29, 271], [395, 134, 138, 108, 326], [219, 363, 282, 179, 7], [293, 284, 345, 41, 189], [295, 344, 85, 274, 303], [284, 240, 94, 263, 183], [90, 340, 100, 342, 117]], ![[0, 1], [380, 307, 100, 201, 402], [266, 26, 397, 106, 299], [382, 384, 374, 13, 339], [122, 66, 279, 320, 379], [82, 392, 246, 86, 262], [419, 375, 300, 226, 263], [336, 184, 63, 68, 192], [87, 264, 266, 302, 405]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [366, 97, 183, 10], [], [], []]
 b := ![[], [83, 70, 300, 182, 58], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI421N0 : CertifiedPrimeIdeal' SI421N0 421 where
  n := 5
  hpos := by decide
  P := [117, 220, 37, 54, 341, 1]
  hirr := P421P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5553003893, -9905197064, 3426295028, 2656327286, -49183746]
  a := ![5, -7, -8, -8, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-13190033, -23527784, 8138468, 6309566, -116826]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI421N0 : Ideal.IsPrime I421N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI421N0 B_one_repr
lemma NI421N0 : Nat.card (O ⧸ I421N0) = 13225450646101 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI421N0

def PBC421 : ContainsPrimesAboveP 421 ![I421N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI421N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![421, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 421 (by decide) 𝕀

instance hp431 : Fact (Nat.Prime 431) := {out := by norm_num}

def I431N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-36, 940, 428, -488, 1447]] i)))

def SI431N0: IdealEqSpanCertificate' Table ![![-36, 940, 428, -488, 1447]] 
 ![![431, 0, 0, 0, 0], ![0, 431, 0, 0, 0], ![428, 254, 1, 0, 0], ![331, 133, 0, 1, 0], ![167, 231, 0, 0, 1]] where
  M :=![![![-36, 940, 428, -488, 1447], ![-1918, -7819, 3798, -120, -5822], ![5942, 15375, -13761, 3678, 5462], ![-8181, -9977, 22616, -10023, 8483], ![1887, -6884, -7914, 6190, -15076]]]
  hmulB := by decide  
  f := ![![![2599771246, -573238456, -152858134, 123844970, 485203571]], ![![-1218097082, 268585197, 71620170, -58026328, -227337322]], ![![1864479810, -411109839, -109625375, 88817990, 347973798]], ![![1621947951, -357632598, -95365288, 77264529, 302709304]], ![![356695595, -78649859, -20972544, 16991866, 66571237]]]
  g := ![![![-611, -875, 428, -488, 1447], ![-1428, 901, 3798, -120, -5822], ![8738, 4083, -13761, 3678, 5462], ![-18067, -14805, 22616, -10023, 8483], ![8951, 10818, -7914, 6190, -15076]]]
  hle1 := by decide   
  hle2 := by decide  


def P431P0 : CertificateIrreducibleZModOfList' 431 2 2 8 [249, 69, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [362, 430], [0, 1]]
 g := ![![[343, 144], [68, 82], [412, 205], [223, 150], [200], [58, 95], [290], [362, 1]], ![[320, 287], [13, 349], [59, 226], [217, 281], [200], [399, 336], [290], [293, 430]]]
 h' := ![![[362, 430], [308, 419], [421, 274], [72, 140], [316, 222], [212, 275], [231, 116], [372, 202], [0, 1]], ![[0, 1], [274, 12], [48, 157], [325, 291], [83, 209], [201, 156], [416, 315], [226, 229], [362, 430]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [242]]
 b := ![[], [80, 121]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI431N0 : CertifiedPrimeIdeal' SI431N0 431 where
  n := 2
  hpos := by decide
  P := [249, 69, 1]
  hirr := P431P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![397, 57372, -52972, 58294, 59598]
  a := ![-6, -56, 11, -57, 21]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-15257, -18580, -52972, 58294, 59598]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI431N0 : Ideal.IsPrime I431N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI431N0 B_one_repr
lemma NI431N0 : Nat.card (O ⧸ I431N0) = 185761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI431N0

def I431N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10278064, -2266298, -604310, 489632, 1918251]] i)))

def SI431N1: IdealEqSpanCertificate' Table ![![10278064, -2266298, -604310, 489632, 1918251]] 
 ![![431, 0, 0, 0, 0], ![0, 431, 0, 0, 0], ![117, 220, 1, 0, 0], ![120, 362, 0, 1, 0], ![313, 289, 0, 0, 1]] where
  M :=![![![10278064, -2266298, -604310, 489632, 1918251], ![-4815766, 1061763, 283170, -229356, -898710], ![1128066, -248879, -66303, 53814, 210642], ![2143427, -472791, -126008, 102189, 400155], ![3773331, -831960, -221872, 179722, 704192]]]
  hmulB := by decide  
  f := ![![![6690, 17782, -15552, 4074, 6807]], ![![-21762, -34749, 57326, -22956, 10830]], ![![-9264, -12985, 24931, -10532, 7191]], ![![-16285, -23693, 43572, -18149, 11403]], ![![-9901, -10865, 27524, -12522, 11987]]]
  g := ![![![-1341499, -1394291, -604310, 489632, 1918251], ![628474, 653175, 283170, -229356, -898710], ![-147339, -153175, -66303, 53814, 210642], ![-279872, -290924, -126008, 102189, 400155], ![-492451, -511812, -221872, 179722, 704192]]]
  hle1 := by decide   
  hle2 := by decide  


def P431P1 : CertificateIrreducibleZModOfList' 431 2 2 8 [333, 60, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [371, 430], [0, 1]]
 g := ![![[404, 184], [52, 80], [393, 328], [312, 318], [345], [21, 324], [5], [371, 1]], ![[139, 247], [424, 351], [108, 103], [196, 113], [345], [407, 107], [5], [311, 430]]]
 h' := ![![[371, 430], [355, 299], [155, 138], [406, 314], [119, 201], [334, 50], [70, 413], [154, 250], [0, 1]], ![[0, 1], [86, 132], [64, 293], [99, 117], [127, 230], [351, 381], [288, 18], [239, 181], [371, 430]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [225]]
 b := ![[], [358, 328]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI431N1 : CertifiedPrimeIdeal' SI431N1 431 where
  n := 2
  hpos := by decide
  P := [333, 60, 1]
  hirr := P431P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![77, -324, 59, 69, 391]
  a := ![1, -4, -1, -5, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-319, -351, 59, 69, 391]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI431N1 : Ideal.IsPrime I431N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI431N1 B_one_repr
lemma NI431N1 : Nat.card (O ⧸ I431N1) = 185761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI431N1

def I431N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-215, 48, 12, -10, -40]] i)))

def SI431N2: IdealEqSpanCertificate' Table ![![-215, 48, 12, -10, -40]] 
 ![![431, 0, 0, 0, 0], ![345, 1, 0, 0, 0], ![181, 0, 1, 0, 0], ![68, 0, 0, 1, 0], ![58, 0, 0, 0, 1]] where
  M :=![![![-215, 48, 12, -10, -40], ![100, -23, -4, 4, 20], ![-24, 2, 1, 0, -8], ![-42, 20, -4, -1, -2], ![-82, 10, 12, -6, -17]]]
  hmulB := by decide  
  f := ![![![515, 376, -396, -502, -524]], ![![417, 305, -320, -406, -424]], ![![225, 166, -171, -218, -228]], ![![94, 72, -68, -89, -94]], ![![68, 50, -52, -66, -69]]]
  g := ![![![-37, 48, 12, -10, -40], ![17, -23, -4, 4, 20], ![-1, 2, 1, 0, -8], ![-14, 20, -4, -1, -2], ![-10, 10, 12, -6, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI431N2 : Nat.card (O ⧸ I431N2) = 431 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI431N2)

lemma isPrimeI431N2 : Ideal.IsPrime I431N2 := prime_ideal_of_norm_prime hp431.out _ NI431N2
def MulI431N0 : IdealMulLeCertificate' Table 
  ![![-36, 940, 428, -488, 1447]] ![![10278064, -2266298, -604310, 489632, 1918251]]
  ![![-515, -376, 396, 502, 524]] where
 M := ![![![-515, -376, 396, 502, 524]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI431N1 : IdealMulLeCertificate' Table 
  ![![-515, -376, 396, 502, 524]] ![![-215, 48, 12, -10, -40]]
  ![![431, 0, 0, 0, 0]] where
 M := ![![![-431, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC431 : ContainsPrimesAboveP 431 ![I431N0, I431N1, I431N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI431N0
    exact isPrimeI431N1
    exact isPrimeI431N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 431 (by decide) (𝕀 ⊙ MulI431N0 ⊙ MulI431N1)
instance hp433 : Fact (Nat.Prime 433) := {out := by norm_num}

def I433N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 217, -74, -84, -66]] i)))

def SI433N0: IdealEqSpanCertificate' Table ![![151, 217, -74, -84, -66]] 
 ![![433, 0, 0, 0, 0], ![0, 433, 0, 0, 0], ![0, 0, 433, 0, 0], ![0, 0, 0, 433, 0], ![83, 82, 421, 80, 1]] where
  M :=![![![151, 217, -74, -84, -66], ![300, 239, 134, -316, -372], ![688, 831, -449, -182, -576], ![608, 1258, 6, -473, 216], ![-396, -939, 412, 140, -323]]]
  hmulB := by decide  
  f := ![![![-677, 149, 40, -32, -126]], ![![316, -71, -18, 16, 60]], ![![-76, 15, 5, -2, -12]], ![![-144, 28, 10, -5, -24]], ![![-171, 35, 11, -6, -29]]]
  g := ![![![13, 13, 64, 12, -66], ![72, 71, 362, 68, -372], ![112, 111, 559, 106, -576], ![-40, -38, -210, -41, 216], ![61, 59, 315, 60, -323]]]
  hle1 := by decide   
  hle2 := by decide  


def P433P0 : CertificateIrreducibleZModOfList' 433 4 2 8 [38, 270, 168, 332, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [368, 376, 165, 368], [217, 129, 90, 413], [382, 360, 178, 85], [0, 1]]
 g := ![![[241, 264, 128, 397], [359, 182, 269], [245, 228, 331], [153, 37, 223], [370, 126, 141, 233], [280, 86, 17, 354], [74, 101, 1], []], ![[11, 44, 248, 63, 112, 287], [415, 113, 318], [107, 98, 288], [339, 253, 396], [293, 257, 239, 411, 316, 7], [315, 329, 175, 342, 277, 141], [62, 67, 374], [236, 383, 36, 296, 407, 330]], ![[78, 411, 373, 400, 53, 391], [111, 357, 4], [214, 284, 41], [426, 180, 233], [203, 54, 251, 114, 159, 214], [136, 33, 235, 164, 216, 194], [326, 352, 147], [49, 311, 189, 253, 161, 227]], ![[341, 333, 193, 304, 62, 15], [41, 8, 208], [278, 208, 271], [184, 395, 394], [322, 10, 107, 324, 112, 276], [319, 332, 13, 1, 93, 152], [1, 39, 272], [265, 428, 6, 144, 361, 131]]]
 h' := ![![[368, 376, 165, 368], [373, 286, 145, 225], [366, 244, 135, 139], [296, 20, 59, 214], [229, 116, 157, 400], [185, 269, 91, 176], [219, 430, 96, 195], [0, 0, 0, 1], [0, 1]], ![[217, 129, 90, 413], [399, 203, 92, 263], [183, 251, 148, 379], [312, 163, 36, 307], [44, 113, 382, 292], [40, 93, 342, 45], [293, 20, 110, 380], [22, 301, 105, 272], [368, 376, 165, 368]], ![[382, 360, 178, 85], [111, 409, 103, 201], [254, 355, 313, 2], [67, 104, 260, 100], [235, 160, 134, 257], [136, 329, 323, 165], [251, 221, 388, 371], [249, 271, 121, 357], [217, 129, 90, 413]], ![[0, 1], [120, 401, 93, 177], [165, 16, 270, 346], [213, 146, 78, 245], [166, 44, 193, 350], [308, 175, 110, 47], [378, 195, 272, 353], [169, 294, 207, 236], [382, 360, 178, 85]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [305, 239, 70], []]
 b := ![[], [], [204, 31, 367, 220], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI433N0 : CertifiedPrimeIdeal' SI433N0 433 where
  n := 4
  hpos := by decide
  P := [38, 270, 168, 332, 1]
  hirr := P433P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3312647423, -3623938020, 1119313599, 2432213078, 2681802356]
  a := ![-8, 27, 13, 26, 25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-521714187, -516239564, -2604894869, -489865994, 2681802356]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI433N0 : Ideal.IsPrime I433N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI433N0 B_one_repr
lemma NI433N0 : Nat.card (O ⧸ I433N0) = 35152125121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI433N0

def I433N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![677, -149, -40, 32, 126]] i)))

def SI433N1: IdealEqSpanCertificate' Table ![![677, -149, -40, 32, 126]] 
 ![![433, 0, 0, 0, 0], ![388, 1, 0, 0, 0], ![70, 0, 1, 0, 0], ![82, 0, 0, 1, 0], ![146, 0, 0, 0, 1]] where
  M :=![![![677, -149, -40, 32, 126], ![-316, 71, 18, -16, -60], ![76, -15, -5, 2, 12], ![144, -28, -10, 5, 24], ![248, -55, -14, 12, 47]]]
  hmulB := by decide  
  f := ![![![-151, -217, 74, 84, 66]], ![![-136, -195, 66, 76, 60]], ![![-26, -37, 13, 14, 12]], ![![-30, -44, 14, 17, 12]], ![![-50, -71, 24, 28, 23]]]
  g := ![![![93, -149, -40, 32, 126], ![-44, 71, 18, -16, -60], ![10, -15, -5, 2, 12], ![18, -28, -10, 5, 24], ![34, -55, -14, 12, 47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI433N1 : Nat.card (O ⧸ I433N1) = 433 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI433N1)

lemma isPrimeI433N1 : Ideal.IsPrime I433N1 := prime_ideal_of_norm_prime hp433.out _ NI433N1
def MulI433N0 : IdealMulLeCertificate' Table 
  ![![151, 217, -74, -84, -66]] ![![677, -149, -40, 32, 126]]
  ![![433, 0, 0, 0, 0]] where
 M := ![![![-433, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC433 : ContainsPrimesAboveP 433 ![I433N0, I433N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI433N0
    exact isPrimeI433N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 433 (by decide) (𝕀 ⊙ MulI433N0)


lemma PB434I9_primes (p : ℕ) :
  p ∈ Set.range ![421, 431, 433] ↔ Nat.Prime p ∧ 419 < p ∧ p ≤ 433 := by
  rw [← List.mem_ofFn']
  convert primes_range 419 433 (by omega)

def PB434I9 : PrimesBelowBoundCertificateInterval O 419 433 434 where
  m := 3
  g := ![1, 3, 2]
  P := ![421, 431, 433]
  hP := PB434I9_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I421N0]
    · exact ![I431N0, I431N1, I431N2]
    · exact ![I433N0, I433N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC421
    · exact PBC431
    · exact PBC433
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![13225450646101]
    · exact ![185761, 185761, 431]
    · exact ![35152125121, 433]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI421N0
    · dsimp ; intro j
      fin_cases j
      exact NI431N0
      exact NI431N1
      exact NI431N2
    · dsimp ; intro j
      fin_cases j
      exact NI433N0
      exact NI433N1
  β := ![I431N2, I433N1]
  Il := ![[], [I431N2], [I433N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
