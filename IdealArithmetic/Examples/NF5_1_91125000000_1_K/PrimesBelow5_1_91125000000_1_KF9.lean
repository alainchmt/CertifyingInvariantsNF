
import IdealArithmetic.Examples.NF5_1_91125000000_1_K.RI5_1_91125000000_1_K
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 

instance hp421 : Fact (Nat.Prime 421) := {out := by norm_num}

def I421N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![421, 0, 0, 0, 0], ![15998, 842, 421, 0, 0]] i)))

def P421P0 : CertificateIrreducibleZModOfList' 421 5 2 8 [278, 317, 321, 0, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [112, 20, 100, 334, 365], [141, 371, 14, 346, 272], [223, 65, 128, 28, 219], [366, 385, 179, 134, 407], [0, 1]]
 g := ![![[42, 123, 108, 283, 347], [181, 317, 304, 246], [287, 9, 214, 406, 25], [152, 224, 415, 101], [117, 301, 22, 63], [263, 171, 317], [0, 1], []], ![[98, 279, 20, 177, 16, 372, 244, 76], [154, 46, 71, 347], [43, 210, 114, 181, 348, 130, 363, 267], [70, 36, 128, 118], [389, 322, 183, 77], [141, 256, 334, 7, 67, 77, 399, 211], [192, 145, 207, 152], [301, 258, 391, 398, 105, 114, 349, 362]], ![[321, 120, 347, 217, 323, 52, 359, 118], [209, 340, 70, 55], [270, 15, 167, 30, 155, 284, 211, 101], [60, 341, 199, 190], [388, 16, 128, 182], [147, 224, 344, 33, 245, 220, 8, 78], [281, 71, 261, 182], [36, 377, 93, 229, 174, 185, 361, 269]], ![[262, 56, 309, 147, 259, 417, 258, 53], [261, 56, 41, 100], [371, 329, 417, 91, 172, 270, 388, 379], [252, 97, 333, 26], [341, 33, 272, 104], [284, 405, 272, 313, 324, 17, 81, 228], [419, 412, 276, 404], [281, 377, 256, 332, 167, 163, 175, 351]], ![[288, 178, 54, 207, 87, 20, 296, 211], [256, 168, 394, 269], [169, 239, 409, 185, 260, 190, 416, 285], [392, 33, 416, 281], [82, 224, 51, 26], [31, 329, 201, 209, 86, 153, 406, 83], [41, 112, 399, 277], [269, 254, 383, 120, 145, 282, 65, 203]]]
 h' := ![![[112, 20, 100, 334, 365], [139, 338, 146, 262, 342], [204, 278, 155, 163, 81], [313, 93, 158, 209, 5], [125, 326, 75, 14, 90], [140, 22, 163, 210, 399], [0, 143, 104, 100], [0, 0, 0, 1], [0, 1]], ![[141, 371, 14, 346, 272], [216, 306, 154, 236, 122], [120, 272, 315, 274, 342], [188, 198, 49, 372, 398], [330, 243, 382, 246, 322], [230, 379, 93, 381, 224], [40, 340, 341, 363, 243], [152, 309, 420, 327, 346], [112, 20, 100, 334, 365]], ![[223, 65, 128, 28, 219], [254, 300, 68, 344, 325], [382, 380, 228, 305, 359], [112, 229, 76, 178, 49], [164, 5, 113, 371, 78], [44, 391, 237, 2, 32], [337, 107, 175, 121, 334], [299, 192, 221, 213, 389], [141, 371, 14, 346, 272]], ![[366, 385, 179, 134, 407], [20, 258, 59, 155, 118], [333, 337, 331, 19, 411], [284, 77, 228, 320, 321], [36, 111, 271, 396, 187], [178, 53, 334, 230, 374], [302, 165, 231, 404, 18], [194, 39, 78, 99, 180], [223, 65, 128, 28, 219]], ![[0, 1], [334, 61, 415, 266, 356], [61, 417, 234, 81, 70], [193, 245, 331, 184, 69], [352, 157, 1, 236, 165], [68, 418, 15, 19, 234], [272, 87, 412, 275, 247], [76, 302, 123, 202, 348], [366, 385, 179, 134, 407]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [177, 147, 413, 407], [], [], []]
 b := ![[], [226, 122, 340, 160, 105], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A421 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 421 1 where
 D := ![[278, 317, 321, 0, 0, 1]]; D' := ![[278, 317, 321, 0, 0, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8]
 n := ![5]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P421P0

def C4210 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A421.D 0) 421 where
  n := 5
  w := ![![421, 0, 0, 0, 0], ![15998, 842, 421, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K421 : KummerData 421 ![I421N0] ![13225450646101] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A421
  C := by
    intro i
    match i with
    | 0 => exact C4210
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 421 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp431 : Fact (Nat.Prime 431) := {out := by norm_num}

def I431N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![431, 0, 0, 0, 0], ![15947, 862, 431, 0, 0]] i)))

def P431P0 : CertificateIrreducibleZModOfList' 431 5 2 8 [227, 337, 331, 0, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [210, 355, 181, 259, 178], [376, 21, 52, 365, 66], [372, 268, 114, 35, 68], [335, 217, 84, 203, 119], [0, 1]]
 g := ![![[394, 356, 262, 82, 169], [205, 420, 138, 163, 361], [272, 257, 226, 193, 324], [365, 159, 204, 425, 246], [32, 207, 52, 157], [71, 267, 87], [0, 1], []], ![[262, 318, 142, 201, 82, 201, 261, 408], [32, 231, 304, 82, 101, 312, 183, 351], [367, 387, 53, 156, 313, 329, 180, 133], [379, 91, 39, 280, 360, 248, 376, 137], [72, 199, 180, 182], [177, 138, 331, 307, 251, 330, 71, 202], [246, 188, 110, 294], [48, 308, 228, 377, 128, 167, 179, 117]], ![[265, 83, 332, 15, 358, 114, 116, 243], [339, 19, 3, 359, 205, 350, 308, 358], [417, 108, 308, 159, 220, 406, 235, 307], [265, 60, 67, 196, 429, 12, 305, 288], [428, 410, 86, 38], [280, 91, 102, 219, 24, 71, 267, 329], [76, 102, 17, 20], [338, 239, 349, 310, 340, 337, 374, 19]], ![[18, 359, 7, 91, 293, 353, 183, 14], [256, 18, 165, 374, 399, 254, 305, 279], [384, 301, 338, 87, 117, 21, 17, 127], [81, 205, 98, 239, 256, 349, 142, 377], [374, 222, 7, 151], [176, 104, 251, 403, 249, 200, 357, 102], [241, 347, 309, 180], [86, 376, 192, 104, 155, 420, 214, 233]], ![[210, 197, 10, 85, 226, 412, 8, 108], [300, 116, 271, 117, 57, 176, 389, 24], [47, 79, 198, 189, 276, 354, 195, 50], [67, 336, 349, 66, 387, 277, 314, 159], [130, 379, 50, 229], [93, 351, 294, 32, 96, 181, 190, 289], [420, 219, 294, 276], [362, 83, 288, 32, 181, 182, 170, 380]]]
 h' := ![![[210, 355, 181, 259, 178], [13, 39, 307, 401, 13], [320, 250, 151, 370, 412], [328, 10, 175, 270, 413], [86, 124, 422, 132, 382], [261, 371, 381, 207, 73], [0, 204, 94, 100], [0, 0, 0, 1], [0, 1]], ![[376, 21, 52, 365, 66], [297, 273, 77, 183, 417], [251, 341, 70, 357, 374], [424, 18, 429, 376, 373], [217, 86, 276, 33, 89], [238, 319, 98, 167, 127], [81, 301, 414, 383, 258], [413, 107, 416, 65, 34], [210, 355, 181, 259, 178]], ![[372, 268, 114, 35, 68], [418, 325, 257, 318, 224], [63, 324, 58, 110, 381], [153, 203, 209, 242, 166], [149, 411, 212, 136, 292], [54, 82, 365, 102, 30], [277, 232, 288, 11, 245], [414, 4, 346, 3, 362], [376, 21, 52, 365, 66]], ![[335, 217, 84, 203, 119], [262, 60, 175, 147, 335], [414, 101, 248, 348, 183], [404, 188, 112, 215, 355], [109, 279, 373, 150, 208], [10, 194, 87, 119, 393], [126, 284, 304, 158, 367], [81, 122, 368, 210, 207], [372, 268, 114, 35, 68]], ![[0, 1], [135, 165, 46, 244, 304], [106, 277, 335, 108, 374], [0, 12, 368, 190, 417], [357, 393, 10, 411, 322], [211, 327, 362, 267, 239], [208, 272, 193, 210, 423], [254, 198, 163, 152, 259], [335, 217, 84, 203, 119]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [398, 366, 238, 39], [], [], []]
 b := ![[], [401, 182, 123, 168, 70], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A431 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 431 1 where
 D := ![[227, 337, 331, 0, 0, 1]]; D' := ![[227, 337, 331, 0, 0, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8]
 n := ![5]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P431P0

def C4310 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A431.D 0) 431 where
  n := 5
  w := ![![431, 0, 0, 0, 0], ![15947, 862, 431, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K431 : KummerData 431 ![I431N0] ![14872581271151] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A431
  C := by
    intro i
    match i with
    | 0 => exact C4310
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 431 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp433 : Fact (Nat.Prime 433) := {out := by norm_num}

def I433N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![433, 0, 0, 0, 0], ![68, 1, 0, 0, 0]] i)))

def I433N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![433, 0, 0, 0, 0], ![78, 1, 0, 0, 0]] i)))

def I433N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![433, 0, 0, 0, 0], ![216, 1, 0, 0, 0]] i)))

def I433N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![433, 0, 0, 0, 0], ![243, 71, 1, 0, 0]] i)))

def P433P0 : CertificateIrreducibleZModOfList' 433 1 2 8 [68, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [], [424], [27], [], [294, 365, 1]]]
 h' := ![![[0, 1], [1], [1], [432], [179], [329], [280], [359], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P433P1 : CertificateIrreducibleZModOfList' 433 1 2 8 [78, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [], [161], [153], [], [22, 355, 1]]]
 h' := ![![[0, 1], [1], [1], [1], [432], [190], [256], [16], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P433P2 : CertificateIrreducibleZModOfList' 433 1 2 8 [216, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [], [275], [235], [], [325, 217, 1]]]
 h' := ![![[0, 1], [1], [432], [179], [354], [334], [318], [379], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P433P3 : CertificateIrreducibleZModOfList' 433 2 2 8 [243, 71, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [362, 432], [0, 1]]
 g := ![![[403, 335], [363], [16], [408], [260, 192], [365, 274], [359], [362, 1]], ![[0, 98], [363], [16], [408], [51, 241], [396, 159], [359], [291, 432]]]
 h' := ![![[362, 432], [86, 50], [292, 128], [158, 4], [38, 404], [70, 25], [388, 131], [366, 35], [0, 1]], ![[0, 1], [0, 383], [297, 305], [307, 429], [365, 29], [27, 408], [180, 302], [46, 398], [362, 432]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [292]]
 b := ![[], [420, 146]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A433 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 433 4 where
 D := ![[68, 1], [78, 1], [216, 1], [243, 71, 1]]; D' := ![[68, 1], [78, 1], [216, 1], [243, 71, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8, 8, 8, 8]
 n := ![1, 1, 1, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P433P0
  | 1 => exact P433P1
  | 2 => exact P433P2
  | 3 => exact P433P3

def C4330 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A433.D 0) 433 where
  n := 1
  w := ![![433, 0, 0, 0, 0], ![68, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C4331 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A433.D 1) 433 where
  n := 1
  w := ![![433, 0, 0, 0, 0], ![78, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C4332 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A433.D 2) 433 where
  n := 1
  w := ![![433, 0, 0, 0, 0], ![216, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C4333 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A433.D 3) 433 where
  n := 2
  w := ![![433, 0, 0, 0, 0], ![243, 71, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K433 : KummerData 433 ![I433N0, I433N1, I433N2, I433N3] ![433, 433, 433, 187489] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A433
  C := by
    intro i
    match i with
    | 0 => exact C4330
    | 1 => exact C4331
    | 2 => exact C4332
    | 3 => exact C4333
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 433 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp439 : Fact (Nat.Prime 439) := {out := by norm_num}

def I439N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![439, 0, 0, 0, 0], ![353, 1, 0, 0, 0]] i)))

def I439N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![439, 0, 0, 0, 0], ![317, 221, 1, 0, 0]] i)))

def I439N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![439, 0, 0, 0, 0], ![38, 304, 1, 0, 0]] i)))

def P439P0 : CertificateIrreducibleZModOfList' 439 1 2 8 [353, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [342], [397], [], [319], [109], [], [372, 86, 1]]]
 h' := ![![[0, 1], [438], [339], [122], [216], [155], [391], [384], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P439P1 : CertificateIrreducibleZModOfList' 439 2 2 8 [317, 221, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [218, 438], [0, 1]]
 g := ![![[412, 102], [31, 360], [375, 424], [123], [392, 364], [383, 254], [320], [218, 1]], ![[259, 337], [369, 79], [178, 15], [123], [285, 75], [2, 185], [320], [436, 438]]]
 h' := ![![[218, 438], [270, 249], [94, 393], [370, 174], [412, 347], [192, 398], [94, 359], [256, 234], [0, 1]], ![[0, 1], [116, 190], [163, 46], [109, 265], [111, 92], [34, 41], [214, 80], [344, 205], [218, 438]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [319]]
 b := ![[], [394, 379]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P439P2 : CertificateIrreducibleZModOfList' 439 2 2 8 [38, 304, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [135, 438], [0, 1]]
 g := ![![[8, 104], [70, 32], [206, 44], [142], [258, 320], [31, 347], [224], [135, 1]], ![[0, 335], [0, 407], [0, 395], [142], [436, 119], [342, 92], [224], [270, 438]]]
 h' := ![![[135, 438], [413, 101], [74, 84], [116, 191], [293, 286], [139, 234], [435, 35], [138, 188], [0, 1]], ![[0, 1], [0, 338], [0, 355], [0, 248], [271, 153], [121, 205], [331, 404], [56, 251], [135, 438]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [83]]
 b := ![[], [162, 261]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A439 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 439 3 where
 D := ![[353, 1], [317, 221, 1], [38, 304, 1]]; D' := ![[353, 1], [317, 221, 1], [38, 304, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8, 8, 8]
 n := ![1, 2, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P439P0
  | 1 => exact P439P1
  | 2 => exact P439P2

def C4390 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A439.D 0) 439 where
  n := 1
  w := ![![439, 0, 0, 0, 0], ![353, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C4391 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A439.D 1) 439 where
  n := 2
  w := ![![439, 0, 0, 0, 0], ![317, 221, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C4392 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A439.D 2) 439 where
  n := 2
  w := ![![439, 0, 0, 0, 0], ![38, 304, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K439 : KummerData 439 ![I439N0, I439N1, I439N2] ![439, 192721, 192721] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A439
  C := by
    intro i
    match i with
    | 0 => exact C4390
    | 1 => exact C4391
    | 2 => exact C4392
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 439 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp443 : Fact (Nat.Prime 443) := {out := by norm_num}

def I443N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![443, 0, 0, 0, 0], ![438, 1, 0, 0, 0]] i)))

def I443N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![443, 0, 0, 0, 0], ![691, 2132, 10920, -3028, 22728]] i)))

def P443P0 : CertificateIrreducibleZModOfList' 443 1 2 8 [438, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [177], [], [36], [267], [224], [], [25, 5, 1]]]
 h' := ![![[0, 1], [442], [61], [180], [6], [234], [120], [125], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P443P1 : CertificateIrreducibleZModOfList' 443 4 2 8 [43, 25, 25, 5, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 221, 255, 192], [182, 408, 213, 167], [253, 256, 418, 84], [0, 1]]
 g := ![![[309, 168, 82, 126], [244, 42, 440, 123], [296, 177, 309], [297, 126, 42, 208], [328, 234, 389, 149], [315, 63, 68, 254], [0, 438, 1], []], ![[339, 392, 134, 53, 411, 137], [268, 261, 315, 436, 93, 369], [39, 282, 270], [86, 376, 350, 412, 244, 51], [140, 307, 350, 188, 256, 14], [401, 57, 178, 283, 189, 217], [203, 389, 151], [409, 429, 315, 43, 81, 77]], ![[6, 388, 173, 352, 178, 62], [124, 118, 35, 433, 296, 61], [126, 434, 17], [72, 412, 402, 365, 405, 27], [105, 243, 319, 18, 374, 47], [210, 105, 316, 80, 254, 58], [121, 58, 221], [389, 162, 350, 418, 376, 204]], ![[310, 97, 413, 121, 98, 158], [304, 231, 56, 289, 103, 394], [222, 191, 339], [276, 273, 401, 63, 135, 223], [61, 32, 121, 315, 17, 336], [293, 80, 280, 254, 427, 178], [336, 0, 231], [326, 235, 264, 428, 335, 413]]]
 h' := ![![[3, 221, 255, 192], [140, 401, 252, 353], [136, 87, 229, 218], [76, 315, 295, 75], [72, 248, 118, 151], [188, 48, 30, 329], [0, 215, 82, 100], [0, 0, 0, 1], [0, 1]], ![[182, 408, 213, 167], [182, 229, 305, 218], [144, 234, 296, 305], [436, 155, 419, 409], [7, 182, 415, 231], [154, 325, 436, 340], [37, 391, 380, 86], [160, 331, 412, 53], [3, 221, 255, 192]], ![[253, 256, 418, 84], [242, 125, 101, 425], [392, 129, 268, 24], [149, 420, 221, 367], [159, 188, 434, 157], [340, 302, 279, 219], [253, 393, 70, 171], [331, 116, 29, 211], [182, 408, 213, 167]], ![[0, 1], [306, 131, 228, 333], [409, 436, 93, 339], [274, 439, 394, 35], [135, 268, 362, 347], [394, 211, 141, 441], [352, 330, 354, 86], [127, 439, 2, 178], [253, 256, 418, 84]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [29, 57, 193], []]
 b := ![[], [], [368, 31, 387, 349], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A443 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 443 2 where
 D := ![[438, 1], [43, 25, 25, 5, 1]]; D' := ![[438, 1], [43, 25, 25, 5, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8, 8]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P443P0
  | 1 => exact P443P1

def C4430 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A443.D 0) 443 where
  n := 1
  w := ![![443, 0, 0, 0, 0], ![438, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C4431 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A443.D 1) 443 where
  n := 4
  w := ![![443, 0, 0, 0, 0], ![691, 2132, 10920, -3028, 22728]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K443 : KummerData 443 ![I443N0, I443N1] ![443, 38513670001] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A443
  C := by
    intro i
    match i with
    | 0 => exact C4430
    | 1 => exact C4431
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 443 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp449 : Fact (Nat.Prime 449) := {out := by norm_num}

def I449N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![449, 0, 0, 0, 0], ![16164, 898, 449, 0, 0]] i)))

def P449P0 : CertificateIrreducibleZModOfList' 449 5 2 8 [444, 373, 349, 0, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [129, 191, 292, 207, 185], [188, 376, 194, 388, 128], [428, 58, 85, 116, 38], [153, 272, 327, 187, 98], [0, 1]]
 g := ![![[385, 357, 352, 3, 207], [322, 80, 390, 371], [198, 54, 288, 67], [121, 65, 328, 426], [391, 116, 409, 9], [388, 41, 383, 122], [0, 0, 1], []], ![[432, 130, 370, 79, 375, 379, 360, 155], [313, 425, 442, 77], [10, 413, 322, 137], [81, 56, 259, 50], [378, 91, 166, 35], [431, 184, 201, 14], [115, 63, 284, 129, 368, 56, 372, 406], [65, 436, 2, 113, 28, 382, 310, 276]], ![[63, 36, 8, 380, 418, 446, 261, 122], [265, 384, 127, 268], [305, 79, 276, 9], [270, 42, 187, 305], [119, 302, 45, 328], [248, 353, 261, 335], [151, 358, 96, 416, 147, 387, 178, 440], [185, 129, 267, 343, 94, 221, 150, 322]], ![[142, 447, 180, 358, 89, 92, 344, 291], [416, 413, 6, 64], [92, 81, 84, 40], [299, 312, 203, 70], [139, 309, 134, 312], [316, 32, 8, 128], [420, 286, 278, 115, 264, 378, 284, 85], [135, 375, 1, 110, 345, 240, 81, 94]], ![[12, 385, 94, 37, 24, 123, 71, 441], [168, 194, 371, 258], [397, 85, 69, 72], [59, 389, 319, 181], [396, 334, 91, 169], [360, 272, 293, 295], [429, 89, 65, 24, 334, 230, 6, 335], [301, 88, 386, 197, 395, 290, 293, 88]]]
 h' := ![![[129, 191, 292, 207, 185], [425, 238, 307, 414, 109], [270, 425, 300, 311, 145], [316, 321, 176, 227, 327], [241, 143, 153, 426, 110], [144, 59, 278, 143, 3], [0, 0, 5, 76, 100], [0, 0, 0, 1], [0, 1]], ![[188, 376, 194, 388, 128], [186, 143, 0, 83, 252], [42, 46, 378, 77, 102], [428, 141, 301, 95, 290], [263, 134, 299, 285, 299], [436, 202, 253, 65, 22], [347, 415, 342, 269, 310], [345, 265, 207, 251, 204], [129, 191, 292, 207, 185]], ![[428, 58, 85, 116, 38], [233, 81, 127, 182, 412], [399, 350, 404, 222, 244], [391, 57, 115, 403, 446], [76, 56, 118, 204, 94], [231, 125, 219, 414, 288], [390, 303, 49, 292, 421], [397, 312, 126, 279, 16], [188, 376, 194, 388, 128]], ![[153, 272, 327, 187, 98], [376, 232, 359, 311, 80], [372, 86, 307, 168, 441], [19, 103, 259, 199, 104], [46, 152, 134, 59, 211], [344, 414, 304, 48, 123], [88, 115, 307, 232, 240], [394, 416, 0, 353, 169], [428, 58, 85, 116, 38]], ![[0, 1], [193, 204, 105, 357, 45], [253, 440, 407, 120, 415], [8, 276, 47, 423, 180], [179, 413, 194, 373, 184], [273, 98, 293, 228, 13], [291, 65, 195, 29, 276], [62, 354, 116, 14, 60], [153, 272, 327, 187, 98]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [231, 173, 258, 231], [], [], []]
 b := ![[], [2, 293, 109, 112, 57], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A449 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 449 1 where
 D := ![[444, 373, 349, 0, 0, 1]]; D' := ![[444, 373, 349, 0, 0, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8]
 n := ![5]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P449P0

def C4490 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A449.D 0) 449 where
  n := 5
  w := ![![449, 0, 0, 0, 0], ![16164, 898, 449, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K449 : KummerData 449 ![I449N0] ![18248690477249] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A449
  C := by
    intro i
    match i with
    | 0 => exact C4490
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 449 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp457 : Fact (Nat.Prime 457) := {out := by norm_num}

def I457N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![457, 0, 0, 0, 0], ![74, 1, 0, 0, 0]] i)))

def I457N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![457, 0, 0, 0, 0], ![90, 1, 0, 0, 0]] i)))

def I457N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![457, 0, 0, 0, 0], ![189, 1, 0, 0, 0]] i)))

def I457N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![457, 0, 0, 0, 0], ![123, 104, 1, 0, 0]] i)))

def P457P0 : CertificateIrreducibleZModOfList' 457 1 2 8 [74, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [256], [], [], [402], [449, 383, 1]]]
 h' := ![![[0, 1], [456], [348], [250], [441], [21], [414], [135], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P457P1 : CertificateIrreducibleZModOfList' 457 1 2 8 [90, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [205], [], [], [370], [331, 367, 1]]]
 h' := ![![[0, 1], [456], [109], [287], [112], [65], [61], [372], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P457P2 : CertificateIrreducibleZModOfList' 457 1 2 8 [189, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [292], [], [], [64], [75, 268, 1]]]
 h' := ![![[0, 1], [1], [456], [109], [76], [96], [243], [449], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P457P3 : CertificateIrreducibleZModOfList' 457 2 2 8 [123, 104, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [353, 456], [0, 1]]
 g := ![![[38, 343], [75], [14], [372, 453], [218], [9], [342, 220], [353, 1]], ![[12, 114], [75], [14], [331, 4], [218], [9], [312, 237], [249, 456]]]
 h' := ![![[353, 456], [393, 228], [43, 189], [401, 71], [285, 218], [291, 110], [435, 454], [453, 182], [0, 1]], ![[0, 1], [445, 229], [38, 268], [329, 386], [6, 239], [276, 347], [290, 3], [262, 275], [353, 456]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [88]]
 b := ![[], [3, 44]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A457 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 457 4 where
 D := ![[74, 1], [90, 1], [189, 1], [123, 104, 1]]; D' := ![[74, 1], [90, 1], [189, 1], [123, 104, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8, 8, 8, 8]
 n := ![1, 1, 1, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P457P0
  | 1 => exact P457P1
  | 2 => exact P457P2
  | 3 => exact P457P3

def C4570 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A457.D 0) 457 where
  n := 1
  w := ![![457, 0, 0, 0, 0], ![74, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C4571 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A457.D 1) 457 where
  n := 1
  w := ![![457, 0, 0, 0, 0], ![90, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C4572 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A457.D 2) 457 where
  n := 1
  w := ![![457, 0, 0, 0, 0], ![189, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C4573 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A457.D 3) 457 where
  n := 2
  w := ![![457, 0, 0, 0, 0], ![123, 104, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K457 : KummerData 457 ![I457N0, I457N1, I457N2, I457N3] ![457, 457, 457, 208849] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A457
  C := by
    intro i
    match i with
    | 0 => exact C4570
    | 1 => exact C4571
    | 2 => exact C4572
    | 3 => exact C4573
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 457 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp461 : Fact (Nat.Prime 461) := {out := by norm_num}

def I461N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![461, 0, 0, 0, 0], ![131, 1, 0, 0, 0]] i)))

def I461N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![461, 0, 0, 0, 0], ![237, 1, 0, 0, 0]] i)))

def I461N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![461, 0, 0, 0, 0], ![17, 192, 93, 2, 0]] i)))

def P461P0 : CertificateIrreducibleZModOfList' 461 1 2 8 [131, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [436], [125], [], [], [24], [104, 330, 1]]]
 h' := ![![[0, 1], [460], [48], [221], [215], [435], [83], [206], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P461P1 : CertificateIrreducibleZModOfList' 461 1 2 8 [237, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [319], [370], [], [], [67], [388, 224, 1]]]
 h' := ![![[0, 1], [1], [1], [361], [405], [74], [256], [244], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P461P2 : CertificateIrreducibleZModOfList' 461 3 2 8 [17, 191, 93, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [115, 208, 327], [253, 252, 134], [0, 1]]
 g := ![![[400, 55, 365], [74, 207], [131, 193, 67], [17, 424, 180], [428, 58], [380, 460], [445, 117, 351], [1]], ![[7, 228, 218, 42], [344, 45], [107, 343, 385, 363], [290, 168, 15, 382], [313, 336], [392, 130], [117, 421, 136, 396], [193, 373, 55, 316]], ![[10, 124, 146, 194], [265, 281], [359, 245, 227, 285], [438, 117, 381, 293], [277, 447], [58, 352], [17, 453, 299, 338], [348, 379, 14, 145]]]
 h' := ![![[115, 208, 327], [216, 244, 47], [78, 360, 395], [172, 206, 217], [141, 69, 258], [218, 339, 320], [272, 434, 413], [444, 270, 368], [0, 1]], ![[253, 252, 134], [109, 163, 354], [288, 391, 129], [119, 4, 342], [114, 19, 450], [156, 77, 178], [235, 224, 281], [443, 169, 314], [115, 208, 327]], ![[0, 1], [146, 54, 60], [243, 171, 398], [156, 251, 363], [44, 373, 214], [323, 45, 424], [159, 264, 228], [346, 22, 240], [253, 252, 134]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [332, 454], []]
 b := ![[], [444, 298, 141], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A461 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 461 3 where
 D := ![[131, 1], [237, 1], [17, 191, 93, 1]]; D' := ![[131, 1], [237, 1], [17, 191, 93, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8, 8, 8]
 n := ![1, 1, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P461P0
  | 1 => exact P461P1
  | 2 => exact P461P2

def C4610 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A461.D 0) 461 where
  n := 1
  w := ![![461, 0, 0, 0, 0], ![131, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C4611 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A461.D 1) 461 where
  n := 1
  w := ![![461, 0, 0, 0, 0], ![237, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C4612 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A461.D 2) 461 where
  n := 3
  w := ![![461, 0, 0, 0, 0], ![17, 192, 93, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K461 : KummerData 461 ![I461N0, I461N1, I461N2] ![461, 461, 97972181] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A461
  C := by
    intro i
    match i with
    | 0 => exact C4610
    | 1 => exact C4611
    | 2 => exact C4612
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 461 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp463 : Fact (Nat.Prime 463) := {out := by norm_num}

def I463N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![463, 0, 0, 0, 0], ![76, 1, 0, 0, 0]] i)))

def I463N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![463, 0, 0, 0, 0], ![222, 1, 0, 0, 0]] i)))

def I463N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![463, 0, 0, 0, 0], ![349, 1, 0, 0, 0]] i)))

def I463N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![463, 0, 0, 0, 0], ![26, 279, 1, 0, 0]] i)))

def P463P0 : CertificateIrreducibleZModOfList' 463 1 2 8 [76, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [67], [313], [370], [], [], [389], [220, 387, 1]]]
 h' := ![![[0, 1], [1], [288], [123], [36], [457], [68], [411], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P463P1 : CertificateIrreducibleZModOfList' 463 1 2 8 [222, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [73], [124], [133], [], [], [376], [206, 241, 1]]]
 h' := ![![[0, 1], [462], [252], [106], [194], [293], [331], [105], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P463P2 : CertificateIrreducibleZModOfList' 463 1 2 8 [349, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [264], [357], [370], [], [], [358], [32, 114, 1]]]
 h' := ![![[0, 1], [1], [417], [47], [36], [457], [68], [407], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P463P3 : CertificateIrreducibleZModOfList' 463 2 2 8 [26, 279, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [184, 462], [0, 1]]
 g := ![![[171, 236], [169, 29], [208, 264], [370, 441], [270], [389], [133, 35], [184, 1]], ![[73, 227], [412, 434], [169, 199], [26, 22], [270], [389], [91, 428], [368, 462]]]
 h' := ![![[184, 462], [236, 390], [148, 347], [103, 417], [446, 442], [398, 393], [246, 52], [309, 31], [0, 1]], ![[0, 1], [231, 73], [102, 116], [436, 46], [286, 21], [19, 70], [91, 411], [457, 432], [184, 462]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [138]]
 b := ![[], [134, 69]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A463 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 463 4 where
 D := ![[76, 1], [222, 1], [349, 1], [26, 279, 1]]; D' := ![[76, 1], [222, 1], [349, 1], [26, 279, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8, 8, 8, 8]
 n := ![1, 1, 1, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P463P0
  | 1 => exact P463P1
  | 2 => exact P463P2
  | 3 => exact P463P3

def C4630 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A463.D 0) 463 where
  n := 1
  w := ![![463, 0, 0, 0, 0], ![76, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C4631 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A463.D 1) 463 where
  n := 1
  w := ![![463, 0, 0, 0, 0], ![222, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C4632 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A463.D 2) 463 where
  n := 1
  w := ![![463, 0, 0, 0, 0], ![349, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C4633 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A463.D 3) 463 where
  n := 2
  w := ![![463, 0, 0, 0, 0], ![26, 279, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K463 : KummerData 463 ![I463N0, I463N1, I463N2, I463N3] ![463, 463, 463, 214369] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A463
  C := by
    intro i
    match i with
    | 0 => exact C4630
    | 1 => exact C4631
    | 2 => exact C4632
    | 3 => exact C4633
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 463 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


lemma PB18792I9_primes (p : ℕ) :
  p ∈ Set.range ![421, 431, 433, 439, 443, 449, 457, 461, 463] ↔ Nat.Prime p ∧ 419 < p ∧ p ≤ 463 := by
  rw [← List.mem_ofFn']
  convert primes_range 419 463 (by omega)
  decide

def PB18792I9 : PrimesBelowBoundCertificateInterval O 419 463 18792 where
  m := 9
  g := ![1, 1, 4, 3, 2, 1, 4, 3, 4]
  P := ![421, 431, 433, 439, 443, 449, 457, 461, 463]
  hP := PB18792I9_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I421N0]
    · exact ![I431N0]
    · exact ![I433N0, I433N1, I433N2, I433N3]
    · exact ![I439N0, I439N1, I439N2]
    · exact ![I443N0, I443N1]
    · exact ![I449N0]
    · exact ![I457N0, I457N1, I457N2, I457N3]
    · exact ![I461N0, I461N1, I461N2]
    · exact ![I463N0, I463N1, I463N2, I463N3]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · convert (containsPrimesAbove_of_KummerData K421) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K431) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K433) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K439) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K443) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K449) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K457) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K461) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K463) <;> rfl
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![13225450646101]
    · exact ![14872581271151]
    · exact ![433, 433, 433, 187489]
    · exact ![439, 192721, 192721]
    · exact ![443, 38513670001]
    · exact ![18248690477249]
    · exact ![457, 457, 457, 208849]
    · exact ![461, 461, 97972181]
    · exact ![463, 463, 463, 214369]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact (card_quot_of_KummerData K421)
    · exact (card_quot_of_KummerData K431)
    · exact (card_quot_of_KummerData K433)
    · exact (card_quot_of_KummerData K439)
    · exact (card_quot_of_KummerData K443)
    · exact (card_quot_of_KummerData K449)
    · exact (card_quot_of_KummerData K457)
    · exact (card_quot_of_KummerData K461)
    · exact (card_quot_of_KummerData K463)
  β := ![I433N0, I433N1, I433N2, I439N0, I443N0, I457N0, I457N1, I457N2, I461N0, I461N1, I463N0, I463N1, I463N2]
  Il := ![[], [], [I433N0, I433N1, I433N2], [I439N0], [I443N0], [], [I457N0, I457N1, I457N2], [I461N0, I461N1], [I463N0, I463N1, I463N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
