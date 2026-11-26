
import IdealArithmetic.Examples.NF5_1_91125000000_1_K.RI5_1_91125000000_1_K
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 

instance hp467 : Fact (Nat.Prime 467) := {out := by norm_num}

def I467N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![467, 0, 0, 0, 0], ![131, 1, 0, 0, 0]] i)))

def I467N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![467, 0, 0, 0, 0], ![995, 2852, 11244, -2366, 22728]] i)))

def P467P0 : CertificateIrreducibleZModOfList' 467 1 2 8 [131, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [385], [], [], [123], [], [341], [349, 336, 1]]]
 h' := ![![[0, 1], [1], [151], [119], [232], [236], [161], [47], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P467P1 : CertificateIrreducibleZModOfList' 467 4 2 8 [347, 414, 349, 336, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [416, 284, 460, 319], [51, 365, 46, 463], [131, 284, 428, 152], [0, 1]]
 g := ![![[128, 30, 185, 209], [65, 237, 385, 199], [77, 359, 299], [415, 442, 356], [151, 290, 12, 436], [202, 274, 186], [100, 0, 131, 1], []], ![[375, 98, 165, 316, 31, 207], [444, 444, 328, 443, 249, 229], [257, 29, 448], [115, 398, 90], [104, 211, 361, 21, 394, 172], [339, 190, 23], [89, 434, 130, 128, 92, 351], [409, 175, 256, 187, 115, 122]], ![[38, 199, 121, 419, 363, 178], [266, 94, 344, 203, 435, 460], [125, 162, 108], [126, 410, 394], [365, 284, 411, 157, 462, 105], [346, 288, 301], [341, 69, 436, 270, 190, 257], [66, 34, 416, 242, 362, 403]], ![[250, 381, 15, 208, 264, 149], [328, 162, 34, 330, 465, 175], [74, 213, 83], [241, 305, 462], [339, 52, 112, 272, 398, 95], [4, 312, 213], [167, 358, 386, 169, 241, 366], [228, 186, 64, 56, 306, 435]]]
 h' := ![![[416, 284, 460, 319], [328, 276, 38, 441], [239, 290, 251, 427], [74, 2, 396, 247], [374, 426, 86, 193], [39, 96, 417, 48], [325, 163, 434, 82], [0, 0, 0, 1], [0, 1]], ![[51, 365, 46, 463], [303, 208, 4, 31], [207, 175, 135, 76], [242, 268, 416, 424], [61, 445, 178, 435], [87, 27, 265, 248], [6, 341, 95, 81], [22, 317, 119, 320], [416, 284, 460, 319]], ![[131, 284, 428, 152], [396, 41, 280, 242], [109, 74, 397, 207], [204, 116, 45, 405], [106, 226, 269, 101], [465, 403, 225, 18], [173, 457, 213, 146], [4, 435, 292, 400], [51, 365, 46, 463]], ![[0, 1], [256, 409, 145, 220], [448, 395, 151, 224], [446, 81, 77, 325], [389, 304, 401, 205], [172, 408, 27, 153], [240, 440, 192, 158], [227, 182, 56, 213], [131, 284, 428, 152]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [454, 193, 296], []]
 b := ![[], [], [61, 225, 195, 74], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A467 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 467 2 where
 D := ![[131, 1], [347, 414, 349, 336, 1]]; D' := ![[131, 1], [347, 414, 349, 336, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8, 8]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P467P0
  | 1 => exact P467P1

def C4670 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A467.D 0) 467 where
  n := 1
  w := ![![467, 0, 0, 0, 0], ![131, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C4671 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A467.D 1) 467 where
  n := 4
  w := ![![467, 0, 0, 0, 0], ![995, 2852, 11244, -2366, 22728]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K467 : KummerData 467 ![I467N0, I467N1] ![467, 47562811921] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A467
  C := by
    intro i
    match i with
    | 0 => exact C4670
    | 1 => exact C4671
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 467 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp479 : Fact (Nat.Prime 479) := {out := by norm_num}

def I479N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![479, 0, 0, 0, 0], ![15807, 958, 479, 0, 0]] i)))

def P479P0 : CertificateIrreducibleZModOfList' 479 5 2 8 [87, 433, 379, 0, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [57, 75, 27, 255, 309], [22, 272, 453, 200, 220], [459, 416, 88, 219, 60], [420, 194, 390, 284, 369], [0, 1]]
 g := ![![[148, 67, 352, 299, 343], [299, 17, 310, 36, 445], [191, 206, 392, 162, 210], [192, 154, 202, 184, 50], [256, 325, 244, 35, 214], [466, 44, 99, 420], [0, 0, 1], []], ![[334, 77, 129, 413, 326, 117, 192, 77], [328, 44, 427, 366, 234, 456, 431, 181], [177, 422, 403, 358, 379, 90, 271, 169], [456, 388, 41, 333, 221, 144, 339, 256], [330, 275, 234, 16, 32, 4, 291, 343], [170, 91, 295, 61], [227, 10, 181, 167, 428, 295, 17, 271], [167, 30, 225, 227, 67, 363, 255, 103]], ![[190, 110, 367, 385, 211, 424, 126, 355], [235, 172, 366, 372, 356, 198, 262, 61], [436, 340, 347, 20, 202, 364, 451, 60], [423, 218, 30, 384, 97, 353, 455, 432], [157, 431, 328, 1, 388, 79, 392, 393], [160, 110, 124, 169], [109, 382, 394, 16, 45, 227, 365, 211], [278, 63, 276, 113, 427, 193, 146, 309]], ![[74, 160, 226, 154, 414, 461, 430, 466], [375, 404, 46, 272, 126, 154, 280, 92], [450, 405, 203, 147, 305, 115, 139, 107], [342, 117, 447, 52, 399, 155, 116, 103], [0, 178, 358, 262, 387, 410, 125, 146], [472, 355, 164, 373], [219, 342, 297, 131, 48, 135, 424, 412], [390, 303, 110, 149, 264, 27, 377, 450]], ![[153, 39, 287, 185, 109, 240, 203, 215], [26, 404, 151, 46, 288, 182, 32, 473], [210, 372, 382, 354, 457, 387, 318, 464], [87, 66, 36, 442, 457, 272, 425, 78], [141, 94, 215, 335, 91, 111, 177, 188], [153, 186, 169, 414], [403, 167, 11, 171, 17, 282, 304, 347], [430, 429, 241, 189, 223, 268, 162, 141]]]
 h' := ![![[57, 75, 27, 255, 309], [332, 170, 253, 148, 213], [148, 333, 280, 155, 133], [61, 346, 142, 294, 230], [241, 18, 129, 4, 23], [173, 364, 254, 196, 385], [0, 0, 392, 46, 100], [0, 0, 0, 1], [0, 1]], ![[22, 272, 453, 200, 220], [112, 115, 177, 302, 374], [269, 322, 29, 156, 63], [367, 320, 63, 53, 120], [446, 81, 14, 402, 74], [71, 468, 369, 224, 87], [62, 302, 447, 346, 260], [140, 353, 183, 53, 380], [57, 75, 27, 255, 309]], ![[459, 416, 88, 219, 60], [113, 273, 96, 197, 251], [44, 117, 69, 38, 337], [96, 34, 442, 199, 272], [331, 412, 60, 145, 379], [41, 186, 261, 106, 275], [178, 405, 270, 189, 13], [353, 370, 87, 157, 327], [22, 272, 453, 200, 220]], ![[420, 194, 390, 284, 369], [284, 326, 411, 27, 422], [318, 248, 252, 61, 89], [229, 267, 232, 439, 291], [102, 9, 140, 75, 377], [222, 42, 226, 277, 249], [209, 218, 303, 356, 159], [222, 283, 401, 132, 275], [459, 416, 88, 219, 60]], ![[0, 1], [107, 74, 21, 284, 177], [41, 417, 328, 69, 336], [263, 470, 79, 452, 45], [248, 438, 136, 332, 105], [189, 377, 327, 155, 441], [137, 33, 25, 21, 426], [64, 431, 287, 136, 455], [420, 194, 390, 284, 369]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59, 304, 97, 463], [], [], []]
 b := ![[], [473, 62, 266, 347, 462], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A479 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 479 1 where
 D := ![[87, 433, 379, 0, 0, 1]]; D' := ![[87, 433, 379, 0, 0, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8]
 n := ![5]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P479P0

def C4790 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A479.D 0) 479 where
  n := 5
  w := ![![479, 0, 0, 0, 0], ![15807, 958, 479, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K479 : KummerData 479 ![I479N0] ![25216079618399] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A479
  C := by
    intro i
    match i with
    | 0 => exact C4790
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 479 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp487 : Fact (Nat.Prime 487) := {out := by norm_num}

def I487N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![487, 0, 0, 0, 0], ![408, 1, 0, 0, 0]] i)))

def I487N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![487, 0, 0, 0, 0], ![810, 2276, 11292, -2880, 22728]] i)))

def P487P0 : CertificateIrreducibleZModOfList' 487 1 2 8 [408, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [450], [143], [], [], [444], [39], [397, 79, 1]]]
 h' := ![![[0, 1], [486], [96], [282], [144], [12], [159], [195], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P487P1 : CertificateIrreducibleZModOfList' 487 4 2 8 [162, 95, 397, 79, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [390, 140, 174, 89], [377, 403, 108, 10], [128, 430, 205, 388], [0, 1]]
 g := ![![[196, 125, 73, 477], [391, 360, 474, 81], [53, 220, 308, 138], [94, 177, 58], [448, 278, 481], [410, 482, 374, 30], [100, 0, 408, 1], []], ![[107, 470, 164, 76, 449, 286], [325, 81, 115, 27, 172, 304], [178, 69, 348, 177, 195, 463], [474, 382, 354], [201, 356, 135], [336, 55, 318, 416, 36, 220], [230, 190, 162, 58, 430, 2], [352, 102, 63, 388, 414, 280]], ![[396, 332, 79, 312, 342, 418], [0, 387, 160, 17, 61, 317], [19, 68, 161, 297, 6, 46], [179, 113, 332], [287, 336, 21], [316, 278, 112, 427, 351, 160], [304, 476, 439, 482, 161, 27], [461, 308, 115, 450, 152, 26]], ![[311, 210, 471, 65, 370, 303], [458, 32, 115, 327, 339, 91], [71, 123, 176, 127, 354, 134], [225, 329, 459], [51, 109, 139], [13, 125, 305, 123, 55, 369], [471, 181, 104, 340, 454, 49], [278, 145, 113, 378, 324, 292]]]
 h' := ![![[390, 140, 174, 89], [455, 245, 384, 351], [180, 447, 24, 478], [56, 181, 68, 462], [267, 462, 428, 360], [299, 416, 92, 433], [358, 240, 370, 417], [0, 0, 0, 1], [0, 1]], ![[377, 403, 108, 10], [276, 251, 283, 217], [278, 291, 114, 456], [314, 54, 330, 248], [97, 215, 99, 458], [417, 445, 39, 185], [364, 217, 418, 465], [407, 459, 343, 227], [390, 140, 174, 89]], ![[128, 430, 205, 388], [245, 369, 325, 373], [142, 335, 484, 38], [263, 354, 292, 383], [125, 55, 284, 229], [29, 234, 400, 316], [471, 113, 86, 4], [287, 207, 335, 21], [377, 403, 108, 10]], ![[0, 1], [308, 109, 469, 33], [112, 388, 352, 2], [475, 385, 284, 368], [467, 242, 163, 414], [391, 366, 443, 40], [411, 404, 100, 88], [385, 308, 296, 238], [128, 430, 205, 388]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [312, 77, 195], []]
 b := ![[], [], [154, 255, 26, 224], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A487 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 487 2 where
 D := ![[408, 1], [162, 95, 397, 79, 1]]; D' := ![[408, 1], [162, 95, 397, 79, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8, 8]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P487P0
  | 1 => exact P487P1

def C4870 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A487.D 0) 487 where
  n := 1
  w := ![![487, 0, 0, 0, 0], ![408, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C4871 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A487.D 1) 487 where
  n := 4
  w := ![![487, 0, 0, 0, 0], ![810, 2276, 11292, -2880, 22728]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K487 : KummerData 487 ![I487N0, I487N1] ![487, 56249134561] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A487
  C := by
    intro i
    match i with
    | 0 => exact C4870
    | 1 => exact C4871
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 487 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp491 : Fact (Nat.Prime 491) := {out := by norm_num}

def I491N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![491, 0, 0, 0, 0], ![16203, 982, 491, 0, 0]] i)))

def P491P0 : CertificateIrreducibleZModOfList' 491 5 2 8 [483, 457, 391, 0, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [110, 304, 45, 362, 100], [84, 354, 398, 249, 343], [359, 448, 473, 18, 124], [429, 366, 66, 353, 415], [0, 1]]
 g := ![![[382, 287, 485, 39, 403], [79, 221, 16, 134, 260], [342, 4, 303, 106], [453, 55, 482, 427, 42], [262, 91, 74, 79], [257, 377, 301, 417, 180], [0, 0, 1], []], ![[217, 447, 84, 151, 152, 249, 397, 153], [284, 15, 228, 57, 127, 243, 224, 16], [192, 221, 472, 38], [202, 189, 165, 68, 368, 135, 451, 400], [38, 448, 371, 44], [466, 5, 0, 90, 364, 261, 363, 419], [29, 305, 169, 43, 178, 297, 170, 422], [205, 62, 307, 465, 277, 53, 62, 324]], ![[81, 199, 318, 381, 328, 433, 216, 368], [156, 268, 217, 295, 282, 281, 52, 82], [163, 203, 465, 470], [109, 109, 353, 80, 438, 211, 331, 47], [202, 471, 52, 107], [1, 460, 238, 209, 135, 457, 402, 421], [142, 3, 41, 118, 299, 415, 227, 34], [411, 242, 37, 185, 126, 223, 204, 281]], ![[114, 269, 434, 30, 358, 211, 403, 269], [329, 4, 194, 183, 270, 9, 378, 44], [105, 91, 35, 206], [26, 29, 347, 159, 114, 423, 426, 240], [382, 432, 277, 106], [269, 3, 440, 138, 148, 386, 257, 277], [85, 225, 316, 29, 188, 196, 246, 302], [252, 363, 274, 299, 327, 210, 23, 71]], ![[470, 353, 184, 221, 453, 374, 453, 215], [228, 19, 348, 94, 479, 234, 117, 33], [168, 413, 90, 419], [232, 379, 325, 84, 6, 283, 487, 467], [342, 281, 404, 226], [61, 263, 483, 416, 114, 247, 160, 46], [84, 79, 141, 86, 383, 345, 259, 451], [134, 48, 109, 403, 186, 481, 397, 469]]]
 h' := ![![[110, 304, 45, 362, 100], [141, 128, 43, 205, 145], [389, 295, 176, 450, 178], [187, 265, 296, 118, 149], [249, 188, 261, 1, 459], [92, 461, 173, 206, 55], [0, 0, 8, 34, 100], [0, 0, 0, 1], [0, 1]], ![[84, 354, 398, 249, 343], [406, 34, 318, 352, 24], [235, 406, 301, 212, 196], [139, 286, 369, 117, 23], [350, 399, 195, 43, 489], [111, 389, 211, 259, 432], [176, 229, 315, 369, 351], [66, 76, 254, 421, 17], [110, 304, 45, 362, 100]], ![[359, 448, 473, 18, 124], [71, 251, 140, 109, 381], [210, 128, 432, 270, 217], [403, 146, 333, 253, 31], [375, 470, 274, 124, 378], [270, 23, 109, 148, 458], [320, 68, 132, 144, 481], [409, 28, 304, 60, 270], [84, 354, 398, 249, 343]], ![[429, 366, 66, 353, 415], [464, 18, 371, 1, 399], [36, 259, 118, 339, 425], [81, 263, 164, 387, 361], [152, 442, 210, 431, 413], [459, 204, 81, 294, 342], [355, 423, 16, 363, 58], [419, 281, 191, 316, 362], [359, 448, 473, 18, 124]], ![[0, 1], [319, 60, 110, 315, 33], [217, 385, 446, 202, 457], [306, 22, 311, 107, 418], [486, 465, 42, 383, 225], [68, 396, 408, 75, 186], [363, 262, 20, 72, 483], [388, 106, 233, 184, 333], [429, 366, 66, 353, 415]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54, 87, 178, 217], [], [], []]
 b := ![[], [303, 157, 86, 463, 425], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A491 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 491 1 where
 D := ![[483, 457, 391, 0, 0, 1]]; D' := ![[483, 457, 391, 0, 0, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8]
 n := ![5]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P491P0

def C4910 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A491.D 0) 491 where
  n := 5
  w := ![![491, 0, 0, 0, 0], ![16203, 982, 491, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K491 : KummerData 491 ![I491N0] ![28536943843451] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A491
  C := by
    intro i
    match i with
    | 0 => exact C4910
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 491 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp499 : Fact (Nat.Prime 499) := {out := by norm_num}

def I499N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![499, 0, 0, 0, 0], ![85, 1, 0, 0, 0]] i)))

def I499N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![499, 0, 0, 0, 0], ![368, 59, 1, 0, 0]] i)))

def I499N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![499, 0, 0, 0, 0], ![383, 355, 1, 0, 0]] i)))

def P499P0 : CertificateIrreducibleZModOfList' 499 1 2 8 [85, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [317], [], [], [451], [480], [277], [239, 414, 1]]]
 h' := ![![[0, 1], [1], [215], [259], [88], [118], [407], [144], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P499P1 : CertificateIrreducibleZModOfList' 499 2 2 8 [368, 59, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [440, 498], [0, 1]]
 g := ![![[270, 189], [283, 414], [446], [358], [28, 320], [205, 211], [138, 189], [440, 1]], ![[97, 310], [308, 85], [446], [358], [110, 179], [231, 288], [464, 310], [381, 498]]]
 h' := ![![[440, 498], [147, 380], [290, 188], [178, 38], [175, 146], [408, 99], [114, 305], [255, 119], [0, 1]], ![[0, 1], [182, 119], [176, 311], [431, 461], [44, 353], [56, 400], [83, 194], [220, 380], [440, 498]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [230]]
 b := ![[], [149, 115]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P499P2 : CertificateIrreducibleZModOfList' 499 2 2 8 [383, 355, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [144, 498], [0, 1]]
 g := ![![[397, 337], [316, 257], [281], [444], [357, 224], [396, 167], [381, 258], [144, 1]], ![[23, 162], [398, 242], [281], [444], [178, 275], [492, 332], [108, 241], [288, 498]]]
 h' := ![![[144, 498], [229, 395], [120, 238], [132, 237], [494, 332], [28, 366], [284, 243], [237, 393], [0, 1]], ![[0, 1], [223, 104], [460, 261], [328, 262], [398, 167], [337, 133], [346, 256], [442, 106], [144, 498]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [433]]
 b := ![[], [380, 466]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A499 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 499 3 where
 D := ![[85, 1], [368, 59, 1], [383, 355, 1]]; D' := ![[85, 1], [368, 59, 1], [383, 355, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8, 8, 8]
 n := ![1, 2, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P499P0
  | 1 => exact P499P1
  | 2 => exact P499P2

def C4990 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A499.D 0) 499 where
  n := 1
  w := ![![499, 0, 0, 0, 0], ![85, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C4991 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A499.D 1) 499 where
  n := 2
  w := ![![499, 0, 0, 0, 0], ![368, 59, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C4992 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A499.D 2) 499 where
  n := 2
  w := ![![499, 0, 0, 0, 0], ![383, 355, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K499 : KummerData 499 ![I499N0, I499N1, I499N2] ![499, 249001, 249001] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A499
  C := by
    intro i
    match i with
    | 0 => exact C4990
    | 1 => exact C4991
    | 2 => exact C4992
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 499 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp503 : Fact (Nat.Prime 503) := {out := by norm_num}

def I503N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![503, 0, 0, 0, 0], ![145, 151, 1, 0, 0]] i)))

def I503N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![503, 0, 0, 0, 0], ![13, 22, 352, 2, 0]] i)))

def P503P0 : CertificateIrreducibleZModOfList' 503 2 2 8 [145, 151, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [352, 502], [0, 1]]
 g := ![![[341, 392], [455, 23], [39, 4], [416], [141, 25], [109, 301], [414, 441], [352, 1]], ![[0, 111], [0, 480], [441, 499], [416], [390, 478], [431, 202], [219, 62], [201, 502]]]
 h' := ![![[352, 502], [421, 186], [381, 289], [35, 2], [178, 411], [291, 5], [330, 130], [266, 21], [0, 1]], ![[0, 1], [0, 317], [0, 214], [236, 501], [489, 92], [39, 498], [317, 373], [113, 482], [352, 502]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [486]]
 b := ![[], [490, 243]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P503P1 : CertificateIrreducibleZModOfList' 503 3 2 8 [13, 21, 352, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [141, 154, 78], [10, 348, 425], [0, 1]]
 g := ![![[260, 11, 8], [245, 325, 122], [400, 469, 131], [477, 400], [489, 389, 488], [208, 19, 131], [32, 113, 166], [1]], ![[409, 100, 315, 72], [335, 370, 138, 77], [213, 159, 118, 42], [250, 216], [210, 322, 8, 370], [325, 194, 91, 350], [232, 461, 341, 197], [398, 377, 16, 223]], ![[106, 41, 411, 209], [426, 418, 113, 307], [338, 374, 365, 439], [172, 236], [56, 306, 12, 127], [312, 411, 452, 102], [310, 233, 397, 477], [458, 252, 343, 280]]]
 h' := ![![[141, 154, 78], [336, 416, 189], [333, 372, 478], [264, 379, 159], [182, 275, 20], [314, 439, 50], [87, 40, 344], [490, 482, 151], [0, 1]], ![[10, 348, 425], [198, 90, 135], [194, 110, 196], [409, 323, 390], [248, 168, 242], [399, 379, 336], [170, 322, 100], [361, 61, 107], [141, 154, 78]], ![[0, 1], [210, 500, 179], [226, 21, 332], [105, 304, 457], [360, 60, 241], [286, 188, 117], [412, 141, 59], [76, 463, 245], [10, 348, 425]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [361, 498], []]
 b := ![[], [352, 214, 71], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A503 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 503 2 where
 D := ![[145, 151, 1], [13, 21, 352, 1]]; D' := ![[145, 151, 1], [13, 21, 352, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8, 8]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P503P0
  | 1 => exact P503P1

def C5030 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A503.D 0) 503 where
  n := 2
  w := ![![503, 0, 0, 0, 0], ![145, 151, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C5031 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A503.D 1) 503 where
  n := 3
  w := ![![503, 0, 0, 0, 0], ![13, 22, 352, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K503 : KummerData 503 ![I503N0, I503N1] ![253009, 127263527] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A503
  C := by
    intro i
    match i with
    | 0 => exact C5030
    | 1 => exact C5031
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 503 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp509 : Fact (Nat.Prime 509) := {out := by norm_num}

def I509N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![509, 0, 0, 0, 0], ![447, 1, 0, 0, 0]] i)))

def I509N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![509, 0, 0, 0, 0], ![101, 197, 1, 0, 0]] i)))

def I509N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![509, 0, 0, 0, 0], ![307, 374, 1, 0, 0]] i)))

def P509P0 : CertificateIrreducibleZModOfList' 509 1 2 8 [447, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [156], [224], [376], [441], [222], [281, 62, 1]]]
 h' := ![![[0, 1], [1], [1], [145], [407], [365], [21], [116], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P509P1 : CertificateIrreducibleZModOfList' 509 2 2 8 [101, 197, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [312, 508], [0, 1]]
 g := ![![[390, 126], [480], [47, 179], [375, 253], [296, 9], [325, 353], [207, 67], [312, 1]], ![[0, 383], [480], [414, 330], [416, 256], [50, 500], [8, 156], [242, 442], [115, 508]]]
 h' := ![![[312, 508], [454, 178], [343, 55], [300, 237], [135, 235], [260, 3], [471, 380], [46, 24], [0, 1]], ![[0, 1], [0, 331], [197, 454], [439, 272], [159, 274], [178, 506], [434, 129], [408, 485], [312, 508]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [478]]
 b := ![[], [382, 239]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P509P2 : CertificateIrreducibleZModOfList' 509 2 2 8 [307, 374, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [135, 508], [0, 1]]
 g := ![![[361, 49], [24], [76, 84], [164, 138], [93, 394], [78, 100], [185, 429], [135, 1]], ![[359, 460], [24], [218, 425], [470, 371], [347, 115], [344, 409], [74, 80], [270, 508]]]
 h' := ![![[135, 508], [374, 502], [82, 64], [43, 307], [462, 34], [486, 258], [213, 499], [293, 103], [0, 1]], ![[0, 1], [447, 7], [69, 445], [259, 202], [471, 475], [195, 251], [390, 10], [455, 406], [135, 508]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [397]]
 b := ![[], [217, 453]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A509 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 509 3 where
 D := ![[447, 1], [101, 197, 1], [307, 374, 1]]; D' := ![[447, 1], [101, 197, 1], [307, 374, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8, 8, 8]
 n := ![1, 2, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P509P0
  | 1 => exact P509P1
  | 2 => exact P509P2

def C5090 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A509.D 0) 509 where
  n := 1
  w := ![![509, 0, 0, 0, 0], ![447, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C5091 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A509.D 1) 509 where
  n := 2
  w := ![![509, 0, 0, 0, 0], ![101, 197, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C5092 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A509.D 2) 509 where
  n := 2
  w := ![![509, 0, 0, 0, 0], ![307, 374, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K509 : KummerData 509 ![I509N0, I509N1, I509N2] ![509, 259081, 259081] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A509
  C := by
    intro i
    match i with
    | 0 => exact C5090
    | 1 => exact C5091
    | 2 => exact C5092
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 509 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp521 : Fact (Nat.Prime 521) := {out := by norm_num}

def I521N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![521, 0, 0, 0, 0], ![445, 1, 0, 0, 0]] i)))

def I521N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![521, 0, 0, 0, 0], ![447, 1, 0, 0, 0]] i)))

def I521N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![521, 0, 0, 0, 0], ![181, 205, 150, 2, 0]] i)))

def P521P0 : CertificateIrreducibleZModOfList' 521 1 2 9 [445, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [20], [], [], [], [], [76, 1]]]
 h' := ![![[0, 1], [520], [286], [478], [123], [464], [355], [462], [45], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P521P1 : CertificateIrreducibleZModOfList' 521 1 2 9 [447, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [320], [], [], [], [], [74, 1]]]
 h' := ![![[0, 1], [1], [520], [235], [29], [302], [101], [421], [266], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P521P2 : CertificateIrreducibleZModOfList' 521 3 2 9 [181, 204, 150, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [237, 112, 128], [134, 408, 393], [0, 1]]
 g := ![![[465, 318, 295], [470, 336], [405, 84], [291, 141, 325], [186, 231], [310, 290], [95, 508], [371, 1], []], ![[181, 115, 500, 353], [414, 100], [435, 309], [357, 140, 85, 128], [362, 499], [334, 361], [334, 469], [108, 265], [495, 233]], ![[261, 336, 128, 449], [272, 468], [21, 210], [13, 164, 355, 169], [42, 393], [419, 393], [265, 404], [129, 40], [230, 233]]]
 h' := ![![[237, 112, 128], [370, 124, 415], [51, 332, 210], [471, 248, 105], [186, 157, 164], [107, 203, 132], [236, 37, 240], [58, 201, 414], [0, 0, 1], [0, 1]], ![[134, 408, 393], [417, 428, 237], [37, 406, 10], [100, 9, 81], [502, 81, 1], [403, 452, 127], [266, 145, 19], [201, 127, 307], [439, 68, 408], [237, 112, 128]], ![[0, 1], [101, 490, 390], [96, 304, 301], [280, 264, 335], [340, 283, 356], [207, 387, 262], [250, 339, 262], [437, 193, 321], [292, 453, 112], [134, 408, 393]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [372, 446], []]
 b := ![[], [371, 236, 314], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A521 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 521 3 where
 D := ![[445, 1], [447, 1], [181, 204, 150, 1]]; D' := ![[445, 1], [447, 1], [181, 204, 150, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9, 9]
 n := ![1, 1, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P521P0
  | 1 => exact P521P1
  | 2 => exact P521P2

def C5210 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A521.D 0) 521 where
  n := 1
  w := ![![521, 0, 0, 0, 0], ![445, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C5211 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A521.D 1) 521 where
  n := 1
  w := ![![521, 0, 0, 0, 0], ![447, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C5212 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A521.D 2) 521 where
  n := 3
  w := ![![521, 0, 0, 0, 0], ![181, 205, 150, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K521 : KummerData 521 ![I521N0, I521N1, I521N2] ![521, 521, 141420761] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A521
  C := by
    intro i
    match i with
    | 0 => exact C5210
    | 1 => exact C5211
    | 2 => exact C5212
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 521 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp523 : Fact (Nat.Prime 523) := {out := by norm_num}

def I523N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![523, 0, 0, 0, 0], ![54, 1, 0, 0, 0]] i)))

def I523N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![523, 0, 0, 0, 0], ![938, 2953, 11196, -2100, 22728]] i)))

def P523P0 : CertificateIrreducibleZModOfList' 523 1 2 9 [54, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [339], [], [116], [], [], [], [], [469, 1]]]
 h' := ![![[0, 1], [522], [144], [12], [193], [70], [240], [122], [301], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P523P1 : CertificateIrreducibleZModOfList' 523 4 2 9 [290, 382, 301, 469, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [441, 16, 262, 282], [453, 450, 363, 494], [206, 56, 421, 270], [0, 1]]
 g := ![![[480, 450, 391, 179], [474, 374, 135, 122], [222, 201, 339], [412, 99, 385, 387], [35, 86, 102], [470, 449, 216], [462, 482, 301], [1], []], ![[496, 106, 289, 452, 166, 218], [37, 209, 287, 424, 5, 108], [102, 337, 264], [358, 443, 472, 231, 227, 474], [214, 288, 383], [140, 231, 250], [376, 53, 509], [93, 209, 515], [325, 225, 28]], ![[330, 125, 308, 383, 342, 321], [373, 343, 516, 309, 333, 83], [286, 382, 168], [306, 116, 395, 51, 477, 359], [10, 496, 464], [497, 274, 391], [230, 489, 247], [101, 182, 73], [109, 302, 318]], ![[112, 317, 521, 446, 77, 228], [68, 368, 403, 327, 86, 452], [499, 279, 179], [258, 398, 356, 225, 73, 519], [53, 115, 415], [93, 391, 292], [62, 435, 324], [341, 34, 468], [354, 337, 203]]]
 h' := ![![[441, 16, 262, 282], [89, 177, 129, 35], [207, 134, 512, 222], [287, 419, 101, 379], [96, 447, 27, 424], [49, 166, 485, 498], [328, 482, 507, 138], [233, 141, 222, 54], [0, 0, 1], [0, 1]], ![[453, 450, 363, 494], [394, 219, 294, 106], [509, 288, 466, 155], [156, 315, 522, 422], [54, 202, 369, 348], [503, 178, 379, 365], [49, 25, 424, 487], [456, 472, 413, 51], [338, 440, 220, 112], [441, 16, 262, 282]], ![[206, 56, 421, 270], [31, 283, 254, 5], [508, 430, 44, 441], [175, 340, 191, 210], [41, 125, 140, 126], [405, 63, 82, 386], [254, 486, 17, 310], [321, 264, 155, 436], [486, 246, 197, 317], [453, 450, 363, 494]], ![[0, 1], [288, 367, 369, 377], [81, 194, 24, 228], [135, 495, 232, 35], [227, 272, 510, 148], [133, 116, 100, 320], [133, 53, 98, 111], [445, 169, 256, 505], [444, 360, 105, 94], [206, 56, 421, 270]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [364, 182, 409], []]
 b := ![[], [], [66, 220, 313, 483], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A523 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 523 2 where
 D := ![[54, 1], [290, 382, 301, 469, 1]]; D' := ![[54, 1], [290, 382, 301, 469, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P523P0
  | 1 => exact P523P1

def C5230 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A523.D 0) 523 where
  n := 1
  w := ![![523, 0, 0, 0, 0], ![54, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C5231 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A523.D 1) 523 where
  n := 4
  w := ![![523, 0, 0, 0, 0], ![938, 2953, 11196, -2100, 22728]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K523 : KummerData 523 ![I523N0, I523N1] ![523, 74818113841] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A523
  C := by
    intro i
    match i with
    | 0 => exact C5230
    | 1 => exact C5231
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 523 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


lemma PB18792I10_primes (p : ℕ) :
  p ∈ Set.range ![467, 479, 487, 491, 499, 503, 509, 521, 523] ↔ Nat.Prime p ∧ 463 < p ∧ p ≤ 523 := by
  rw [← List.mem_ofFn']
  convert primes_range 463 523 (by omega)
  decide

def PB18792I10 : PrimesBelowBoundCertificateInterval O 463 523 18792 where
  m := 9
  g := ![2, 1, 2, 1, 3, 2, 3, 3, 2]
  P := ![467, 479, 487, 491, 499, 503, 509, 521, 523]
  hP := PB18792I10_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I467N0, I467N1]
    · exact ![I479N0]
    · exact ![I487N0, I487N1]
    · exact ![I491N0]
    · exact ![I499N0, I499N1, I499N2]
    · exact ![I503N0, I503N1]
    · exact ![I509N0, I509N1, I509N2]
    · exact ![I521N0, I521N1, I521N2]
    · exact ![I523N0, I523N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · convert (containsPrimesAbove_of_KummerData K467) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K479) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K487) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K491) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K499) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K503) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K509) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K521) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K523) <;> rfl
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![467, 47562811921]
    · exact ![25216079618399]
    · exact ![487, 56249134561]
    · exact ![28536943843451]
    · exact ![499, 249001, 249001]
    · exact ![253009, 127263527]
    · exact ![509, 259081, 259081]
    · exact ![521, 521, 141420761]
    · exact ![523, 74818113841]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact (card_quot_of_KummerData K467)
    · exact (card_quot_of_KummerData K479)
    · exact (card_quot_of_KummerData K487)
    · exact (card_quot_of_KummerData K491)
    · exact (card_quot_of_KummerData K499)
    · exact (card_quot_of_KummerData K503)
    · exact (card_quot_of_KummerData K509)
    · exact (card_quot_of_KummerData K521)
    · exact (card_quot_of_KummerData K523)
  β := ![I467N0, I487N0, I499N0, I509N0, I521N0, I521N1, I523N0]
  Il := ![[I467N0], [], [I487N0], [], [I499N0], [], [I509N0], [I521N0, I521N1], [I523N0]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
