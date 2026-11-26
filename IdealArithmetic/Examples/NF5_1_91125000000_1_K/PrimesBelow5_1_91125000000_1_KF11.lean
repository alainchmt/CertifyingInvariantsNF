
import IdealArithmetic.Examples.NF5_1_91125000000_1_K.RI5_1_91125000000_1_K
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 

instance hp541 : Fact (Nat.Prime 541) := {out := by norm_num}

def I541N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![541, 0, 0, 0, 0], ![16230, 541, 541, 0, 0]] i)))

def P541P0 : CertificateIrreducibleZModOfList' 541 5 2 9 [510, 16, 441, 0, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [495, 240, 153, 230, 449], [263, 315, 162, 392, 514], [383, 336, 205, 203, 77], [482, 190, 21, 257, 42], [0, 1]]
 g := ![![[365, 428, 296, 397, 306], [308, 49, 255, 312], [58, 142, 435, 387, 315], [14, 523, 121, 393, 104], [426, 147, 358, 228, 95], [533, 151, 90, 256], [100, 0, 0, 1], [], []], ![[201, 84, 415, 388, 54, 263, 130, 187], [93, 404, 449, 514], [423, 131, 274, 60, 334, 263, 458, 15], [225, 70, 496, 121, 265, 25, 69, 345], [313, 520, 110, 539, 329, 281, 502, 343], [44, 242, 411, 285], [518, 103, 196, 57], [441, 372, 320, 235], [528, 403, 419, 349]], ![[447, 164, 436, 177, 334, 453, 217, 178], [260, 188, 515, 215], [450, 93, 152, 471, 250, 199, 198, 141], [142, 309, 155, 250, 227, 309, 175, 76], [170, 151, 453, 351, 474, 487, 63, 19], [310, 489, 366, 320], [398, 438, 323, 237], [344, 425, 46, 115], [40, 469, 472, 188]], ![[361, 342, 516, 253, 39, 415, 227, 447], [121, 540, 6, 192], [272, 237, 266, 201, 38, 423, 195, 59], [135, 83, 368, 420, 99, 227, 94, 293], [437, 10, 388, 195, 206, 509, 267, 414], [96, 286, 421, 467], [128, 266, 161, 20], [491, 524, 457, 287], [229, 285, 425, 519]], ![[272, 341, 56, 276, 38, 127, 461, 8], [251, 69, 265, 441], [457, 184, 139, 26, 52, 441, 414, 293], [326, 224, 148, 89, 121, 511, 536, 487], [294, 106, 500, 441, 143, 199, 253, 485], [326, 142, 331, 215], [35, 440, 281, 287], [67, 433, 282, 159], [279, 188, 489, 141]]]
 h' := ![![[495, 240, 153, 230, 449], [139, 73, 178, 201, 363], [175, 316, 440, 306, 316], [434, 353, 423, 307, 72], [222, 325, 247, 264, 53], [510, 257, 421, 251, 119], [395, 23, 262, 31, 525], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[263, 315, 162, 392, 514], [273, 66, 51, 429, 39], [119, 504, 90, 362, 236], [363, 412, 6, 33, 329], [275, 415, 373, 345, 496], [198, 363, 212, 129, 199], [218, 525, 472, 76, 291], [131, 389, 17, 211, 62], [90, 359, 75, 397, 59], [495, 240, 153, 230, 449]], ![[383, 336, 205, 203, 77], [275, 121, 337, 514, 184], [103, 284, 524, 231, 466], [151, 8, 25, 443, 307], [314, 199, 173, 295, 476], [417, 89, 283, 204, 238], [539, 93, 443, 518, 486], [134, 250, 396, 329, 49], [79, 518, 264, 155, 234], [263, 315, 162, 392, 514]], ![[482, 190, 21, 257, 42], [21, 415, 428, 200, 366], [479, 356, 62, 331, 85], [107, 506, 381, 517, 8], [230, 179, 345, 46, 249], [512, 240, 250, 432, 173], [426, 219, 366, 131, 396], [251, 403, 174, 63, 392], [144, 162, 104, 496, 37], [383, 336, 205, 203, 77]], ![[0, 1], [267, 407, 88, 279, 130], [163, 163, 507, 393, 520], [424, 344, 247, 323, 366], [137, 505, 485, 132, 349], [431, 133, 457, 66, 353], [442, 222, 80, 326, 466], [502, 40, 495, 479, 37], [228, 43, 97, 34, 211], [482, 190, 21, 257, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [252, 255, 74, 483], [], [], []]
 b := ![[], [477, 89, 505, 158, 411], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A541 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 541 1 where
 D := ![[510, 16, 441, 0, 0, 1]]; D' := ![[510, 16, 441, 0, 0, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9]
 n := ![5]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P541P0

def C5410 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A541.D 0) 541 where
  n := 5
  w := ![![541, 0, 0, 0, 0], ![16230, 541, 541, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K541 : KummerData 541 ![I541N0] ![46343232758701] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A541
  C := by
    intro i
    match i with
    | 0 => exact C5410
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 541 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp547 : Fact (Nat.Prime 547) := {out := by norm_num}

def I547N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![547, 0, 0, 0, 0], ![66, 1, 0, 0, 0]] i)))

def I547N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![547, 0, 0, 0, 0], ![407, 1, 0, 0, 0]] i)))

def I547N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![547, 0, 0, 0, 0], ![515, 1, 0, 0, 0]] i)))

def I547N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![547, 0, 0, 0, 0], ![57, 106, 1, 0, 0]] i)))

def P547P0 : CertificateIrreducibleZModOfList' 547 1 2 9 [66, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [489], [], [], [], [143], [], [], [481, 1]]]
 h' := ![![[0, 1], [546], [184], [344], [176], [408], [276], [400], [527], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P547P1 : CertificateIrreducibleZModOfList' 547 1 2 9 [407, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [379], [], [], [], [69], [], [], [140, 1]]]
 h' := ![![[0, 1], [1], [191], [174], [135], [361], [347], [259], [455], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P547P2 : CertificateIrreducibleZModOfList' 547 1 2 9 [515, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [188], [], [], [], [324], [], [], [32, 1]]]
 h' := ![![[0, 1], [546], [113], [67], [78], [522], [529], [524], [477], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P547P3 : CertificateIrreducibleZModOfList' 547 2 2 9 [57, 106, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [441, 546], [0, 1]]
 g := ![![[165, 402], [295, 361], [502], [167], [143], [370, 375], [276], [296], [1]], ![[219, 145], [319, 186], [502], [167], [143], [4, 172], [276], [296], [1]]]
 h' := ![![[441, 546], [142, 245], [180, 528], [509, 99], [27, 279], [243, 276], [100, 310], [52, 400], [490, 441], [0, 1]], ![[0, 1], [428, 302], [6, 19], [408, 448], [538, 268], [525, 271], [60, 237], [318, 147], [239, 106], [441, 546]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [193]]
 b := ![[], [465, 370]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A547 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 547 4 where
 D := ![[66, 1], [407, 1], [515, 1], [57, 106, 1]]; D' := ![[66, 1], [407, 1], [515, 1], [57, 106, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9, 9, 9]
 n := ![1, 1, 1, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P547P0
  | 1 => exact P547P1
  | 2 => exact P547P2
  | 3 => exact P547P3

def C5470 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A547.D 0) 547 where
  n := 1
  w := ![![547, 0, 0, 0, 0], ![66, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C5471 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A547.D 1) 547 where
  n := 1
  w := ![![547, 0, 0, 0, 0], ![407, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C5472 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A547.D 2) 547 where
  n := 1
  w := ![![547, 0, 0, 0, 0], ![515, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C5473 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A547.D 3) 547 where
  n := 2
  w := ![![547, 0, 0, 0, 0], ![57, 106, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K547 : KummerData 547 ![I547N0, I547N1, I547N2, I547N3] ![547, 547, 547, 299209] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A547
  C := by
    intro i
    match i with
    | 0 => exact C5470
    | 1 => exact C5471
    | 2 => exact C5472
    | 3 => exact C5473
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 547 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp557 : Fact (Nat.Prime 557) := {out := by norm_num}

def I557N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![557, 0, 0, 0, 0], ![159, 484, 1, 0, 0]] i)))

def I557N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![557, 0, 0, 0, 0], ![311, 158, 73, 2, 0]] i)))

def P557P0 : CertificateIrreducibleZModOfList' 557 2 2 9 [159, 484, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [73, 556], [0, 1]]
 g := ![![[511, 550], [463], [201, 304], [466, 498], [390], [228, 233], [150], [316], [1]], ![[0, 7], [463], [113, 253], [58, 59], [390], [527, 324], [150], [316], [1]]]
 h' := ![![[73, 556], [4, 267], [347, 483], [544, 96], [355, 337], [510, 163], [479, 104], [102, 411], [398, 73], [0, 1]], ![[0, 1], [0, 290], [515, 74], [311, 461], [448, 220], [155, 394], [273, 453], [27, 146], [157, 484], [73, 556]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [188]]
 b := ![[], [468, 94]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P557P1 : CertificateIrreducibleZModOfList' 557 3 2 9 [311, 157, 73, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [463, 413, 140], [21, 143, 417], [0, 1]]
 g := ![![[140, 82, 547], [138, 361], [438, 88, 448], [248, 76, 531], [191, 157], [142, 343, 153], [223, 216], [484, 1], []], ![[104, 83, 143, 501], [352, 143], [86, 228, 136, 288], [345, 89, 389, 264], [206, 112], [91, 463, 207, 512], [303, 62], [143, 397], [474, 105]], ![[265, 15, 251, 345], [357, 382], [201, 112, 392, 412], [447, 420, 115, 300], [321, 438], [511, 16, 367, 44], [88, 384], [215, 127], [197, 105]]]
 h' := ![![[463, 413, 140], [267, 457, 382], [247, 360, 19], [295, 209, 273], [414, 119, 100], [398, 272, 132], [404, 406, 316], [423, 10, 159], [0, 0, 1], [0, 1]], ![[21, 143, 417], [125, 455, 522], [341, 552, 202], [347, 236, 345], [171, 222, 325], [36, 410, 142], [251, 264, 97], [501, 281, 186], [115, 207, 143], [463, 413, 140]], ![[0, 1], [118, 202, 210], [90, 202, 336], [14, 112, 496], [525, 216, 132], [106, 432, 283], [515, 444, 144], [490, 266, 212], [444, 350, 413], [21, 143, 417]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [223, 268], []]
 b := ![[], [323, 275, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A557 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 557 2 where
 D := ![[159, 484, 1], [311, 157, 73, 1]]; D' := ![[159, 484, 1], [311, 157, 73, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P557P0
  | 1 => exact P557P1

def C5570 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A557.D 0) 557 where
  n := 2
  w := ![![557, 0, 0, 0, 0], ![159, 484, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C5571 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A557.D 1) 557 where
  n := 3
  w := ![![557, 0, 0, 0, 0], ![311, 158, 73, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K557 : KummerData 557 ![I557N0, I557N1] ![310249, 172808693] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A557
  C := by
    intro i
    match i with
    | 0 => exact C5570
    | 1 => exact C5571
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 557 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp563 : Fact (Nat.Prime 563) := {out := by norm_num}

def I563N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![563, 0, 0, 0, 0], ![361, 1, 0, 0, 0]] i)))

def I563N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![563, 0, 0, 0, 0], ![1077, 2855, 11163, -2634, 22728]] i)))

def P563P0 : CertificateIrreducibleZModOfList' 563 1 2 9 [361, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [432], [], [], [177], [437], [], [], [202, 1]]]
 h' := ![![[0, 1], [562], [326], [153], [285], [446], [174], [323], [268], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P563P1 : CertificateIrreducibleZModOfList' 563 4 2 9 [429, 551, 268, 202, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [148, 477, 449, 381], [482, 75, 490, 1], [294, 10, 187, 181], [0, 1]]
 g := ![![[270, 469, 27, 117], [407, 30, 194, 334], [116, 416, 537], [454, 289, 522], [80, 119, 389, 149], [379, 7, 50, 7], [459, 88, 268], [1], []], ![[539, 185, 214, 217, 265, 280], [297, 28, 224, 14, 472, 241], [472, 466, 543], [213, 249, 428], [342, 63, 467, 190, 187, 400], [396, 361, 406, 141, 454, 406], [549, 197, 522], [219, 467, 117], [138, 41, 470]], ![[2, 343, 342, 392, 88, 454], [15, 368, 478, 276, 315, 555], [83, 437, 297], [64, 543, 113], [63, 211, 553, 199, 33, 231], [443, 35, 473, 128, 90, 475], [36, 494, 251], [556, 166, 59], [65, 215, 1]], ![[219, 123, 420, 173, 83, 328], [218, 420, 531, 466, 486, 296], [162, 63, 68], [384, 481, 429], [184, 460, 133, 408, 77, 243], [324, 263, 531, 385, 10, 137], [144, 466, 485], [287, 558, 181], [261, 477, 107]]]
 h' := ![![[148, 477, 449, 381], [490, 386, 82, 491], [347, 400, 268, 309], [561, 109, 153, 492], [23, 523, 271, 327], [116, 467, 133, 49], [79, 248, 479, 313], [134, 12, 295, 361], [0, 0, 1], [0, 1]], ![[482, 75, 490, 1], [298, 4, 501, 416], [313, 189, 63, 439], [552, 349, 172, 150], [520, 394, 21, 362], [549, 501, 231, 144], [475, 201, 25, 287], [528, 26, 171, 327], [423, 273, 140, 72], [148, 477, 449, 381]], ![[294, 10, 187, 181], [430, 70, 43, 78], [384, 302, 80, 41], [327, 512, 458, 294], [549, 396, 276, 537], [43, 38, 382, 291], [198, 403, 118, 103], [21, 72, 454, 292], [70, 550, 493, 348], [482, 75, 490, 1]], ![[0, 1], [382, 103, 500, 141], [493, 235, 152, 337], [424, 156, 343, 190], [398, 376, 558, 463], [85, 120, 380, 79], [52, 274, 504, 423], [531, 453, 206, 146], [365, 303, 492, 143], [294, 10, 187, 181]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [296, 422, 382], []]
 b := ![[], [], [539, 376, 372, 181], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A563 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 563 2 where
 D := ![[361, 1], [429, 551, 268, 202, 1]]; D' := ![[361, 1], [429, 551, 268, 202, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P563P0
  | 1 => exact P563P1

def C5630 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A563.D 0) 563 where
  n := 1
  w := ![![563, 0, 0, 0, 0], ![361, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C5631 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A563.D 1) 563 where
  n := 4
  w := ![![563, 0, 0, 0, 0], ![1077, 2855, 11163, -2634, 22728]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K563 : KummerData 563 ![I563N0, I563N1] ![563, 100469346961] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A563
  C := by
    intro i
    match i with
    | 0 => exact C5630
    | 1 => exact C5631
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 563 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp569 : Fact (Nat.Prime 569) := {out := by norm_num}

def I569N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![569, 0, 0, 0, 0], ![50, 1, 0, 0, 0]] i)))

def I569N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![569, 0, 0, 0, 0], ![558, 1, 0, 0, 0]] i)))

def I569N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![569, 0, 0, 0, 0], ![101, 365, 530, 2, 0]] i)))

def P569P0 : CertificateIrreducibleZModOfList' 569 1 2 9 [50, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [70], [26], [25], [], [], [519, 1]]]
 h' := ![![[0, 1], [1], [568], [483], [407], [457], [5], [104], [224], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P569P1 : CertificateIrreducibleZModOfList' 569 1 2 9 [558, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [200], [438], [141], [], [], [11, 1]]]
 h' := ![![[0, 1], [568], [86], [493], [266], [413], [80], [416], [121], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P569P2 : CertificateIrreducibleZModOfList' 569 3 2 9 [101, 364, 530, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [63, 219, 233], [545, 349, 336], [0, 1]]
 g := ![![[405, 34, 224], [264, 536], [365, 395], [114, 430, 439], [369, 468, 86], [486, 423, 526], [532, 361], [39, 1], []], ![[141, 61, 326, 236], [486, 282], [287, 560], [510, 513, 502, 459], [518, 256, 395, 463], [389, 215, 556, 95], [20, 305], [197, 35], [225, 234]], ![[84, 69, 504, 515], [89, 43], [67, 282], [194, 407, 306, 408], [220, 2, 382, 538], [499, 270, 492, 150], [292, 369], [172, 165], [122, 234]]]
 h' := ![![[63, 219, 233], [433, 326, 519], [437, 322, 180], [435, 282, 163], [285, 271, 281], [417, 296, 493], [552, 259, 327], [44, 497, 19], [0, 0, 1], [0, 1]], ![[545, 349, 336], [6, 188, 470], [36, 26, 148], [2, 149, 258], [499, 412, 185], [399, 108, 338], [407, 89, 356], [459, 411, 97], [21, 13, 349], [63, 219, 233]], ![[0, 1], [98, 55, 149], [230, 221, 241], [13, 138, 148], [183, 455, 103], [76, 165, 307], [403, 221, 455], [508, 230, 453], [203, 556, 219], [545, 349, 336]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [400, 495], []]
 b := ![[], [0, 219, 98], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A569 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 569 3 where
 D := ![[50, 1], [558, 1], [101, 364, 530, 1]]; D' := ![[50, 1], [558, 1], [101, 364, 530, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9, 9]
 n := ![1, 1, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P569P0
  | 1 => exact P569P1
  | 2 => exact P569P2

def C5690 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A569.D 0) 569 where
  n := 1
  w := ![![569, 0, 0, 0, 0], ![50, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C5691 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A569.D 1) 569 where
  n := 1
  w := ![![569, 0, 0, 0, 0], ![558, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C5692 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A569.D 2) 569 where
  n := 3
  w := ![![569, 0, 0, 0, 0], ![101, 365, 530, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K569 : KummerData 569 ![I569N0, I569N1, I569N2] ![569, 569, 184220009] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A569
  C := by
    intro i
    match i with
    | 0 => exact C5690
    | 1 => exact C5691
    | 2 => exact C5692
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 569 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp571 : Fact (Nat.Prime 571) := {out := by norm_num}

def I571N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![571, 0, 0, 0, 0], ![61, 1, 0, 0, 0]] i)))

def I571N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![571, 0, 0, 0, 0], ![559, 1, 0, 0, 0]] i)))

def I571N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![571, 0, 0, 0, 0], ![87, 279, 522, 2, 0]] i)))

def P571P0 : CertificateIrreducibleZModOfList' 571 1 2 9 [61, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [337], [], [82], [494], [223], [], [], [510, 1]]]
 h' := ![![[0, 1], [570], [497], [137], [129], [101], [44], [233], [295], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P571P1 : CertificateIrreducibleZModOfList' 571 1 2 9 [559, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [333], [], [496], [337], [482], [], [], [12, 1]]]
 h' := ![![[0, 1], [570], [322], [242], [47], [74], [424], [180], [144], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P571P2 : CertificateIrreducibleZModOfList' 571 3 2 9 [87, 278, 522, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [363, 76, 483], [257, 494, 88], [0, 1]]
 g := ![![[429, 57, 191], [400, 356, 270], [182, 281], [15, 405, 415], [384, 132, 449], [229, 227, 215], [122, 226], [49, 1], []], ![[555, 354, 292, 303], [283, 145, 485, 92], [382, 97], [551, 33, 457, 374], [207, 493, 77, 115], [520, 567, 263, 457], [533, 253], [60, 219], [69, 321]], ![[493, 219, 564, 40], [212, 485, 98, 412], [552, 482], [348, 327, 366, 489], [327, 364, 310, 372], [371, 526, 329, 247], [312, 434], [132, 66], [464, 321]]]
 h' := ![![[363, 76, 483], [31, 441, 251], [457, 537, 542], [408, 157, 515], [281, 379, 269], [62, 93, 303], [187, 472, 277], [305, 566, 410], [0, 0, 1], [0, 1]], ![[257, 494, 88], [336, 449, 107], [440, 438, 86], [117, 421, 203], [122, 477, 180], [403, 66, 461], [124, 135, 516], [108, 429, 275], [146, 73, 494], [363, 76, 483]], ![[0, 1], [222, 252, 213], [119, 167, 514], [429, 564, 424], [274, 286, 122], [307, 412, 378], [558, 535, 349], [132, 147, 457], [557, 498, 76], [257, 494, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51, 438], []]
 b := ![[], [208, 535, 563], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A571 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 571 3 where
 D := ![[61, 1], [559, 1], [87, 278, 522, 1]]; D' := ![[61, 1], [559, 1], [87, 278, 522, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9, 9]
 n := ![1, 1, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P571P0
  | 1 => exact P571P1
  | 2 => exact P571P2

def C5710 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A571.D 0) 571 where
  n := 1
  w := ![![571, 0, 0, 0, 0], ![61, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C5711 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A571.D 1) 571 where
  n := 1
  w := ![![571, 0, 0, 0, 0], ![559, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C5712 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A571.D 2) 571 where
  n := 3
  w := ![![571, 0, 0, 0, 0], ![87, 279, 522, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K571 : KummerData 571 ![I571N0, I571N1, I571N2] ![571, 571, 186169411] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A571
  C := by
    intro i
    match i with
    | 0 => exact C5710
    | 1 => exact C5711
    | 2 => exact C5712
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 571 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp577 : Fact (Nat.Prime 577) := {out := by norm_num}

def I577N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![577, 0, 0, 0, 0], ![160, 555, 1, 0, 0]] i)))

def I577N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![577, 0, 0, 0, 0], ![46, 325, 22, 2, 0]] i)))

def P577P0 : CertificateIrreducibleZModOfList' 577 2 2 9 [160, 555, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 576], [0, 1]]
 g := ![![[310, 384], [81], [182], [306], [207], [543], [166, 544], [484], [1]], ![[103, 193], [81], [182], [306], [207], [543], [17, 33], [484], [1]]]
 h' := ![![[22, 576], [241, 31], [514, 568], [28, 392], [382, 179], [571, 28], [559, 299], [90, 146], [417, 22], [0, 1]], ![[0, 1], [346, 546], [316, 9], [574, 185], [281, 398], [33, 549], [213, 278], [417, 431], [324, 555], [22, 576]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [74]]
 b := ![[], [170, 37]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P577P1 : CertificateIrreducibleZModOfList' 577 3 2 9 [46, 324, 22, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [458, 475, 177], [97, 101, 400], [0, 1]]
 g := ![![[266, 98, 263], [60, 478], [349, 114], [405, 23], [286, 571], [185, 552], [309, 313, 212], [555, 1], []], ![[509, 335, 492, 324], [365, 92], [533, 256], [283, 212], [87, 520], [85, 153], [162, 270, 361, 142], [217, 392], [520, 171]], ![[189, 16, 194, 53], [436, 354], [334, 555], [496, 529], [385, 18], [408, 290], [78, 118, 142, 48], [306, 18], [297, 171]]]
 h' := ![![[458, 475, 177], [1, 417, 436], [284, 223, 47], [392, 411, 445], [315, 250, 183], [237, 249, 93], [211, 278, 457], [435, 158, 160], [0, 0, 1], [0, 1]], ![[97, 101, 400], [451, 137, 137], [331, 343, 366], [275, 186, 561], [487, 365, 417], [67, 327, 382], [365, 115, 158], [19, 353, 274], [50, 258, 101], [458, 475, 177]], ![[0, 1], [230, 23, 4], [317, 11, 164], [421, 557, 148], [405, 539, 554], [449, 1, 102], [350, 184, 539], [562, 66, 143], [363, 319, 475], [97, 101, 400]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [483, 261], []]
 b := ![[], [177, 293, 155], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A577 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 577 2 where
 D := ![[160, 555, 1], [46, 324, 22, 1]]; D' := ![[160, 555, 1], [46, 324, 22, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P577P0
  | 1 => exact P577P1

def C5770 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A577.D 0) 577 where
  n := 2
  w := ![![577, 0, 0, 0, 0], ![160, 555, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C5771 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A577.D 1) 577 where
  n := 3
  w := ![![577, 0, 0, 0, 0], ![46, 325, 22, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K577 : KummerData 577 ![I577N0, I577N1] ![332929, 192100033] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A577
  C := by
    intro i
    match i with
    | 0 => exact C5770
    | 1 => exact C5771
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 577 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp587 : Fact (Nat.Prime 587) := {out := by norm_num}

def I587N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![587, 0, 0, 0, 0], ![557, 1, 0, 0, 0]] i)))

def I587N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![587, 0, 0, 0, 0], ![1172, 2617, 11208, -2978, 22728]] i)))

def P587P0 : CertificateIrreducibleZModOfList' 587 1 2 9 [557, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [137], [], [169], [], [], [78], [], [30, 1]]]
 h' := ![![[0, 1], [1], [170], [374], [574], [64], [579], [527], [313], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P587P1 : CertificateIrreducibleZModOfList' 587 4 2 9 [524, 485, 313, 30, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [400, 214, 499, 189], [534, 142, 269, 311], [210, 230, 406, 87], [0, 1]]
 g := ![![[407, 440, 229, 212], [511, 418, 95, 456], [16, 144, 233], [561, 535, 569, 429], [226, 100, 10], [501, 578, 564], [557, 397, 585, 313], [1], []], ![[350, 334, 404, 291, 45, 28], [562, 256, 564, 205, 214, 507], [495, 446, 527], [132, 342, 315, 516, 252, 82], [135, 193, 548], [133, 503, 84], [259, 128, 270, 528, 329, 400], [99, 377, 296], [19, 427, 501]], ![[535, 33, 534, 85, 154, 3], [66, 468, 560, 375, 84, 299], [578, 328, 147], [559, 232, 470, 207, 149, 374], [372, 165, 229], [324, 324, 63], [406, 242, 564, 482, 344, 249], [286, 118, 169], [331, 521, 453]], ![[52, 49, 543, 230, 245, 563], [403, 214, 139, 147, 454, 74], [300, 199, 387], [386, 390, 562, 209, 469, 542], [321, 370, 579], [299, 312, 214], [449, 303, 187, 514, 138, 68], [371, 247, 312], [330, 303, 525]]]
 h' := ![![[400, 214, 499, 189], [495, 562, 191, 489], [288, 215, 126, 248], [123, 227, 7, 258], [354, 345, 212, 58], [70, 384, 416, 373], [458, 92, 388, 369], [63, 102, 274, 557], [0, 0, 1], [0, 1]], ![[534, 142, 269, 311], [514, 389, 262, 205], [481, 103, 434, 503], [355, 555, 176, 313], [250, 197, 507, 434], [186, 76, 61, 247], [5, 2, 35, 387], [108, 58, 79, 313], [359, 459, 541, 480], [400, 214, 499, 189]], ![[210, 230, 406, 87], [515, 490, 499, 276], [132, 331, 154, 139], [317, 74, 42, 294], [190, 138, 126, 36], [415, 135, 392, 140], [247, 100, 162, 496], [73, 52, 106, 94], [182, 464, 252, 574], [534, 142, 269, 311]], ![[0, 1], [464, 320, 222, 204], [496, 525, 460, 284], [520, 318, 362, 309], [132, 494, 329, 59], [464, 579, 305, 414], [96, 393, 2, 509], [155, 375, 128, 210], [320, 251, 380, 120], [210, 230, 406, 87]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [314, 213, 36], []]
 b := ![[], [], [546, 584, 366, 434], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A587 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 587 2 where
 D := ![[557, 1], [524, 485, 313, 30, 1]]; D' := ![[557, 1], [524, 485, 313, 30, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P587P0
  | 1 => exact P587P1

def C5870 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A587.D 0) 587 where
  n := 1
  w := ![![587, 0, 0, 0, 0], ![557, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C5871 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A587.D 1) 587 where
  n := 4
  w := ![![587, 0, 0, 0, 0], ![1172, 2617, 11208, -2978, 22728]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K587 : KummerData 587 ![I587N0, I587N1] ![587, 118727795761] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A587
  C := by
    intro i
    match i with
    | 0 => exact C5870
    | 1 => exact C5871
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 587 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp593 : Fact (Nat.Prime 593) := {out := by norm_num}

def I593N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![593, 0, 0, 0, 0], ![5, 434, 1, 0, 0]] i)))

def I593N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![593, 0, 0, 0, 0], ![414, 371, 159, 2, 0]] i)))

def P593P0 : CertificateIrreducibleZModOfList' 593 2 2 9 [5, 434, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [159, 592], [0, 1]]
 g := ![![[324, 351], [439], [514], [232], [585, 4], [342], [181, 311], [375], [1]], ![[391, 242], [439], [514], [232], [35, 589], [342], [411, 282], [375], [1]]]
 h' := ![![[159, 592], [117, 105], [84, 517], [440, 496], [40, 316], [161, 591], [281, 243], [522, 514], [588, 159], [0, 1]], ![[0, 1], [208, 488], [453, 76], [435, 97], [472, 277], [436, 2], [373, 350], [414, 79], [370, 434], [159, 592]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [246, 299]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P593P1 : CertificateIrreducibleZModOfList' 593 3 2 9 [414, 370, 159, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [543, 111, 171], [484, 481, 422], [0, 1]]
 g := ![![[278, 117, 308], [398, 373], [537, 436], [591, 91], [337, 577, 487], [219, 464], [187, 231, 25], [434, 1], []], ![[546, 142, 214, 279], [536, 39], [0, 9], [404, 200], [274, 254, 115, 279], [284, 435], [287, 152, 525, 414], [524, 91], [404, 184]], ![[493, 344, 434, 520], [326, 347], [243, 279], [511, 523], [161, 431, 155, 422], [448, 449], [113, 176, 333, 514], [103, 461], [153, 184]]]
 h' := ![![[543, 111, 171], [278, 435, 402], [579, 583, 128], [119, 173, 423], [430, 99, 112], [314, 162, 303], [265, 39, 196], [3, 302, 5], [0, 0, 1], [0, 1]], ![[484, 481, 422], [134, 247, 304], [577, 573, 558], [308, 58, 590], [526, 231, 234], [560, 113, 289], [326, 31, 135], [218, 162, 84], [98, 444, 481], [543, 111, 171]], ![[0, 1], [379, 504, 480], [519, 30, 500], [79, 362, 173], [48, 263, 247], [105, 318, 1], [146, 523, 262], [350, 129, 504], [130, 149, 111], [484, 481, 422]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 290], []]
 b := ![[], [83, 449, 85], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A593 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 593 2 where
 D := ![[5, 434, 1], [414, 370, 159, 1]]; D' := ![[5, 434, 1], [414, 370, 159, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P593P0
  | 1 => exact P593P1

def C5930 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A593.D 0) 593 where
  n := 2
  w := ![![593, 0, 0, 0, 0], ![5, 434, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C5931 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A593.D 1) 593 where
  n := 3
  w := ![![593, 0, 0, 0, 0], ![414, 371, 159, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K593 : KummerData 593 ![I593N0, I593N1] ![351649, 208527857] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A593
  C := by
    intro i
    match i with
    | 0 => exact C5930
    | 1 => exact C5931
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 593 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


lemma PB18792I11_primes (p : ℕ) :
  p ∈ Set.range ![541, 547, 557, 563, 569, 571, 577, 587, 593] ↔ Nat.Prime p ∧ 523 < p ∧ p ≤ 593 := by
  rw [← List.mem_ofFn']
  convert primes_range 523 593 (by omega)
  decide

def PB18792I11 : PrimesBelowBoundCertificateInterval O 523 593 18792 where
  m := 9
  g := ![1, 4, 2, 2, 3, 3, 2, 2, 2]
  P := ![541, 547, 557, 563, 569, 571, 577, 587, 593]
  hP := PB18792I11_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I541N0]
    · exact ![I547N0, I547N1, I547N2, I547N3]
    · exact ![I557N0, I557N1]
    · exact ![I563N0, I563N1]
    · exact ![I569N0, I569N1, I569N2]
    · exact ![I571N0, I571N1, I571N2]
    · exact ![I577N0, I577N1]
    · exact ![I587N0, I587N1]
    · exact ![I593N0, I593N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · convert (containsPrimesAbove_of_KummerData K541) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K547) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K557) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K563) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K569) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K571) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K577) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K587) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K593) <;> rfl
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![46343232758701]
    · exact ![547, 547, 547, 299209]
    · exact ![310249, 172808693]
    · exact ![563, 100469346961]
    · exact ![569, 569, 184220009]
    · exact ![571, 571, 186169411]
    · exact ![332929, 192100033]
    · exact ![587, 118727795761]
    · exact ![351649, 208527857]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact (card_quot_of_KummerData K541)
    · exact (card_quot_of_KummerData K547)
    · exact (card_quot_of_KummerData K557)
    · exact (card_quot_of_KummerData K563)
    · exact (card_quot_of_KummerData K569)
    · exact (card_quot_of_KummerData K571)
    · exact (card_quot_of_KummerData K577)
    · exact (card_quot_of_KummerData K587)
    · exact (card_quot_of_KummerData K593)
  β := ![I547N0, I547N1, I547N2, I563N0, I569N0, I569N1, I571N0, I571N1, I587N0]
  Il := ![[], [I547N0, I547N1, I547N2], [], [I563N0], [I569N0, I569N1], [I571N0, I571N1], [], [I587N0], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
