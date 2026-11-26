
import IdealArithmetic.Examples.NF5_1_91125000000_1_K.RI5_1_91125000000_1_K
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 

instance hp599 : Fact (Nat.Prime 599) := {out := by norm_num}

def I599N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![599, 0, 0, 0, 0], ![16173, 599, 599, 0, 0]] i)))

def P599P0 : CertificateIrreducibleZModOfList' 599 5 2 9 [453, 74, 499, 0, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [266, 356, 262, 262, 96], [92, 573, 512, 90, 198], [594, 111, 198, 207, 491], [246, 157, 226, 40, 413], [0, 1]]
 g := ![![[568, 6, 383, 449, 34], [432, 413, 535, 217, 13], [536, 3, 520, 566, 24], [279, 29, 203, 185], [556, 215, 152, 64, 480], [180, 130, 474, 351], [525, 100, 0, 0, 1], [], []], ![[205, 246, 241, 359, 356, 495, 14, 490], [4, 240, 441, 320, 460, 570, 51, 81], [39, 485, 483, 427, 405, 328, 386, 424], [489, 294, 364, 3], [240, 252, 333, 178, 147, 313, 97, 72], [321, 120, 160, 506], [9, 433, 44, 400, 199, 381, 447, 128], [187, 97, 89, 48], [521, 346, 587, 231]], ![[375, 114, 406, 379, 270, 129, 131, 542], [220, 94, 524, 365, 309, 67, 317, 549], [550, 519, 553, 424, 396, 461, 334, 378], [158, 155, 216, 4], [67, 17, 522, 346, 164, 45, 296, 350], [475, 460, 335, 68], [64, 555, 542, 141, 119, 17, 150, 226], [590, 333, 418, 473], [345, 4, 299, 269]], ![[433, 332, 107, 573, 451, 443, 44, 291], [373, 212, 298, 43, 119, 538, 38, 560], [264, 380, 168, 340, 94, 491, 410, 280], [58, 170, 60, 588], [163, 168, 166, 288, 433, 343, 450, 70], [94, 459, 390, 181], [563, 364, 196, 53, 88, 163, 15, 241], [259, 410, 117, 592], [40, 81, 213, 283]], ![[0, 439, 207, 51, 167, 422, 12, 462], [328, 253, 170, 494, 561, 129, 305, 16], [309, 359, 475, 252, 597, 118, 131, 319], [547, 567, 189, 85], [364, 543, 291, 288, 142, 531, 511, 139], [111, 137, 232, 459], [287, 35, 189, 339, 187, 144, 386, 592], [530, 319, 500, 102], [184, 190, 95, 453]]]
 h' := ![![[266, 356, 262, 262, 96], [177, 22, 55, 581, 104], [386, 99, 370, 385, 278], [284, 507, 516, 382, 479], [311, 371, 198, 378, 28], [408, 450, 41, 414, 220], [577, 309, 175, 416, 146], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[92, 573, 512, 90, 198], [205, 269, 159, 152, 382], [513, 53, 136, 320, 277], [326, 441, 77, 120, 542], [163, 497, 378, 375, 411], [52, 452, 119, 64, 94], [551, 442, 279, 145, 393], [44, 404, 314, 287, 325], [67, 90, 349, 401, 446], [266, 356, 262, 262, 96]], ![[594, 111, 198, 207, 491], [124, 545, 321, 304, 476], [588, 144, 520, 97, 544], [340, 466, 204, 350, 318], [495, 442, 241, 545, 597], [377, 485, 216, 149, 131], [117, 431, 351, 497, 107], [536, 143, 247, 388, 549], [132, 220, 230, 296, 197], [92, 573, 512, 90, 198]], ![[246, 157, 226, 40, 413], [135, 112, 545, 57, 410], [160, 145, 16, 473, 246], [541, 572, 294, 202, 52], [224, 271, 561, 391, 236], [559, 132, 396, 27, 573], [278, 321, 340, 194, 177], [128, 524, 512, 71, 407], [474, 568, 510, 68, 340], [594, 111, 198, 207, 491]], ![[0, 1], [0, 250, 118, 104, 425], [550, 158, 156, 522, 452], [299, 410, 107, 144, 406], [50, 216, 419, 108, 525], [423, 278, 426, 544, 180], [284, 294, 53, 545, 375], [194, 127, 125, 452, 515], [525, 320, 108, 433, 215], [246, 157, 226, 40, 413]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [250, 28, 54, 250], [], [], []]
 b := ![[], [171, 490, 541, 77, 534], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A599 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 599 1 where
 D := ![[453, 74, 499, 0, 0, 1]]; D' := ![[453, 74, 499, 0, 0, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9]
 n := ![5]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P599P0

def C5990 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A599.D 0) 599 where
  n := 5
  w := ![![599, 0, 0, 0, 0], ![16173, 599, 599, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K599 : KummerData 599 ![I599N0] ![77114156402999] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A599
  C := by
    intro i
    match i with
    | 0 => exact C5990
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 599 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp601 : Fact (Nat.Prime 601) := {out := by norm_num}

def I601N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![601, 0, 0, 0, 0], ![506, 1, 0, 0, 0]] i)))

def I601N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![601, 0, 0, 0, 0], ![453, 8, 1, 0, 0]] i)))

def I601N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![601, 0, 0, 0, 0], ![63, 87, 1, 0, 0]] i)))

def P601P0 : CertificateIrreducibleZModOfList' 601 1 2 9 [506, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [46], [493], [], [384], [], [95, 1]]]
 h' := ![![[0, 1], [600], [125], [163], [558], [307], [420], [100], [10], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P601P1 : CertificateIrreducibleZModOfList' 601 2 2 9 [453, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [593, 600], [0, 1]]
 g := ![![[471, 134], [80], [305], [264, 467], [390, 72], [98], [357, 600], [64], [1]], ![[0, 467], [80], [305], [134, 134], [415, 529], [98], [365, 1], [64], [1]]]
 h' := ![![[593, 600], [195, 400], [114, 110], [7, 268], [24, 484], [380, 471], [549, 352], [124, 125], [148, 593], [0, 1]], ![[0, 1], [0, 201], [436, 491], [267, 333], [359, 117], [218, 130], [137, 249], [326, 476], [212, 8], [593, 600]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [590]]
 b := ![[], [579, 295]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P601P2 : CertificateIrreducibleZModOfList' 601 2 2 9 [63, 87, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [514, 600], [0, 1]]
 g := ![![[30, 540], [331], [80], [368, 266], [369, 376], [445], [81, 581], [357], [1]], ![[529, 61], [331], [80], [64, 335], [111, 225], [445], [18, 20], [357], [1]]]
 h' := ![![[514, 600], [185, 257], [486, 459], [255, 110], [192, 152], [92, 72], [306, 84], [109, 337], [538, 514], [0, 1]], ![[0, 1], [63, 344], [219, 142], [301, 491], [190, 449], [439, 529], [210, 517], [239, 264], [294, 87], [514, 600]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [538]]
 b := ![[], [583, 269]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A601 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 601 3 where
 D := ![[506, 1], [453, 8, 1], [63, 87, 1]]; D' := ![[506, 1], [453, 8, 1], [63, 87, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9, 9]
 n := ![1, 2, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P601P0
  | 1 => exact P601P1
  | 2 => exact P601P2

def C6010 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A601.D 0) 601 where
  n := 1
  w := ![![601, 0, 0, 0, 0], ![506, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C6011 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A601.D 1) 601 where
  n := 2
  w := ![![601, 0, 0, 0, 0], ![453, 8, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C6012 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A601.D 2) 601 where
  n := 2
  w := ![![601, 0, 0, 0, 0], ![63, 87, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K601 : KummerData 601 ![I601N0, I601N1, I601N2] ![601, 361201, 361201] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A601
  C := by
    intro i
    match i with
    | 0 => exact C6010
    | 1 => exact C6011
    | 2 => exact C6012
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 601 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp607 : Fact (Nat.Prime 607) := {out := by norm_num}

def I607N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![607, 0, 0, 0, 0], ![28, 1, 0, 0, 0]] i)))

def I607N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![607, 0, 0, 0, 0], ![867, 3088, 11072, -1880, 22728]] i)))

def P607P0 : CertificateIrreducibleZModOfList' 607 1 2 9 [28, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [542], [182], [553], [36], [], [595], [], [579, 1]]]
 h' := ![![[0, 1], [606], [367], [298], [206], [601], [336], [372], [177], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P607P1 : CertificateIrreducibleZModOfList' 607 4 2 9 [219, 407, 177, 579, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [230, 526, 497, 322], [415, 573, 37, 520], [597, 114, 73, 372], [0, 1]]
 g := ![![[229, 383, 219, 512], [359, 75, 311, 471], [125, 490, 425, 224], [605, 175, 24, 239], [256, 397, 271, 545], [576, 173, 126], [70, 509, 507, 177], [1], []], ![[375, 572, 467, 362, 283, 557], [401, 422, 594, 403, 219, 261], [541, 92, 595, 363, 76, 139], [84, 37, 416, 510, 283, 298], [396, 97, 367, 341, 506, 136], [127, 273, 499], [268, 193, 377, 156, 67, 255], [424, 445, 339], [154, 50, 494]], ![[200, 419, 372, 269, 352, 246], [513, 250, 281, 240, 291, 449], [526, 215, 316, 561, 300, 514], [65, 313, 527, 174, 162, 255], [222, 575, 508, 365, 534, 78], [480, 288, 483], [495, 345, 360, 41, 426, 153], [149, 302, 107], [16, 328, 285]], ![[35, 563, 229, 213, 58, 86], [244, 424, 339, 34, 535, 225], [305, 307, 217, 297, 236, 44], [122, 529, 274, 569, 147, 210], [455, 324, 315, 427, 606, 301], [194, 125, 541], [29, 3, 361, 430, 326, 289], [299, 433, 270], [510, 560, 595]]]
 h' := ![![[230, 526, 497, 322], [289, 96, 397, 538], [547, 274, 162, 423], [438, 570, 513, 312], [387, 488, 224, 229], [464, 329, 307, 200], [452, 264, 37, 373], [388, 200, 430, 28], [0, 0, 1], [0, 1]], ![[415, 573, 37, 520], [118, 283, 504, 360], [368, 449, 196, 30], [528, 110, 344, 267], [158, 432, 511, 561], [463, 171, 308, 37], [576, 265, 265, 509], [601, 105, 77, 239], [357, 193, 477, 406], [230, 526, 497, 322]], ![[597, 114, 73, 372], [272, 434, 94, 473], [443, 206, 569, 401], [454, 259, 121, 494], [237, 320, 268, 25], [53, 202, 422, 317], [532, 550, 62, 559], [165, 36, 501, 539], [582, 268, 48, 541], [415, 573, 37, 520]], ![[0, 1], [595, 401, 219, 450], [313, 285, 287, 360], [517, 275, 236, 141], [219, 581, 211, 399], [543, 512, 177, 53], [362, 135, 243, 380], [574, 266, 206, 408], [98, 146, 81, 267], [597, 114, 73, 372]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [589, 382, 430], []]
 b := ![[], [], [362, 477, 220, 291], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A607 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 607 2 where
 D := ![[28, 1], [219, 407, 177, 579, 1]]; D' := ![[28, 1], [219, 407, 177, 579, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P607P0
  | 1 => exact P607P1

def C6070 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A607.D 0) 607 where
  n := 1
  w := ![![607, 0, 0, 0, 0], ![28, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C6071 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A607.D 1) 607 where
  n := 4
  w := ![![607, 0, 0, 0, 0], ![867, 3088, 11072, -1880, 22728]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K607 : KummerData 607 ![I607N0, I607N1] ![607, 135754665601] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A607
  C := by
    intro i
    match i with
    | 0 => exact C6070
    | 1 => exact C6071
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 607 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp613 : Fact (Nat.Prime 613) := {out := by norm_num}

def I613N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![613, 0, 0, 0, 0], ![5, 162, 1, 0, 0]] i)))

def I613N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![613, 0, 0, 0, 0], ![534, 494, 451, 2, 0]] i)))

def P613P0 : CertificateIrreducibleZModOfList' 613 2 2 9 [5, 162, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [451, 612], [0, 1]]
 g := ![![[155, 427], [67], [305, 385], [138], [167], [355, 154], [346, 441], [498], [1]], ![[250, 186], [67], [461, 228], [138], [167], [540, 459], [12, 172], [498], [1]]]
 h' := ![![[451, 612], [181, 349], [314, 93], [333, 211], [196, 203], [64, 189], [109, 147], [600, 21], [608, 451], [0, 1]], ![[0, 1], [39, 264], [573, 520], [479, 402], [412, 410], [96, 424], [202, 466], [263, 592], [493, 162], [451, 612]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [554]]
 b := ![[], [369, 277]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P613P1 : CertificateIrreducibleZModOfList' 613 3 2 9 [534, 493, 451, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [362, 250, 517], [413, 362, 96], [0, 1]]
 g := ![![[346, 554, 280], [198, 43], [186, 533, 29], [84, 387], [286, 469], [297, 154, 422], [603, 15, 25], [162, 1], []], ![[416, 76, 79, 168], [121, 462], [411, 314, 343, 419], [151, 154], [368, 198], [312, 577, 31, 486], [49, 399, 367, 145], [566, 475], [151, 21]], ![[295, 524, 566, 533], [475, 322], [483, 425, 359, 404], [256, 70], [84, 551], [46, 128, 120, 487], [269, 157, 16, 302], [363, 587], [572, 21]]]
 h' := ![![[362, 250, 517], [28, 524, 541], [595, 246, 61], [57, 209, 320], [276, 251, 183], [169, 58, 193], [436, 93, 154], [538, 516, 5], [0, 0, 1], [0, 1]], ![[413, 362, 96], [352, 109, 257], [351, 592, 305], [421, 282, 148], [407, 174, 466], [530, 566, 546], [495, 202, 232], [472, 71, 88], [144, 328, 362], [362, 250, 517]], ![[0, 1], [193, 593, 428], [502, 388, 247], [604, 122, 145], [543, 188, 577], [227, 602, 487], [365, 318, 227], [227, 26, 520], [594, 285, 250], [413, 362, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [479, 183], []]
 b := ![[], [599, 17, 136], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A613 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 613 2 where
 D := ![[5, 162, 1], [534, 493, 451, 1]]; D' := ![[5, 162, 1], [534, 493, 451, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P613P0
  | 1 => exact P613P1

def C6130 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A613.D 0) 613 where
  n := 2
  w := ![![613, 0, 0, 0, 0], ![5, 162, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C6131 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A613.D 1) 613 where
  n := 3
  w := ![![613, 0, 0, 0, 0], ![534, 494, 451, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K613 : KummerData 613 ![I613N0, I613N1] ![375769, 230346397] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A613
  C := by
    intro i
    match i with
    | 0 => exact C6130
    | 1 => exact C6131
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 613 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp617 : Fact (Nat.Prime 617) := {out := by norm_num}

def I617N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![617, 0, 0, 0, 0], ![188, 388, 1, 0, 0]] i)))

def I617N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![617, 0, 0, 0, 0], ![494, 426, 229, 2, 0]] i)))

def P617P0 : CertificateIrreducibleZModOfList' 617 2 2 9 [188, 388, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [229, 616], [0, 1]]
 g := ![![[304, 128], [329], [366], [375, 236], [209], [237, 152], [140, 529], [613], [1]], ![[0, 489], [329], [366], [123, 381], [209], [493, 465], [349, 88], [613], [1]]]
 h' := ![![[229, 616], [546, 100], [9, 516], [455, 40], [344, 565], [485, 497], [211, 326], [310, 594], [429, 229], [0, 1]], ![[0, 1], [0, 517], [326, 101], [360, 577], [159, 52], [153, 120], [208, 291], [596, 23], [425, 388], [229, 616]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [111]]
 b := ![[], [278, 364]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P617P1 : CertificateIrreducibleZModOfList' 617 3 2 9 [494, 425, 229, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [600, 214, 122], [405, 402, 495], [0, 1]]
 g := ![![[351, 327, 554], [267, 472], [590, 602], [108, 350, 4], [309, 98], [140, 124, 489], [423, 550, 175], [388, 1], []], ![[229, 285, 449, 323], [603, 393], [225, 30], [427, 216, 169, 470], [332, 491], [488, 340, 545, 577], [484, 399, 105, 302], [162, 567], [260, 76]], ![[348, 5, 414, 119], [560, 366], [61, 576], [155, 407, 263, 372], [7, 144], [310, 391, 139, 335], [164, 555, 607, 68], [11, 138], [504, 76]]]
 h' := ![![[600, 214, 122], [593, 215, 82], [569, 256, 584], [327, 397, 336], [421, 8, 2], [561, 472, 396], [201, 119, 344], [215, 579, 188], [0, 0, 1], [0, 1]], ![[405, 402, 495], [385, 226, 579], [601, 12, 73], [208, 3, 257], [38, 189, 546], [395, 596, 209], [118, 438, 407], [472, 488, 602], [185, 164, 402], [600, 214, 122]], ![[0, 1], [2, 176, 573], [328, 349, 577], [193, 217, 24], [349, 420, 69], [546, 166, 12], [97, 60, 483], [507, 167, 444], [195, 453, 214], [405, 402, 495]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [448, 501], []]
 b := ![[], [25, 194, 446], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A617 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 617 2 where
 D := ![[188, 388, 1], [494, 425, 229, 1]]; D' := ![[188, 388, 1], [494, 425, 229, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P617P0
  | 1 => exact P617P1

def C6170 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A617.D 0) 617 where
  n := 2
  w := ![![617, 0, 0, 0, 0], ![188, 388, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C6171 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A617.D 1) 617 where
  n := 3
  w := ![![617, 0, 0, 0, 0], ![494, 426, 229, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K617 : KummerData 617 ![I617N0, I617N1] ![380689, 234885113] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A617
  C := by
    intro i
    match i with
    | 0 => exact C6170
    | 1 => exact C6171
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 617 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp619 : Fact (Nat.Prime 619) := {out := by norm_num}

def I619N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![619, 0, 0, 0, 0], ![16094, 619, 619, 0, 0]] i)))

def P619P0 : CertificateIrreducibleZModOfList' 619 5 2 9 [374, 94, 519, 0, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [169, 366, 426, 187, 107], [149, 150, 199, 360, 495], [399, 39, 211, 116, 544], [521, 63, 402, 575, 92], [0, 1]]
 g := ![![[554, 103, 390, 382, 600], [6, 80, 481, 401, 292], [376, 548, 588, 590], [426, 121, 155, 242, 351], [77, 290, 113, 6], [61, 314, 508, 615, 601], [525, 100, 0, 0, 1], [], []], ![[260, 507, 153, 74, 578, 17, 218, 486], [211, 450, 567, 451, 150, 101, 510, 357], [463, 133, 59, 80], [275, 531, 160, 610, 600, 585, 137, 28], [525, 492, 516, 53], [440, 460, 567, 293, 562, 441, 383, 136], [183, 177, 37, 553, 30, 615, 339, 51], [80, 280, 402, 283], [321, 476, 402, 307]], ![[328, 510, 53, 145, 330, 417, 592, 403], [273, 262, 311, 201, 155, 186, 399, 594], [101, 374, 45, 484], [383, 81, 267, 503, 57, 253, 300, 403], [91, 611, 61, 25], [607, 59, 122, 513, 498, 117, 391, 462], [384, 50, 149, 466, 422, 36, 31, 593], [271, 456, 544, 395], [235, 397, 475, 520]], ![[314, 34, 592, 129, 363, 238, 544, 605], [357, 577, 26, 74, 196, 395, 229, 358], [565, 539, 156, 228], [183, 487, 130, 275, 176, 574, 437, 81], [593, 433, 241, 401], [465, 154, 39, 24, 325, 245, 199, 104], [459, 62, 463, 402, 469, 82, 296, 64], [320, 48, 31, 344], [220, 376, 551, 54]], ![[97, 478, 195, 405, 506, 586, 10, 259], [283, 259, 385, 540, 14, 102, 599, 399], [557, 325, 32, 543], [184, 41, 516, 63, 177, 509, 67, 131], [18, 367, 151, 38], [130, 128, 205, 184, 77, 573, 299, 294], [80, 13, 318, 377, 205, 587, 45, 165], [453, 86, 335, 204], [584, 386, 570, 417]]]
 h' := ![![[169, 366, 426, 187, 107], [232, 78, 340, 591, 369], [403, 309, 242, 525, 337], [378, 211, 507, 124, 232], [169, 196, 279, 32, 410], [89, 46, 104, 287, 25], [492, 529, 389, 96, 245], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[149, 150, 199, 360, 495], [241, 480, 180, 48, 168], [559, 590, 14, 321, 578], [126, 397, 598, 600, 536], [526, 281, 10, 90, 140], [167, 605, 603, 286, 529], [132, 159, 327, 583, 530], [335, 13, 500, 28, 92], [119, 313, 437, 148, 39], [169, 366, 426, 187, 107]], ![[399, 39, 211, 116, 544], [168, 416, 55, 102, 327], [412, 26, 457, 53, 568], [293, 181, 610, 409, 22], [52, 299, 450, 210, 292], [563, 119, 587, 551, 614], [366, 469, 564, 187, 418], [216, 286, 453, 66, 557], [544, 408, 516, 357, 325], [149, 150, 199, 360, 495]], ![[521, 63, 402, 575, 92], [492, 350, 586, 601, 308], [196, 479, 571, 60, 90], [293, 502, 532, 308, 567], [526, 365, 279, 96, 316], [169, 288, 500, 311, 493], [323, 282, 522, 471, 323], [395, 28, 473, 230, 63], [165, 427, 1, 356, 413], [399, 39, 211, 116, 544]], ![[0, 1], [205, 533, 77, 515, 66], [283, 453, 573, 279, 284], [288, 566, 229, 416, 500], [477, 97, 220, 191, 80], [20, 180, 63, 422, 196], [346, 418, 55, 520, 341], [535, 292, 431, 295, 525], [410, 90, 283, 377, 461], [521, 63, 402, 575, 92]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39, 579, 356, 329], [], [], []]
 b := ![[], [562, 439, 343, 284, 587], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A619 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 619 1 where
 D := ![[374, 94, 519, 0, 0, 1]]; D' := ![[374, 94, 519, 0, 0, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9]
 n := ![5]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P619P0

def C6190 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A619.D 0) 619 where
  n := 5
  w := ![![619, 0, 0, 0, 0], ![16094, 619, 619, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K619 : KummerData 619 ![I619N0] ![90876845839099] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A619
  C := by
    intro i
    match i with
    | 0 => exact C6190
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 619 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp631 : Fact (Nat.Prime 631) := {out := by norm_num}

def I631N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![631, 0, 0, 0, 0], ![15775, 631, 631, 0, 0]] i)))

def P631P0 : CertificateIrreducibleZModOfList' 631 5 2 9 [55, 106, 531, 0, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [524, 126, 266, 392, 99], [619, 223, 32, 593, 348], [275, 335, 630, 486, 298], [475, 577, 334, 422, 517], [0, 1]]
 g := ![![[610, 462, 369, 585, 170], [58, 199, 610, 391, 202], [309, 1, 490, 104, 71], [55, 45, 551, 387], [407, 95, 185, 540, 256], [599, 110, 206, 464, 501], [525, 100, 0, 0, 1], [], []], ![[101, 76, 61, 316, 612, 189, 425, 503], [369, 220, 320, 340, 245, 58, 466, 389], [554, 321, 304, 57, 413, 282, 249, 374], [243, 622, 629, 41], [318, 223, 430, 138, 626, 104, 402, 399], [521, 78, 528, 502, 432, 152, 353, 499], [66, 315, 186, 605, 426, 150, 289, 552], [541, 327, 157, 349], [179, 626, 3, 336]], ![[345, 597, 443, 338, 129, 544, 559, 381], [435, 142, 70, 432, 526, 433, 157, 3], [469, 377, 568, 118, 352, 202, 40, 370], [625, 129, 281, 47], [213, 284, 524, 247, 131, 117, 574, 315], [604, 170, 252, 163, 45, 180, 80, 412], [563, 104, 316, 123, 55, 261, 316, 315], [548, 573, 31, 2], [322, 369, 54, 583]], ![[136, 351, 262, 540, 591, 496, 428, 493], [257, 118, 357, 191, 354, 336, 98, 128], [567, 607, 445, 481, 401, 602, 204, 378], [118, 166, 47, 47], [592, 413, 521, 209, 442, 204, 570, 340], [627, 195, 255, 527, 593, 407, 604, 290], [90, 538, 108, 97, 438, 319, 301, 215], [609, 486, 461, 577], [260, 237, 27, 464]], ![[490, 58, 21, 291, 158, 131, 211, 563], [46, 200, 544, 613, 172, 264, 444, 103], [71, 598, 354, 8, 83, 586, 484, 367], [312, 56, 348, 127], [509, 501, 48, 122, 606, 281, 32, 267], [33, 496, 24, 495, 350, 293, 348, 516], [251, 68, 136, 268, 1, 306, 481, 530], [426, 227, 432, 309], [533, 341, 327, 376]]]
 h' := ![![[524, 126, 266, 392, 99], [596, 446, 179, 354, 319], [42, 516, 230, 195, 145], [528, 428, 275, 511, 273], [331, 241, 46, 363, 132], [498, 582, 489, 62, 615], [151, 57, 254, 535, 576], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[619, 223, 32, 593, 348], [19, 273, 44, 604, 184], [270, 454, 66, 327, 378], [147, 616, 49, 546, 12], [92, 439, 612, 504, 159], [180, 352, 587, 408, 359], [139, 285, 69, 249, 58], [131, 135, 37, 238, 479], [342, 400, 564, 444, 89], [524, 126, 266, 392, 99]], ![[275, 335, 630, 486, 298], [467, 140, 452, 14, 129], [73, 297, 262, 462, 559], [316, 406, 621, 185, 272], [364, 357, 287, 510, 476], [529, 604, 276, 384, 300], [327, 12, 435, 495, 395], [456, 420, 6, 171, 300], [102, 166, 586, 413, 94], [619, 223, 32, 593, 348]], ![[475, 577, 334, 422, 517], [590, 490, 109, 453, 386], [288, 531, 289, 41, 536], [519, 274, 516, 474, 400], [229, 1, 58, 393, 155], [441, 292, 505, 362, 81], [465, 46, 582, 440, 69], [621, 423, 49, 143, 236], [118, 418, 12, 83, 75], [275, 335, 630, 486, 298]], ![[0, 1], [16, 544, 478, 468, 244], [343, 95, 415, 237, 275], [187, 169, 432, 177, 305], [567, 224, 259, 123, 340], [355, 63, 36, 46, 538], [503, 231, 553, 174, 164], [261, 284, 539, 79, 246], [69, 278, 99, 322, 373], [475, 577, 334, 422, 517]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26, 486, 271, 338], [], [], []]
 b := ![[], [550, 63, 451, 245, 430], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A631 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 631 1 where
 D := ![[55, 106, 531, 0, 0, 1]]; D' := ![[55, 106, 531, 0, 0, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9]
 n := ![5]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P631P0

def C6310 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A631.D 0) 631 where
  n := 5
  w := ![![631, 0, 0, 0, 0], ![15775, 631, 631, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K631 : KummerData 631 ![I631N0] ![100033806792151] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A631
  C := by
    intro i
    match i with
    | 0 => exact C6310
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 631 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp641 : Fact (Nat.Prime 641) := {out := by norm_num}

def I641N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![641, 0, 0, 0, 0], ![22, 1, 0, 0, 0]] i)))

def I641N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![641, 0, 0, 0, 0], ![191, 152, 1, 0, 0]] i)))

def I641N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![641, 0, 0, 0, 0], ![460, 467, 1, 0, 0]] i)))

def P641P0 : CertificateIrreducibleZModOfList' 641 1 2 9 [22, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [], [], [], [], [291], [619, 1]]]
 h' := ![![[0, 1], [1], [640], [487], [323], [250], [64], [8], [484], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P641P1 : CertificateIrreducibleZModOfList' 641 2 2 9 [191, 152, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [489, 640], [0, 1]]
 g := ![![[31, 443], [459], [320], [472], [609], [262], [137], [605, 28], [1]], ![[0, 198], [459], [320], [472], [609], [262], [137], [195, 613], [1]]]
 h' := ![![[489, 640], [626, 468], [49, 285], [69, 610], [321, 562], [156, 393], [612, 246], [466, 68], [450, 489], [0, 1]], ![[0, 1], [0, 173], [317, 356], [294, 31], [150, 79], [33, 248], [398, 395], [386, 573], [478, 152], [489, 640]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [108]]
 b := ![[], [258, 54]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P641P2 : CertificateIrreducibleZModOfList' 641 2 2 9 [460, 467, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [174, 640], [0, 1]]
 g := ![![[47, 125], [59], [360], [175], [160], [367], [529], [456, 149], [1]], ![[3, 516], [59], [360], [175], [160], [367], [529], [101, 492], [1]]]
 h' := ![![[174, 640], [283, 221], [316, 119], [276, 436], [500, 261], [541, 77], [573, 370], [488, 618], [181, 174], [0, 1]], ![[0, 1], [277, 420], [510, 522], [502, 205], [403, 380], [478, 564], [212, 271], [332, 23], [330, 467], [174, 640]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [431]]
 b := ![[], [161, 536]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A641 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 641 3 where
 D := ![[22, 1], [191, 152, 1], [460, 467, 1]]; D' := ![[22, 1], [191, 152, 1], [460, 467, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9, 9]
 n := ![1, 2, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P641P0
  | 1 => exact P641P1
  | 2 => exact P641P2

def C6410 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A641.D 0) 641 where
  n := 1
  w := ![![641, 0, 0, 0, 0], ![22, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C6411 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A641.D 1) 641 where
  n := 2
  w := ![![641, 0, 0, 0, 0], ![191, 152, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C6412 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A641.D 2) 641 where
  n := 2
  w := ![![641, 0, 0, 0, 0], ![460, 467, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K641 : KummerData 641 ![I641N0, I641N1, I641N2] ![641, 410881, 410881] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A641
  C := by
    intro i
    match i with
    | 0 => exact C6410
    | 1 => exact C6411
    | 2 => exact C6412
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 641 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp643 : Fact (Nat.Prime 643) := {out := by norm_num}

def I643N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![643, 0, 0, 0, 0], ![216, 1, 0, 0, 0]] i)))

def I643N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![643, 0, 0, 0, 0], ![861, 3115, 11255, -2184, 22728]] i)))

def P643P0 : CertificateIrreducibleZModOfList' 643 1 2 9 [216, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [515], [], [], [], [], [], [357], [427, 1]]]
 h' := ![![[0, 1], [642], [281], [359], [213], [451], [375], [48], [360], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P643P1 : CertificateIrreducibleZModOfList' 643 4 2 9 [213, 586, 360, 427, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [335, 92, 341, 436], [37, 253, 589, 375], [487, 297, 356, 475], [0, 1]]
 g := ![![[412, 561, 560, 397], [383, 413, 244, 156], [66, 207, 451], [100, 266, 435], [243, 350, 82], [318, 615, 574], [355], [216, 1], []], ![[164, 606, 307, 618, 358, 232], [37, 170, 4, 528, 93, 374], [307, 93, 290], [419, 208, 574], [344, 553, 433], [277, 383, 23], [5, 31, 595], [517, 131, 522, 232, 169, 78], [438, 328, 411]], ![[110, 259, 583, 268, 562, 241], [21, 364, 376, 31, 338, 9], [596, 556, 6], [640, 554, 611], [531, 313, 486], [100, 135, 321], [254, 541, 516], [303, 37, 251, 444, 476, 606], [424, 332, 451]], ![[227, 548, 60, 551, 230, 348], [209, 128, 559, 458, 81, 45], [263, 322, 356], [375, 82, 307], [128, 520, 577], [255, 283, 515], [568, 568, 212], [236, 318, 498, 346, 39, 538], [551, 83, 575]]]
 h' := ![![[335, 92, 341, 436], [82, 341, 523, 505], [463, 176, 539, 99], [595, 134, 590, 268], [26, 389, 100, 361], [374, 147, 29, 388], [256, 492, 308, 354], [288, 525, 100], [0, 0, 1], [0, 1]], ![[37, 253, 589, 375], [73, 201, 200, 358], [563, 374, 528, 401], [380, 589, 566, 93], [463, 281, 94, 354], [305, 621, 148, 305], [426, 207, 481, 548], [89, 546, 597, 509], [284, 24, 119, 526], [335, 92, 341, 436]], ![[487, 297, 356, 475], [391, 188, 286, 557], [123, 413, 318, 201], [20, 466, 533, 471], [344, 93, 157, 462], [417, 319, 601, 381], [66, 596, 48, 103], [99, 28, 471, 500], [434, 466, 629, 126], [37, 253, 589, 375]], ![[0, 1], [154, 556, 277, 509], [8, 323, 544, 585], [616, 97, 240, 454], [541, 523, 292, 109], [544, 199, 508, 212], [484, 634, 449, 281], [273, 187, 118, 277], [208, 153, 537, 634], [487, 297, 356, 475]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [180, 443, 175], []]
 b := ![[], [], [580, 33, 318, 171], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A643 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 643 2 where
 D := ![[216, 1], [213, 586, 360, 427, 1]]; D' := ![[216, 1], [213, 586, 360, 427, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P643P0
  | 1 => exact P643P1

def C6430 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A643.D 0) 643 where
  n := 1
  w := ![![643, 0, 0, 0, 0], ![216, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C6431 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A643.D 1) 643 where
  n := 4
  w := ![![643, 0, 0, 0, 0], ![861, 3115, 11255, -2184, 22728]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K643 : KummerData 643 ![I643N0, I643N1] ![643, 170940075601] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A643
  C := by
    intro i
    match i with
    | 0 => exact C6430
    | 1 => exact C6431
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 643 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


lemma PB18792I12_primes (p : ℕ) :
  p ∈ Set.range ![599, 601, 607, 613, 617, 619, 631, 641, 643] ↔ Nat.Prime p ∧ 593 < p ∧ p ≤ 643 := by
  rw [← List.mem_ofFn']
  convert primes_range 593 643 (by omega)
  decide

def PB18792I12 : PrimesBelowBoundCertificateInterval O 593 643 18792 where
  m := 9
  g := ![1, 3, 2, 2, 2, 1, 1, 3, 2]
  P := ![599, 601, 607, 613, 617, 619, 631, 641, 643]
  hP := PB18792I12_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I599N0]
    · exact ![I601N0, I601N1, I601N2]
    · exact ![I607N0, I607N1]
    · exact ![I613N0, I613N1]
    · exact ![I617N0, I617N1]
    · exact ![I619N0]
    · exact ![I631N0]
    · exact ![I641N0, I641N1, I641N2]
    · exact ![I643N0, I643N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · convert (containsPrimesAbove_of_KummerData K599) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K601) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K607) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K613) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K617) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K619) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K631) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K641) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K643) <;> rfl
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![77114156402999]
    · exact ![601, 361201, 361201]
    · exact ![607, 135754665601]
    · exact ![375769, 230346397]
    · exact ![380689, 234885113]
    · exact ![90876845839099]
    · exact ![100033806792151]
    · exact ![641, 410881, 410881]
    · exact ![643, 170940075601]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact (card_quot_of_KummerData K599)
    · exact (card_quot_of_KummerData K601)
    · exact (card_quot_of_KummerData K607)
    · exact (card_quot_of_KummerData K613)
    · exact (card_quot_of_KummerData K617)
    · exact (card_quot_of_KummerData K619)
    · exact (card_quot_of_KummerData K631)
    · exact (card_quot_of_KummerData K641)
    · exact (card_quot_of_KummerData K643)
  β := ![I601N0, I607N0, I641N0, I643N0]
  Il := ![[], [I601N0], [I607N0], [], [], [], [], [I641N0], [I643N0]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
