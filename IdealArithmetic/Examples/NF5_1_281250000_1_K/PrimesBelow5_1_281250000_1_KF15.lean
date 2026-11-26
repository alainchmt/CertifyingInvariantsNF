
import IdealArithmetic.Examples.NF5_1_281250000_1_K.RI5_1_281250000_1_K
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 

instance hp769 : Fact (Nat.Prime 769) := {out := by norm_num}

def I769N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![769, 0, 0, 0, 0], ![769, 0, 0, 3845, 0]] i)))

def P769P0 : CertificateIrreducibleZModOfList' 769 5 2 9 [469, 250, 0, 744, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [763, 391, 376, 339, 171], [420, 587, 644, 416, 478], [706, 656, 341, 319, 133], [418, 672, 177, 464, 756], [0, 1]]
 g := ![![[446, 430, 10, 23, 289], [464, 494, 35, 541], [543, 679, 482, 409], [515, 59, 127, 521], [489, 445, 328, 273], [684, 490, 498, 43], [389, 49, 0, 625], [0, 1], []], ![[750, 434, 399, 161, 531, 565, 425, 445], [320, 170, 276, 317], [580, 718, 202, 722], [358, 562, 1, 200], [149, 513, 344, 108], [41, 392, 3, 313], [318, 734, 409, 573], [473, 704, 467, 24], [400, 728, 301, 463, 425, 237, 98, 173]], ![[487, 691, 477, 180, 556, 354, 425, 696], [766, 516, 23, 95], [530, 590, 472, 272], [43, 506, 255, 738], [518, 281, 177, 749], [24, 322, 154, 36], [762, 173, 208, 235], [750, 608, 643, 484], [354, 185, 357, 732, 189, 416, 525, 434]], ![[421, 150, 633, 740, 430, 187, 705, 682], [226, 686, 501, 286], [149, 104, 614, 135], [306, 197, 575, 463], [307, 602, 414, 226], [53, 356, 187, 607], [191, 627, 727, 633], [253, 0, 73, 72], [369, 540, 679, 569, 378, 445, 376, 266]], ![[134, 120, 393, 56, 85, 644, 625, 156], [152, 594, 242, 543], [42, 176, 379, 129], [486, 355, 572, 589], [744, 145, 503, 273], [466, 191, 361, 9], [705, 598, 594, 726], [694, 218, 361, 638], [696, 437, 633, 616, 110, 376, 703, 110]]]
 h' := ![![[763, 391, 376, 339, 171], [723, 164, 232, 610, 752], [518, 361, 8, 278, 267], [154, 592, 337, 734, 81], [160, 594, 462, 268, 346], [616, 261, 61, 276, 647], [581, 502, 81, 316, 524], [0, 300, 519, 0, 25], [0, 0, 0, 1], [0, 1]], ![[420, 587, 644, 416, 478], [646, 485, 102, 307, 272], [636, 291, 588, 474, 487], [258, 730, 93, 738, 220], [123, 688, 156, 708, 208], [5, 554, 282, 497, 169], [3, 144, 214, 261, 632], [506, 314, 627, 631, 670], [589, 676, 55, 540, 454], [763, 391, 376, 339, 171]], ![[706, 656, 341, 319, 133], [353, 752, 520, 218, 548], [747, 547, 81, 95, 417], [418, 618, 495, 340, 444], [678, 704, 219, 42, 415], [117, 45, 59, 735, 642], [379, 752, 538, 141, 6], [279, 586, 564, 624, 641], [311, 610, 551, 102, 22], [420, 587, 644, 416, 478]], ![[418, 672, 177, 464, 756], [593, 517, 41, 627, 639], [656, 233, 364, 64, 70], [649, 573, 728, 390, 685], [361, 43, 421, 658, 181], [502, 288, 749, 50, 727], [639, 128, 185, 752, 379], [125, 325, 594, 151, 392], [611, 30, 7, 12, 740], [706, 656, 341, 319, 133]], ![[0, 1], [191, 389, 643, 545, 96], [280, 106, 497, 627, 297], [248, 563, 654, 105, 108], [649, 278, 280, 631, 388], [536, 390, 387, 749, 122], [240, 12, 520, 68, 766], [530, 13, 3, 132, 579], [27, 222, 156, 114, 322], [418, 672, 177, 464, 756]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [133, 639, 745, 137], [], [], []]
 b := ![[], [399, 552, 274, 151, 305], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A769 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 769 1 where
 D := ![[469, 250, 0, 744, 0, 1]]; D' := ![[469, 250, 0, 744, 0, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9]
 n := ![5]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P769P0

def C7690 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A769.D 0) 769 where
  n := 5
  w := ![![769, 0, 0, 0, 0], ![769, 0, 0, 3845, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K769 : KummerData 769 ![I769N0] ![268925323054849] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A769
  C := by
    intro i
    match i with
    | 0 => exact C7690
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 769 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp773 : Fact (Nat.Prime 773) := {out := by norm_num}

def I773N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![773, 0, 0, 0, 0], ![494, 92, 1, 0, 0]] i)))

def I773N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![773, 0, 0, 0, 0], ![159, 215, 681, 5, 0]] i)))

def P773P0 : CertificateIrreducibleZModOfList' 773 2 2 9 [494, 92, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [681, 772], [0, 1]]
 g := ![![[44, 54], [636], [125, 627], [446], [418], [719], [673], [398], [681, 1]], ![[487, 719], [636], [416, 146], [446], [418], [719], [673], [398], [589, 772]]]
 h' := ![![[681, 772], [24, 40], [90, 394], [765, 107], [28, 638], [599, 132], [572, 312], [275, 695], [614, 240], [0, 1]], ![[0, 1], [209, 733], [173, 379], [197, 666], [80, 135], [50, 641], [469, 461], [494, 78], [178, 533], [681, 772]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [417]]
 b := ![[], [315, 595]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P773P1 : CertificateIrreducibleZModOfList' 773 3 2 9 [159, 215, 681, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [552, 217, 275], [313, 555, 498], [0, 1]]
 g := ![![[507, 593, 56], [566, 600], [560, 680, 240], [398, 729], [328, 706], [274, 634], [217, 677], [140, 734], [1]], ![[471, 715, 233, 328], [376, 546], [743, 436, 430, 409], [259, 655], [292, 712], [371, 719], [555, 769], [676, 140], [416, 117, 184, 83]], ![[359, 709, 113, 769], [752, 498], [601, 651, 757, 154], [698, 234], [33, 153], [727, 36], [439, 202], [501, 301], [116, 453, 203, 690]]]
 h' := ![![[552, 217, 275], [601, 345, 176], [628, 543, 391], [446, 483, 570], [538, 340, 27], [509, 312, 55], [685, 57, 318], [702, 410, 357], [614, 558, 92], [0, 1]], ![[313, 555, 498], [317, 342, 78], [386, 518, 701], [494, 446, 62], [55, 670, 265], [467, 113, 375], [505, 565, 461], [114, 679, 139], [645, 632, 438], [552, 217, 275]], ![[0, 1], [326, 86, 519], [403, 485, 454], [128, 617, 141], [313, 536, 481], [368, 348, 343], [745, 151, 767], [668, 457, 277], [268, 356, 243], [313, 555, 498]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [457, 305], []]
 b := ![[], [0, 706, 27], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A773 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 773 2 where
 D := ![[494, 92, 1], [159, 215, 681, 1]]; D' := ![[494, 92, 1], [159, 215, 681, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P773P0
  | 1 => exact P773P1

def C7730 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A773.D 0) 773 where
  n := 2
  w := ![![773, 0, 0, 0, 0], ![494, 92, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C7731 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A773.D 1) 773 where
  n := 3
  w := ![![773, 0, 0, 0, 0], ![159, 215, 681, 5, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K773 : KummerData 773 ![I773N0, I773N1] ![597529, 461889917] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A773
  C := by
    intro i
    match i with
    | 0 => exact C7730
    | 1 => exact C7731
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 773 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp787 : Fact (Nat.Prime 787) := {out := by norm_num}

def I787N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![787, 0, 0, 0, 0], ![219, 429, 1, 0, 0]] i)))

def I787N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![787, 0, 0, 0, 0], ![128, 426, 358, 5, 0]] i)))

def P787P0 : CertificateIrreducibleZModOfList' 787 2 2 9 [219, 429, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [358, 786], [0, 1]]
 g := ![![[541, 306], [538, 225], [190], [641], [472, 555], [39], [625], [355], [358, 1]], ![[696, 481], [27, 562], [190], [641], [51, 232], [39], [625], [355], [716, 786]]]
 h' := ![![[358, 786], [228, 598], [376, 15], [744, 745], [516, 589], [684, 733], [170, 718], [41, 25], [298, 451], [0, 1]], ![[0, 1], [248, 189], [237, 772], [661, 42], [462, 198], [240, 54], [652, 69], [334, 762], [421, 336], [358, 786]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [596]]
 b := ![[], [174, 298]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P787P1 : CertificateIrreducibleZModOfList' 787 3 2 9 [128, 426, 358, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [300, 698, 329], [129, 88, 458], [0, 1]]
 g := ![![[219, 430, 551], [461, 776, 142], [16, 568], [463, 106], [150, 619, 491], [207, 268], [506, 592], [622, 670], [1]], ![[231, 251, 711, 279], [423, 759, 88, 451], [755, 760], [586, 692], [222, 633, 306, 779], [32, 556], [430, 368], [711, 594], [180, 99, 422, 326]], ![[202, 614, 439, 140], [707, 565, 456, 220], [663, 769], [533, 139], [198, 286, 472, 537], [697, 199], [51, 429], [741, 241], [582, 673, 673, 461]]]
 h' := ![![[300, 698, 329], [17, 79, 514], [650, 461, 85], [304, 50, 617], [475, 439, 154], [304, 82, 255], [559, 104, 292], [515, 720, 341], [659, 361, 429], [0, 1]], ![[129, 88, 458], [364, 172, 393], [87, 316, 175], [266, 217, 703], [36, 514, 583], [241, 261, 624], [425, 51, 100], [654, 356, 95], [174, 624, 695], [300, 698, 329]], ![[0, 1], [612, 536, 667], [141, 10, 527], [3, 520, 254], [669, 621, 50], [153, 444, 695], [35, 632, 395], [76, 498, 351], [22, 589, 450], [129, 88, 458]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [462, 344], []]
 b := ![[], [603, 695, 530], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A787 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 787 2 where
 D := ![[219, 429, 1], [128, 426, 358, 1]]; D' := ![[219, 429, 1], [128, 426, 358, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P787P0
  | 1 => exact P787P1

def C7870 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A787.D 0) 787 where
  n := 2
  w := ![![787, 0, 0, 0, 0], ![219, 429, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C7871 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A787.D 1) 787 where
  n := 3
  w := ![![787, 0, 0, 0, 0], ![128, 426, 358, 5, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K787 : KummerData 787 ![I787N0, I787N1] ![619369, 487443403] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A787
  C := by
    intro i
    match i with
    | 0 => exact C7870
    | 1 => exact C7871
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 787 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp797 : Fact (Nat.Prime 797) := {out := by norm_num}

def I797N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![797, 0, 0, 0, 0], ![452, 1, 0, 0, 0]] i)))

def I797N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![797, 0, 0, 0, 0], ![486, 733, 252, 1725, 10]] i)))

def P797P0 : CertificateIrreducibleZModOfList' 797 1 2 9 [452, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [369], [634], [647], [], [], [], [272, 345, 1]]]
 h' := ![![[0, 1], [796], [582], [352], [55], [759], [566], [195], [591], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P797P1 : CertificateIrreducibleZModOfList' 797 4 2 9 [486, 733, 247, 345, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [683, 281, 364, 492], [518, 707, 297, 146], [48, 605, 136, 159], [0, 1]]
 g := ![![[689, 171, 15, 540], [755, 550, 100], [8, 608, 431, 46], [56, 437, 356, 337], [265, 411, 482, 519], [714, 529, 329], [329, 66, 239], [25, 452, 1], []], ![[673, 183, 705, 583, 61, 597], [423, 700, 679], [252, 770, 717, 696, 134, 75], [72, 101, 387, 153, 221, 129], [221, 636, 346, 367, 97, 301], [207, 601, 573], [41, 415, 490], [744, 255, 64], [340, 763, 558, 519, 149, 575]], ![[723, 596, 359, 412, 624, 91], [200, 450, 460], [412, 390, 236, 81, 533, 139], [480, 10, 14, 13, 140, 269], [759, 747, 249, 48, 765, 229], [109, 256, 240], [328, 662, 757], [363, 576, 428], [503, 741, 36, 317, 443, 648]], ![[411, 717, 703, 330, 84, 505], [477, 58, 608], [656, 475, 524, 788, 620, 679], [714, 86, 756, 61, 345, 387], [108, 301, 80, 119, 567, 60], [73, 175, 133], [347, 66, 438], [312, 787, 676], [12, 89, 668, 204, 183, 408]]]
 h' := ![![[683, 281, 364, 492], [332, 471, 332, 301], [97, 289, 240, 787], [679, 585, 598, 722], [324, 406, 649, 298], [93, 505, 451, 336], [72, 348, 50, 168], [602, 306, 748, 142], [0, 0, 0, 1], [0, 1]], ![[518, 707, 297, 146], [651, 617, 454, 222], [643, 19, 18, 704], [626, 616, 627, 694], [248, 704, 276, 768], [477, 71, 30, 742], [448, 225, 393, 305], [701, 253, 534, 343], [615, 94, 51, 8], [683, 281, 364, 492]], ![[48, 605, 136, 159], [86, 397, 640, 684], [85, 740, 141, 310], [569, 485, 479, 57], [427, 396, 194, 52], [773, 167, 790, 478], [82, 236, 222, 65], [147, 693, 154, 449], [35, 250, 706, 762], [518, 707, 297, 146]], ![[0, 1], [609, 109, 168, 387], [730, 546, 398, 590], [694, 705, 687, 121], [697, 88, 475, 476], [321, 54, 323, 38], [368, 785, 132, 259], [75, 342, 158, 660], [353, 453, 40, 26], [48, 605, 136, 159]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [22, 219, 754], []]
 b := ![[], [], [224, 12, 226, 770], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A797 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 797 2 where
 D := ![[452, 1], [486, 733, 247, 345, 1]]; D' := ![[452, 1], [486, 733, 247, 345, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P797P0
  | 1 => exact P797P1

def C7970 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A797.D 0) 797 where
  n := 1
  w := ![![797, 0, 0, 0, 0], ![452, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C7971 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A797.D 1) 797 where
  n := 4
  w := ![![797, 0, 0, 0, 0], ![486, 733, 252, 1725, 10]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K797 : KummerData 797 ![I797N0, I797N1] ![797, 403490473681] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A797
  C := by
    intro i
    match i with
    | 0 => exact C7970
    | 1 => exact C7971
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 797 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp809 : Fact (Nat.Prime 809) := {out := by norm_num}

def I809N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![809, 0, 0, 0, 0], ![407, 1, 0, 0, 0]] i)))

def I809N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![809, 0, 0, 0, 0], ![596, 1, 0, 0, 0]] i)))

def I809N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![809, 0, 0, 0, 0], ![331, 525, 615, 5, 0]] i)))

def P809P0 : CertificateIrreducibleZModOfList' 809 1 2 9 [407, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [324], [], [16], [], [], [613, 402, 1]]]
 h' := ![![[0, 1], [1], [1], [808], [791], [769], [805], [636], [490], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P809P1 : CertificateIrreducibleZModOfList' 809 1 2 9 [596, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [594], [], [89], [], [], [65, 213, 1]]]
 h' := ![![[0, 1], [1], [808], [318], [341], [350], [728], [374], [92], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P809P2 : CertificateIrreducibleZModOfList' 809 3 2 9 [331, 525, 615, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [52, 244, 722], [142, 564, 87], [0, 1]]
 g := ![![[474, 754, 277], [788, 19], [479, 774], [287, 632, 801], [178, 242], [697, 545, 20], [182, 649], [327, 422], [1]], ![[609, 266, 247, 781], [230, 688], [760, 521], [369, 214, 685, 173], [401, 605], [738, 126, 186, 63], [553, 97], [62, 348], [756, 176, 84, 23]], ![[638, 700, 93, 354], [370, 14], [792, 73], [47, 708, 797, 801], [722, 101], [251, 95, 744, 342], [745, 172], [407, 231], [32, 440, 670, 786]]]
 h' := ![![[52, 244, 722], [18, 424, 52], [237, 66, 309], [465, 559, 699], [78, 404, 243], [667, 356, 282], [306, 357, 248], [515, 597, 411], [478, 284, 194], [0, 1]], ![[142, 564, 87], [788, 625, 530], [41, 459, 262], [614, 359, 160], [592, 338, 779], [120, 695, 254], [95, 312, 407], [382, 37, 267], [396, 16, 572], [52, 244, 722]], ![[0, 1], [308, 569, 227], [401, 284, 238], [671, 700, 759], [573, 67, 596], [779, 567, 273], [594, 140, 154], [742, 175, 131], [162, 509, 43], [142, 564, 87]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [806, 142], []]
 b := ![[], [797, 536, 262], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A809 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 809 3 where
 D := ![[407, 1], [596, 1], [331, 525, 615, 1]]; D' := ![[407, 1], [596, 1], [331, 525, 615, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9, 9]
 n := ![1, 1, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P809P0
  | 1 => exact P809P1
  | 2 => exact P809P2

def C8090 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A809.D 0) 809 where
  n := 1
  w := ![![809, 0, 0, 0, 0], ![407, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C8091 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A809.D 1) 809 where
  n := 1
  w := ![![809, 0, 0, 0, 0], ![596, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C8092 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A809.D 2) 809 where
  n := 3
  w := ![![809, 0, 0, 0, 0], ![331, 525, 615, 5, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K809 : KummerData 809 ![I809N0, I809N1, I809N2] ![809, 809, 529475129] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A809
  C := by
    intro i
    match i with
    | 0 => exact C8090
    | 1 => exact C8091
    | 2 => exact C8092
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 809 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp811 : Fact (Nat.Prime 811) := {out := by norm_num}

def I811N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![811, 0, 0, 0, 0], ![255, 1, 0, 0, 0]] i)))

def I811N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![811, 0, 0, 0, 0], ![273, 1, 0, 0, 0]] i)))

def I811N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![811, 0, 0, 0, 0], ![739, 717, 283, 5, 0]] i)))

def P811P0 : CertificateIrreducibleZModOfList' 811 1 2 9 [255, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [617], [], [605], [], [69], [], [], [145, 556, 1]]]
 h' := ![![[0, 1], [810], [163], [626], [184], [247], [99], [76], [331], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P811P1 : CertificateIrreducibleZModOfList' 811 1 2 9 [273, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [710], [], [477], [], [764], [], [], [728, 538, 1]]]
 h' := ![![[0, 1], [810], [39], [350], [750], [666], [213], [779], [762], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P811P2 : CertificateIrreducibleZModOfList' 811 3 2 9 [739, 717, 283, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [625, 27, 692], [714, 783, 119], [0, 1]]
 g := ![![[65, 638, 529], [432, 436, 49], [532, 511], [17, 673, 372], [215, 51], [49, 619, 238], [390, 741], [152, 611], [1]], ![[33, 730, 672, 205], [416, 380, 429, 121], [285, 391], [118, 57, 3, 41], [247, 37], [199, 407, 354, 464], [226, 465], [796, 324], [566, 552, 655, 99]], ![[27, 683, 671, 493], [479, 348, 81, 364], [336, 283], [516, 452, 772, 375], [86, 203], [319, 543, 128, 272], [113, 701], [793, 580], [227, 430, 656, 712]]]
 h' := ![![[625, 27, 692], [286, 42, 23], [446, 79, 804], [413, 220, 634], [438, 21, 302], [284, 482, 594], [49, 281, 183], [719, 448, 344], [72, 94, 528], [0, 1]], ![[714, 783, 119], [155, 149, 35], [269, 705, 527], [312, 650, 673], [490, 539, 399], [575, 375, 622], [646, 314, 365], [502, 361, 314], [631, 765, 793], [625, 27, 692]], ![[0, 1], [420, 620, 753], [247, 27, 291], [392, 752, 315], [551, 251, 110], [6, 765, 406], [455, 216, 263], [595, 2, 153], [637, 763, 301], [714, 783, 119]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [98, 596], []]
 b := ![[], [385, 166, 632], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A811 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 811 3 where
 D := ![[255, 1], [273, 1], [739, 717, 283, 1]]; D' := ![[255, 1], [273, 1], [739, 717, 283, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9, 9]
 n := ![1, 1, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P811P0
  | 1 => exact P811P1
  | 2 => exact P811P2

def C8110 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A811.D 0) 811 where
  n := 1
  w := ![![811, 0, 0, 0, 0], ![255, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C8111 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A811.D 1) 811 where
  n := 1
  w := ![![811, 0, 0, 0, 0], ![273, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C8112 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A811.D 2) 811 where
  n := 3
  w := ![![811, 0, 0, 0, 0], ![739, 717, 283, 5, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K811 : KummerData 811 ![I811N0, I811N1, I811N2] ![811, 811, 533411731] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A811
  C := by
    intro i
    match i with
    | 0 => exact C8110
    | 1 => exact C8111
    | 2 => exact C8112
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 811 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp821 : Fact (Nat.Prime 821) := {out := by norm_num}

def I821N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![821, 0, 0, 0, 0], ![613, 1, 0, 0, 0]] i)))

def I821N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![821, 0, 0, 0, 0], ![732, 1, 0, 0, 0]] i)))

def I821N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![821, 0, 0, 0, 0], ![273, 708, 297, 5, 0]] i)))

def P821P0 : CertificateIrreducibleZModOfList' 821 1 2 9 [613, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [42], [], [136], [183], [], [], [572, 208, 1]]]
 h' := ![![[0, 1], [820], [526], [306], [374], [298], [132], [656], [752], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P821P1 : CertificateIrreducibleZModOfList' 821 1 2 9 [732, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [369], [], [122], [720], [], [], [532, 89, 1]]]
 h' := ![![[0, 1], [1], [1], [564], [185], [42], [647], [652], [551], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P821P2 : CertificateIrreducibleZModOfList' 821 3 2 9 [273, 708, 297, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [368, 132, 546], [156, 688, 275], [0, 1]]
 g := ![![[552, 269, 785], [22, 263], [23, 612, 441], [235, 741], [454, 653, 796], [535, 498, 706], [386, 741], [237, 362], [1]], ![[445, 753, 266, 66], [636, 701], [472, 96, 574, 561], [167, 373], [309, 738, 816, 620], [101, 25, 155, 391], [207, 225], [660, 680], [521, 615, 587, 697]], ![[590, 820, 136, 77], [674, 607], [243, 437, 299, 479], [138, 122], [87, 525, 52, 366], [719, 717, 99, 736], [200, 320], [153, 814], [694, 445, 776, 124]]]
 h' := ![![[368, 132, 546], [341, 559, 128], [289, 101, 147], [724, 796, 800], [29, 609, 131], [83, 550, 167], [286, 43, 401], [797, 80, 131], [548, 113, 524], [0, 1]], ![[156, 688, 275], [646, 678, 19], [197, 553, 292], [600, 754, 637], [431, 600, 648], [511, 523, 591], [590, 551, 522], [283, 557, 806], [311, 355, 216], [368, 132, 546]], ![[0, 1], [408, 405, 674], [171, 167, 382], [30, 92, 205], [49, 433, 42], [181, 569, 63], [508, 227, 719], [393, 184, 705], [301, 353, 81], [156, 688, 275]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [201, 475], []]
 b := ![[], [190, 311, 151], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A821 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 821 3 where
 D := ![[613, 1], [732, 1], [273, 708, 297, 1]]; D' := ![[613, 1], [732, 1], [273, 708, 297, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9, 9]
 n := ![1, 1, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P821P0
  | 1 => exact P821P1
  | 2 => exact P821P2

def C8210 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A821.D 0) 821 where
  n := 1
  w := ![![821, 0, 0, 0, 0], ![613, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C8211 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A821.D 1) 821 where
  n := 1
  w := ![![821, 0, 0, 0, 0], ![732, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C8212 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A821.D 2) 821 where
  n := 3
  w := ![![821, 0, 0, 0, 0], ![273, 708, 297, 5, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K821 : KummerData 821 ![I821N0, I821N1, I821N2] ![821, 821, 553387661] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A821
  C := by
    intro i
    match i with
    | 0 => exact C8210
    | 1 => exact C8211
    | 2 => exact C8212
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 821 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp823 : Fact (Nat.Prime 823) := {out := by norm_num}

def I823N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![823, 0, 0, 0, 0], ![349, 1, 0, 0, 0]] i)))

def I823N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![823, 0, 0, 0, 0], ![704, 1, 0, 0, 0]] i)))

def I823N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![823, 0, 0, 0, 0], ![784, 1, 0, 0, 0]] i)))

def I823N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![823, 0, 0, 0, 0], ![542, 632, 1, 0, 0]] i)))

def P823P0 : CertificateIrreducibleZModOfList' 823 1 2 9 [349, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [158], [200], [], [289], [606], [], [], [820, 474, 1]]]
 h' := ![![[0, 1], [822], [155], [452], [368], [17], [729], [796], [224], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P823P1 : CertificateIrreducibleZModOfList' 823 1 2 9 [704, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [83], [25], [], [812], [269], [], [], [170, 119, 1]]]
 h' := ![![[0, 1], [1], [506], [818], [337], [737], [632], [513], [478], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P823P2 : CertificateIrreducibleZModOfList' 823 1 2 9 [784, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [211], [257], [], [71], [140], [], [], [698, 39, 1]]]
 h' := ![![[0, 1], [822], [147], [293], [300], [522], [741], [677], [63], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P823P3 : CertificateIrreducibleZModOfList' 823 2 2 9 [542, 632, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [191, 822], [0, 1]]
 g := ![![[399, 607], [546, 349], [427, 513], [31], [706, 795], [622, 493], [128], [459], [191, 1]], ![[293, 216], [542, 474], [473, 310], [31], [296, 28], [140, 330], [128], [459], [382, 822]]]
 h' := ![![[191, 822], [348, 333], [652, 600], [684, 345], [43, 50], [306, 728], [13, 359], [293, 626], [176, 550], [0, 1]], ![[0, 1], [580, 490], [32, 223], [739, 478], [540, 773], [267, 95], [273, 464], [524, 197], [705, 273], [191, 822]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [257]]
 b := ![[], [279, 540]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A823 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 823 4 where
 D := ![[349, 1], [704, 1], [784, 1], [542, 632, 1]]; D' := ![[349, 1], [704, 1], [784, 1], [542, 632, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9, 9, 9]
 n := ![1, 1, 1, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P823P0
  | 1 => exact P823P1
  | 2 => exact P823P2
  | 3 => exact P823P3

def C8230 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A823.D 0) 823 where
  n := 1
  w := ![![823, 0, 0, 0, 0], ![349, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C8231 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A823.D 1) 823 where
  n := 1
  w := ![![823, 0, 0, 0, 0], ![704, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C8232 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A823.D 2) 823 where
  n := 1
  w := ![![823, 0, 0, 0, 0], ![784, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C8233 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A823.D 3) 823 where
  n := 2
  w := ![![823, 0, 0, 0, 0], ![542, 632, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K823 : KummerData 823 ![I823N0, I823N1, I823N2, I823N3] ![823, 823, 823, 677329] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A823
  C := by
    intro i
    match i with
    | 0 => exact C8230
    | 1 => exact C8231
    | 2 => exact C8232
    | 3 => exact C8233
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 823 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp827 : Fact (Nat.Prime 827) := {out := by norm_num}

def I827N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![827, 0, 0, 0, 0], ![538, 1, 0, 0, 0]] i)))

def I827N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![827, 0, 0, 0, 0], ![436, 138, 801, 1445, 10]] i)))

def P827P0 : CertificateIrreducibleZModOfList' 827 1 2 9 [538, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [641], [], [139], [157], [75], [], [], [821, 289, 1]]]
 h' := ![![[0, 1], [1], [681], [475], [715], [173], [344], [611], [747], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P827P1 : CertificateIrreducibleZModOfList' 827 4 2 9 [436, 138, 796, 289, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [688, 32, 448, 622], [105, 237, 215, 366], [572, 557, 164, 666], [0, 1]]
 g := ![![[484, 162, 406, 496], [672, 677, 689, 580], [58, 426, 183], [391, 41, 365, 777], [11, 779, 264, 501], [478, 725, 590, 197], [639, 201, 385], [25, 538, 1], []], ![[321, 486, 353, 444, 263, 562], [244, 139, 589, 384, 282, 131], [178, 212, 249], [169, 81, 327, 442, 444, 531], [459, 459, 447, 533, 44, 597], [354, 724, 250, 500, 163, 733], [808, 386, 485], [8, 339, 675], [498, 334, 628, 60, 771, 561]], ![[573, 442, 417, 433, 179, 239], [367, 76, 599, 352, 620, 251], [577, 555, 31], [103, 281, 368, 530, 68, 532], [685, 814, 666, 769, 684, 151], [180, 192, 796, 718, 226, 721], [393, 722, 282], [345, 303, 457], [618, 275, 273, 37, 146, 28]], ![[143, 239, 450, 508, 521, 774], [471, 328, 618, 755, 810, 108], [50, 762, 14], [448, 283, 768, 763, 345, 493], [280, 343, 549, 128, 426, 573], [126, 208, 682, 28, 112, 3], [391, 625, 623], [608, 645, 478], [510, 686, 213, 446, 395, 588]]]
 h' := ![![[688, 32, 448, 622], [593, 319, 493, 540], [113, 800, 461, 492], [713, 380, 804, 513], [166, 405, 503, 217], [823, 272, 762, 341], [794, 388, 369, 32], [678, 158, 525, 218], [0, 0, 0, 1], [0, 1]], ![[105, 237, 215, 366], [273, 815, 764, 256], [567, 263, 707, 373], [284, 403, 717, 420], [281, 372, 410, 643], [825, 37, 213, 52], [246, 625, 735, 587], [349, 211, 347, 106], [23, 527, 49, 205], [688, 32, 448, 622]], ![[572, 557, 164, 666], [575, 565, 660, 465], [240, 227, 88, 31], [569, 503, 706, 692], [174, 623, 516, 106], [374, 39, 683, 311], [751, 626, 686, 610], [535, 279, 596, 44], [806, 381, 438, 710], [105, 237, 215, 366]], ![[0, 1], [223, 782, 564, 393], [562, 364, 398, 758], [686, 368, 254, 29], [475, 254, 225, 688], [57, 479, 823, 123], [139, 15, 691, 425], [674, 179, 186, 459], [78, 746, 340, 738], [572, 557, 164, 666]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [52, 382, 386], []]
 b := ![[], [], [44, 381, 20, 130], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A827 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 827 2 where
 D := ![[538, 1], [436, 138, 796, 289, 1]]; D' := ![[538, 1], [436, 138, 796, 289, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P827P0
  | 1 => exact P827P1

def C8270 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A827.D 0) 827 where
  n := 1
  w := ![![827, 0, 0, 0, 0], ![538, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C8271 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A827.D 1) 827 where
  n := 4
  w := ![![827, 0, 0, 0, 0], ![436, 138, 801, 1445, 10]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K827 : KummerData 827 ![I827N0, I827N1] ![827, 467758877041] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A827
  C := by
    intro i
    match i with
    | 0 => exact C8270
    | 1 => exact C8271
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 827 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


lemma PB1045I15_primes (p : ℕ) :
  p ∈ Set.range ![769, 773, 787, 797, 809, 811, 821, 823, 827] ↔ Nat.Prime p ∧ 761 < p ∧ p ≤ 827 := by
  rw [← List.mem_ofFn']
  convert primes_range 761 827 (by omega)
  decide

def PB1045I15 : PrimesBelowBoundCertificateInterval O 761 827 1045 where
  m := 9
  g := ![1, 2, 2, 2, 3, 3, 3, 4, 2]
  P := ![769, 773, 787, 797, 809, 811, 821, 823, 827]
  hP := PB1045I15_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I769N0]
    · exact ![I773N0, I773N1]
    · exact ![I787N0, I787N1]
    · exact ![I797N0, I797N1]
    · exact ![I809N0, I809N1, I809N2]
    · exact ![I811N0, I811N1, I811N2]
    · exact ![I821N0, I821N1, I821N2]
    · exact ![I823N0, I823N1, I823N2, I823N3]
    · exact ![I827N0, I827N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · convert (containsPrimesAbove_of_KummerData K769) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K773) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K787) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K797) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K809) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K811) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K821) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K823) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K827) <;> rfl
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![268925323054849]
    · exact ![597529, 461889917]
    · exact ![619369, 487443403]
    · exact ![797, 403490473681]
    · exact ![809, 809, 529475129]
    · exact ![811, 811, 533411731]
    · exact ![821, 821, 553387661]
    · exact ![823, 823, 823, 677329]
    · exact ![827, 467758877041]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact (card_quot_of_KummerData K769)
    · exact (card_quot_of_KummerData K773)
    · exact (card_quot_of_KummerData K787)
    · exact (card_quot_of_KummerData K797)
    · exact (card_quot_of_KummerData K809)
    · exact (card_quot_of_KummerData K811)
    · exact (card_quot_of_KummerData K821)
    · exact (card_quot_of_KummerData K823)
    · exact (card_quot_of_KummerData K827)
  β := ![I797N0, I809N0, I809N1, I811N0, I811N1, I821N0, I821N1, I823N0, I823N1, I823N2, I827N0]
  Il := ![[], [], [], [I797N0], [I809N0, I809N1], [I811N0, I811N1], [I821N0, I821N1], [I823N0, I823N1, I823N2], [I827N0]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
