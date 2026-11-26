
import IdealArithmetic.Examples.NF5_1_281250000_1_K.RI5_1_281250000_1_K
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 

instance hp887 : Fact (Nat.Prime 887) := {out := by norm_num}

def I887N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![887, 0, 0, 0, 0], ![287, 1, 0, 0, 0]] i)))

def I887N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![887, 0, 0, 0, 0], ![444, 500, 745, 3000, 10]] i)))

def P887P0 : CertificateIrreducibleZModOfList' 887 1 2 9 [287, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [853], [352], [], [581], [169], [445], [], [765, 600, 1]]]
 h' := ![![[0, 1], [1], [94], [81], [9], [282], [13], [728], [421], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P887P1 : CertificateIrreducibleZModOfList' 887 4 2 9 [444, 500, 740, 600, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [433, 581, 191, 802], [876, 154, 415, 535], [752, 151, 281, 437], [0, 1]]
 g := ![![[21, 56, 104, 208], [747, 37, 305, 518], [193, 479, 326, 527], [621, 366, 595], [105, 523, 22, 774], [423, 333, 308, 546], [342, 599, 394, 32], [25, 287, 1], []], ![[245, 36, 473, 806, 519, 199], [87, 394, 218, 226, 22, 295], [823, 869, 848, 236, 596, 563], [1, 628, 798], [102, 3, 680, 556, 849, 34], [315, 741, 739, 82, 61, 348], [267, 510, 35, 732, 468, 855], [223, 506, 325], [549, 26, 117, 395, 417, 566]], ![[335, 90, 676, 438, 235, 5], [327, 325, 14, 316, 515, 187], [622, 632, 876, 191, 743, 522], [132, 396, 643], [25, 675, 394, 438, 539, 55], [546, 221, 407, 210, 91, 295], [382, 785, 495, 355, 95, 717], [541, 69, 176], [16, 531, 17, 784, 315, 469]], ![[463, 664, 116, 568, 581, 165], [627, 293, 829, 524, 500, 239], [281, 691, 53, 6, 830, 845], [243, 753, 825], [801, 140, 694, 856, 101, 621], [14, 132, 252, 840, 387, 328], [382, 107, 116, 791, 581, 788], [15, 152, 282], [726, 119, 205, 500, 595, 58]]]
 h' := ![![[433, 581, 191, 802], [70, 129, 550, 120], [347, 651, 709, 489], [450, 410, 530, 635], [391, 619, 601, 408], [232, 740, 272, 420], [716, 713, 583, 762], [431, 218, 764, 79], [0, 0, 0, 1], [0, 1]], ![[876, 154, 415, 535], [76, 772, 757, 72], [630, 141, 363, 719], [595, 395, 599, 825], [622, 227, 350, 249], [135, 410, 226, 169], [375, 18, 654, 137], [473, 340, 725, 75], [231, 809, 835, 150], [433, 581, 191, 802]], ![[752, 151, 281, 437], [713, 496, 265, 578], [342, 853, 571, 210], [681, 304, 323, 828], [681, 661, 394, 319], [58, 377, 773, 660], [165, 616, 114, 735], [467, 11, 450, 225], [435, 182, 287, 198], [876, 154, 415, 535]], ![[0, 1], [694, 377, 202, 117], [93, 129, 131, 356], [111, 665, 322, 373], [26, 267, 429, 798], [356, 247, 503, 525], [792, 427, 423, 140], [521, 318, 722, 508], [687, 783, 652, 538], [752, 151, 281, 437]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [155, 400, 523], []]
 b := ![[], [], [773, 156, 174, 130], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A887 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 887 2 where
 D := ![[287, 1], [444, 500, 740, 600, 1]]; D' := ![[287, 1], [444, 500, 740, 600, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P887P0
  | 1 => exact P887P1

def C8870 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A887.D 0) 887 where
  n := 1
  w := ![![887, 0, 0, 0, 0], ![287, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C8871 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A887.D 1) 887 where
  n := 4
  w := ![![887, 0, 0, 0, 0], ![444, 500, 745, 3000, 10]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K887 : KummerData 887 ![I887N0, I887N1] ![887, 619005459361] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A887
  C := by
    intro i
    match i with
    | 0 => exact C8870
    | 1 => exact C8871
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 887 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp907 : Fact (Nat.Prime 907) := {out := by norm_num}

def I907N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![907, 0, 0, 0, 0], ![374, 1, 0, 0, 0]] i)))

def I907N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![907, 0, 0, 0, 0], ![450, 1, 0, 0, 0]] i)))

def I907N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![907, 0, 0, 0, 0], ![743, 1, 0, 0, 0]] i)))

def I907N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![907, 0, 0, 0, 0], ![610, 247, 1, 0, 0]] i)))

def P907P0 : CertificateIrreducibleZModOfList' 907 1 2 9 [374, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [502], [], [733], [], [], [], [286], [198, 533, 1]]]
 h' := ![![[0, 1], [1], [285], [679], [476], [399], [216], [62], [322], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P907P1 : CertificateIrreducibleZModOfList' 907 1 2 9 [450, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [389], [], [520], [], [], [], [662], [239, 457, 1]]]
 h' := ![![[0, 1], [1], [36], [6], [372], [122], [863], [503], [383], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P907P2 : CertificateIrreducibleZModOfList' 907 1 2 9 [743, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [271], [], [654], [], [], [], [394], [593, 164, 1]]]
 h' := ![![[0, 1], [1], [294], [230], [246], [309], [797], [219], [203], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P907P3 : CertificateIrreducibleZModOfList' 907 2 2 9 [610, 247, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [660, 906], [0, 1]]
 g := ![![[103, 303], [21, 16], [409], [111, 171], [779], [263], [139], [370, 850], [660, 1]], ![[543, 604], [604, 891], [409], [503, 736], [779], [263], [139], [844, 57], [413, 906]]]
 h' := ![![[660, 906], [795, 702], [297, 903], [315, 467], [740, 639], [524, 430], [56, 349], [143, 394], [108, 537], [0, 1]], ![[0, 1], [638, 205], [378, 4], [155, 440], [725, 268], [433, 477], [18, 558], [781, 513], [798, 370], [660, 906]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [94]]
 b := ![[], [816, 47]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A907 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 907 4 where
 D := ![[374, 1], [450, 1], [743, 1], [610, 247, 1]]; D' := ![[374, 1], [450, 1], [743, 1], [610, 247, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9, 9, 9]
 n := ![1, 1, 1, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P907P0
  | 1 => exact P907P1
  | 2 => exact P907P2
  | 3 => exact P907P3

def C9070 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A907.D 0) 907 where
  n := 1
  w := ![![907, 0, 0, 0, 0], ![374, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C9071 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A907.D 1) 907 where
  n := 1
  w := ![![907, 0, 0, 0, 0], ![450, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C9072 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A907.D 2) 907 where
  n := 1
  w := ![![907, 0, 0, 0, 0], ![743, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C9073 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A907.D 3) 907 where
  n := 2
  w := ![![907, 0, 0, 0, 0], ![610, 247, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K907 : KummerData 907 ![I907N0, I907N1, I907N2, I907N3] ![907, 907, 907, 822649] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A907
  C := by
    intro i
    match i with
    | 0 => exact C9070
    | 1 => exact C9071
    | 2 => exact C9072
    | 3 => exact C9073
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 907 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp911 : Fact (Nat.Prime 911) := {out := by norm_num}

def I911N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![911, 0, 0, 0, 0], ![475, 1, 0, 0, 0]] i)))

def I911N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![911, 0, 0, 0, 0], ![864, 56, 1, 0, 0]] i)))

def I911N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![911, 0, 0, 0, 0], ![303, 380, 1, 0, 0]] i)))

def P911P0 : CertificateIrreducibleZModOfList' 911 1 2 9 [475, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [257], [882], [610], [], [], [], [169], [608, 436, 1]]]
 h' := ![![[0, 1], [910], [110], [859], [39], [366], [517], [804], [898], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P911P1 : CertificateIrreducibleZModOfList' 911 2 2 9 [864, 56, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [855, 910], [0, 1]]
 g := ![![[464, 659], [377, 23], [231, 119], [206, 832], [231], [877], [867], [839, 258], [855, 1]], ![[0, 252], [0, 888], [855, 792], [75, 79], [231], [877], [867], [56, 653], [799, 910]]]
 h' := ![![[855, 910], [410, 170], [836, 80], [572, 706], [440, 283], [180, 267], [851, 416], [260, 851], [101, 450], [0, 1]], ![[0, 1], [0, 741], [0, 831], [209, 205], [79, 628], [715, 644], [330, 495], [887, 60], [409, 461], [855, 910]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [558]]
 b := ![[], [524, 279]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P911P2 : CertificateIrreducibleZModOfList' 911 2 2 9 [303, 380, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [531, 910], [0, 1]]
 g := ![![[341, 471], [510, 535], [775, 502], [413, 618], [484], [693], [298], [234, 684], [531, 1]], ![[828, 440], [363, 376], [414, 409], [611, 293], [484], [693], [298], [860, 227], [151, 910]]]
 h' := ![![[531, 910], [340, 115], [213, 688], [579, 130], [495, 833], [501, 889], [545, 728], [156, 412], [354, 159], [0, 1]], ![[0, 1], [368, 796], [230, 223], [373, 781], [72, 78], [662, 22], [849, 183], [288, 499], [60, 752], [531, 910]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [894]]
 b := ![[], [207, 447]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A911 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 911 3 where
 D := ![[475, 1], [864, 56, 1], [303, 380, 1]]; D' := ![[475, 1], [864, 56, 1], [303, 380, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9, 9]
 n := ![1, 2, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P911P0
  | 1 => exact P911P1
  | 2 => exact P911P2

def C9110 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A911.D 0) 911 where
  n := 1
  w := ![![911, 0, 0, 0, 0], ![475, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C9111 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A911.D 1) 911 where
  n := 2
  w := ![![911, 0, 0, 0, 0], ![864, 56, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C9112 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A911.D 2) 911 where
  n := 2
  w := ![![911, 0, 0, 0, 0], ![303, 380, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K911 : KummerData 911 ![I911N0, I911N1, I911N2] ![911, 829921, 829921] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A911
  C := by
    intro i
    match i with
    | 0 => exact C9110
    | 1 => exact C9111
    | 2 => exact C9112
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 911 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp919 : Fact (Nat.Prime 919) := {out := by norm_num}

def I919N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![919, 0, 0, 0, 0], ![919, 0, 0, 4595, 0]] i)))

def P919P0 : CertificateIrreducibleZModOfList' 919 5 2 9 [619, 250, 0, 894, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [65, 535, 524, 648, 721], [35, 728, 446, 551, 2], [598, 820, 917, 761, 209], [221, 673, 870, 797, 906], [0, 1]]
 g := ![![[812, 795, 420, 44, 251], [79, 769, 826, 148, 636], [469, 427, 719, 906, 355], [583, 774, 61, 353], [78, 721, 254, 30, 771], [22, 25, 77, 832], [764, 18], [25, 0, 1], []], ![[582, 767, 105, 673, 875, 509, 76, 413], [342, 539, 604, 532, 44, 723, 447, 702], [566, 571, 548, 685, 739, 324, 166, 702], [290, 487, 534, 761], [274, 651, 337, 469, 673, 648, 326, 657], [744, 153, 587, 737], [396, 690, 646, 529], [755, 349, 604, 767, 583, 240, 173, 3], [357, 764, 33, 481, 10, 521, 825, 401]], ![[43, 543, 430, 500, 2, 764, 251, 68], [717, 634, 87, 616, 272, 794, 639, 331], [188, 415, 487, 319, 34, 839, 582, 576], [586, 242, 513, 907], [835, 463, 661, 142, 324, 488, 193, 571], [232, 495, 434, 462], [311, 314, 874, 173], [784, 527, 748, 457, 727, 862, 273, 226], [262, 1, 581, 681, 645, 186, 179, 8]], ![[535, 463, 240, 595, 639, 529, 385, 688], [185, 618, 88, 9, 865, 884, 123, 212], [613, 526, 199, 236, 354, 766, 521, 475], [902, 85, 488, 420], [321, 691, 598, 843, 810, 428, 227, 135], [629, 876, 729, 535], [332, 859, 469, 434], [855, 56, 906, 715, 193, 609, 763, 431], [373, 638, 391, 239, 25, 343, 276, 902]], ![[886, 33, 364, 369, 364, 343, 662, 835], [835, 5, 215, 831, 769, 577, 236, 642], [381, 908, 300, 552, 307, 235, 152, 393], [827, 639, 874, 823], [697, 114, 482, 278, 255, 416, 572, 435], [362, 839, 153, 695], [594, 556, 659, 11], [195, 783, 387, 871, 590, 527, 423, 60], [542, 617, 810, 642, 334, 517, 638, 560]]]
 h' := ![![[65, 535, 524, 648, 721], [725, 877, 406, 473, 342], [93, 583, 128, 290, 108], [791, 102, 190, 266, 247], [425, 106, 338, 695, 285], [387, 85, 665, 449, 655], [217, 904, 157, 41, 707], [148, 183, 300, 375], [0, 0, 0, 1], [0, 1]], ![[35, 728, 446, 551, 2], [312, 263, 526, 857, 749], [153, 309, 456, 194, 225], [157, 155, 731, 850, 225], [414, 696, 658, 321, 791], [104, 790, 631, 692, 355], [359, 785, 676, 815, 196], [682, 771, 683, 54, 23], [340, 86, 278, 321, 489], [65, 535, 524, 648, 721]], ![[598, 820, 917, 761, 209], [367, 539, 378, 70, 318], [97, 608, 425, 276, 894], [145, 315, 55, 276, 581], [498, 749, 692, 583, 709], [67, 27, 460, 827, 151], [296, 94, 332, 641, 505], [73, 316, 24, 233, 700], [167, 240, 26, 900, 598], [35, 728, 446, 551, 2]], ![[221, 673, 870, 797, 906], [648, 842, 70, 410, 907], [776, 6, 531, 752, 510], [11, 295, 264, 553, 64], [615, 712, 226, 628, 855], [113, 18, 538, 648, 208], [840, 412, 848, 617, 685], [862, 368, 15, 431, 153], [269, 259, 82, 678, 548], [598, 820, 917, 761, 209]], ![[0, 1], [769, 236, 458, 28, 441], [581, 332, 298, 326, 101], [581, 52, 598, 812, 721], [99, 494, 843, 530, 117], [679, 918, 463, 141, 469], [173, 562, 744, 643, 664], [190, 200, 816, 745, 43], [143, 334, 533, 857, 203], [221, 673, 870, 797, 906]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [111, 476, 724, 723], [], [], []]
 b := ![[], [173, 886, 670, 673, 491], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A919 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 919 1 where
 D := ![[619, 250, 0, 894, 0, 1]]; D' := ![[619, 250, 0, 894, 0, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9]
 n := ![5]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P919P0

def C9190 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A919.D 0) 919 where
  n := 5
  w := ![![919, 0, 0, 0, 0], ![919, 0, 0, 4595, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K919 : KummerData 919 ![I919N0] ![655507336820599] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A919
  C := by
    intro i
    match i with
    | 0 => exact C9190
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 919 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp929 : Fact (Nat.Prime 929) := {out := by norm_num}

def I929N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![929, 0, 0, 0, 0], ![929, 0, 0, 4645, 0]] i)))

def P929P0 : CertificateIrreducibleZModOfList' 929 5 2 9 [629, 250, 0, 904, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [558, 909, 259, 382, 160], [11, 618, 678, 115, 403], [818, 95, 142, 82, 364], [471, 235, 779, 350, 2], [0, 1]]
 g := ![![[615, 55, 391, 903, 182], [400, 1, 53, 452], [745, 52, 124, 769], [829, 87, 745, 312], [549, 408, 164, 196], [908, 905, 489, 491, 880], [182, 346], [25, 0, 1], []], ![[98, 2, 861, 833, 445, 6, 429, 93], [590, 346, 227, 837], [694, 751, 839, 212], [802, 477, 582, 489], [689, 119, 176, 42], [669, 922, 747, 287, 134, 615, 489, 29], [582, 499, 12, 749], [727, 741, 796, 798, 897, 65, 77, 758], [860, 783, 433, 813, 341, 134, 709, 39]], ![[238, 606, 712, 822, 802, 15, 623, 400], [418, 364, 385, 440], [644, 81, 763, 908], [819, 67, 776, 576], [763, 641, 92, 9], [871, 425, 614, 412, 96, 800, 106, 543], [104, 61, 678, 320], [45, 686, 712, 326, 258, 192, 928, 128], [39, 183, 307, 800, 805, 268, 328, 919]], ![[790, 679, 546, 686, 293, 190, 751, 265], [238, 258, 587, 287], [658, 185, 335, 265], [732, 273, 816, 639], [675, 354, 14, 439], [606, 477, 160, 235, 863, 92, 225, 592], [518, 799, 729, 99], [117, 387, 400, 527, 772, 388, 243, 419], [770, 528, 93, 67, 235, 566, 51, 438]], ![[460, 854, 177, 106, 793, 614, 111, 261], [214, 618, 845, 29], [561, 167, 341, 591], [13, 469, 689, 337], [328, 656, 194, 258], [823, 517, 596, 227, 217, 910, 816, 225], [430, 748, 226, 453], [316, 716, 646, 657, 170, 702, 572, 529], [392, 482, 22, 891, 639, 419, 484, 8]]]
 h' := ![![[558, 909, 259, 382, 160], [850, 201, 541, 542, 773], [760, 48, 549, 348, 239], [205, 797, 319, 102, 456], [600, 428, 713, 379, 88], [203, 779, 248, 404, 14], [697, 737, 658, 183, 410], [68, 253, 300, 375], [0, 0, 0, 1], [0, 1]], ![[11, 618, 678, 115, 403], [322, 763, 441, 922, 209], [125, 189, 750, 196, 676], [665, 191, 553, 476, 400], [903, 18, 399, 640, 89], [21, 907, 533, 889, 741], [691, 494, 442, 206, 379], [878, 346, 437, 51, 328], [199, 741, 477, 260, 105], [558, 909, 259, 382, 160]], ![[818, 95, 142, 82, 364], [240, 126, 257, 489, 842], [70, 538, 699, 771, 37], [349, 540, 15, 313, 68], [149, 185, 482, 758, 905], [669, 351, 658, 604, 926], [796, 787, 373, 551, 112], [866, 928, 753, 726, 488], [25, 74, 507, 313, 920], [11, 618, 678, 115, 403]], ![[471, 235, 779, 350, 2], [785, 331, 848, 832, 620], [118, 827, 888, 625, 407], [586, 624, 296, 229, 806], [443, 767, 734, 156, 217], [809, 251, 903, 383, 131], [31, 924, 695, 896, 899], [467, 255, 66, 186, 429], [465, 138, 763, 802, 860], [818, 95, 142, 82, 364]], ![[0, 1], [322, 437, 700, 2, 343], [743, 256, 830, 847, 499], [39, 635, 675, 738, 128], [28, 460, 459, 854, 559], [349, 499, 445, 507, 46], [107, 774, 619, 22, 58], [55, 76, 302, 520, 613], [240, 905, 111, 482, 902], [471, 235, 779, 350, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [421, 376, 306, 209], [], [], []]
 b := ![[], [238, 785, 656, 597, 469], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A929 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 929 1 where
 D := ![[629, 250, 0, 904, 0, 1]]; D' := ![[629, 250, 0, 904, 0, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9]
 n := ![5]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P929P0

def C9290 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A929.D 0) 929 where
  n := 5
  w := ![![929, 0, 0, 0, 0], ![929, 0, 0, 4645, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K929 : KummerData 929 ![I929N0] ![691956144175649] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A929
  C := by
    intro i
    match i with
    | 0 => exact C9290
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 929 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp937 : Fact (Nat.Prime 937) := {out := by norm_num}

def I937N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![937, 0, 0, 0, 0], ![51, 1, 0, 0, 0]] i)))

def I937N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![937, 0, 0, 0, 0], ![876, 741, 707, 4430, 10]] i)))

def P937P0 : CertificateIrreducibleZModOfList' 937 1 2 9 [51, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [702], [], [571], [], [308], [727, 886, 1]]]
 h' := ![![[0, 1], [1], [936], [741], [791], [863], [117], [221], [403], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P937P1 : CertificateIrreducibleZModOfList' 937 4 2 9 [876, 741, 702, 886, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [354, 455, 622, 160], [171, 127, 383, 660], [463, 354, 869, 117], [0, 1]]
 g := ![![[866, 58, 286, 321], [343, 216, 619], [269, 791, 887], [443, 443, 81, 242], [613, 96, 783], [769, 356, 402, 455], [858, 197, 75], [338, 25, 51, 1], []], ![[123, 63, 222, 342, 390, 127], [686, 134, 89], [705, 286, 35], [891, 276, 356, 617, 866, 310], [68, 307, 815], [264, 863, 774, 116, 283, 909], [893, 764, 353], [70, 575, 268, 712, 530, 391], [523, 522, 673, 643, 686, 373]], ![[453, 603, 676, 30, 676, 584], [626, 834, 515], [821, 100, 228], [142, 728, 873, 674, 267, 114], [642, 616, 444], [256, 542, 326, 680, 145, 347], [348, 693, 107], [727, 903, 504, 509, 611, 506], [844, 135, 221, 202, 292, 38]], ![[270, 662, 129, 774, 619, 515], [339, 789, 34], [845, 734, 386], [421, 189, 310, 386, 717, 816], [40, 838, 649], [510, 570, 419, 797, 821, 253], [540, 50, 386], [553, 626, 120, 523, 409, 768], [467, 852, 691, 640, 866, 280]]]
 h' := ![![[354, 455, 622, 160], [627, 546, 791, 745], [492, 454, 406, 858], [787, 232, 936, 672], [583, 8, 449, 891], [59, 838, 105, 841], [819, 879, 693, 809], [4, 309, 300, 375], [0, 0, 0, 1], [0, 1]], ![[171, 127, 383, 660], [642, 717, 674, 496], [31, 779, 260, 433], [289, 554, 807, 413], [248, 576, 764, 914], [846, 209, 567, 114], [623, 631, 504, 298], [569, 299, 673, 148], [581, 790, 283, 380], [354, 455, 622, 160]], ![[463, 354, 869, 117], [719, 886, 390, 314], [551, 782, 862, 713], [297, 919, 451, 490], [61, 497, 718, 161], [656, 635, 269, 283], [492, 365, 189, 569], [114, 865, 680, 115], [328, 205, 650, 324], [171, 127, 383, 660]], ![[0, 1], [318, 662, 19, 319], [281, 796, 346, 807], [206, 169, 617, 299], [324, 793, 880, 845], [583, 192, 933, 636], [583, 936, 488, 198], [57, 401, 221, 299], [562, 879, 4, 232], [463, 354, 869, 117]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [61, 907, 688], []]
 b := ![[], [], [93, 577, 308, 175], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A937 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 937 2 where
 D := ![[51, 1], [876, 741, 702, 886, 1]]; D' := ![[51, 1], [876, 741, 702, 886, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P937P0
  | 1 => exact P937P1

def C9370 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A937.D 0) 937 where
  n := 1
  w := ![![937, 0, 0, 0, 0], ![51, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C9371 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A937.D 1) 937 where
  n := 4
  w := ![![937, 0, 0, 0, 0], ![876, 741, 707, 4430, 10]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K937 : KummerData 937 ![I937N0, I937N1] ![937, 770829564961] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A937
  C := by
    intro i
    match i with
    | 0 => exact C9370
    | 1 => exact C9371
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 937 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp941 : Fact (Nat.Prime 941) := {out := by norm_num}

def I941N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![941, 0, 0, 0, 0], ![941, 0, 0, 4705, 0]] i)))

def P941P0 : CertificateIrreducibleZModOfList' 941 5 2 9 [641, 250, 0, 916, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [644, 919, 448, 392, 161], [146, 121, 443, 658, 586], [166, 244, 302, 843, 802], [926, 597, 689, 930, 333], [0, 1]]
 g := ![![[366, 182, 182, 216, 80], [36, 874, 101, 815], [444, 654, 891, 293, 145], [837, 302, 917, 59, 132], [324, 857, 835, 352], [311, 19, 917, 406, 345], [101, 416], [25, 0, 1], []], ![[724, 904, 358, 698, 918, 468, 68, 415], [837, 496, 580, 80], [750, 504, 164, 123, 95, 492, 431, 683], [430, 672, 482, 139, 369, 909, 387, 469], [317, 374, 677, 49], [406, 841, 630, 565, 143, 604, 882, 440], [250, 373, 856, 501], [142, 647, 8, 868, 572, 117, 219, 569], [356, 154, 150, 166, 723, 873, 342, 887]], ![[514, 188, 147, 177, 295, 89, 332, 767], [356, 299, 191, 233], [525, 834, 176, 594, 902, 344, 30, 352], [557, 175, 826, 640, 576, 37, 253, 440], [662, 286, 240, 592], [901, 322, 295, 293, 392, 732, 451, 674], [295, 320, 864, 84], [787, 910, 497, 407, 280, 255, 766, 586], [606, 19, 601, 481, 359, 579, 239, 29]], ![[565, 491, 874, 686, 708, 100, 65, 763], [837, 587, 868, 369], [856, 358, 329, 853, 742, 66, 723, 838], [45, 831, 123, 91, 384, 427, 305, 284], [104, 532, 439, 596], [412, 122, 934, 581, 113, 254, 891, 778], [155, 101, 98, 686], [490, 520, 788, 174, 213, 843, 387, 69], [360, 929, 673, 151, 908, 247, 443, 936]], ![[872, 378, 179, 428, 650, 51, 124, 134], [532, 303, 827, 183], [243, 799, 843, 691, 95, 138, 317, 740], [665, 802, 832, 292, 11, 199, 853, 822], [131, 654, 798, 83], [315, 535, 9, 247, 249, 704, 490, 504], [152, 161, 706, 853], [442, 837, 323, 910, 624, 836, 604, 174], [246, 647, 664, 644, 320, 909, 212, 256]]]
 h' := ![![[644, 919, 448, 392, 161], [684, 134, 928, 575, 879], [519, 476, 196, 411, 782], [794, 378, 611, 89, 451], [397, 99, 184, 574, 814], [141, 427, 904, 4, 222], [31, 693, 297, 230, 275], [913, 337, 300, 375], [0, 0, 0, 1], [0, 1]], ![[146, 121, 443, 658, 586], [850, 864, 792, 522, 263], [872, 824, 899, 481, 879], [707, 458, 700, 663, 115], [358, 597, 879, 828, 130], [656, 415, 516, 250, 7], [661, 468, 841, 575, 530], [0, 506, 804, 24, 802], [775, 659, 658, 595, 888], [644, 919, 448, 392, 161]], ![[166, 244, 302, 843, 802], [310, 469, 182, 328, 584], [913, 357, 936, 216, 325], [571, 637, 735, 510, 186], [103, 557, 293, 280, 911], [897, 168, 291, 344, 66], [382, 597, 401, 569, 266], [71, 265, 844, 624, 435], [436, 861, 526, 745, 940], [146, 121, 443, 658, 586]], ![[926, 597, 689, 930, 333], [769, 257, 857, 628, 421], [485, 503, 333, 175, 680], [324, 15, 765, 207, 806], [797, 68, 786, 720, 121], [237, 429, 440, 654, 614], [198, 418, 890, 490, 473], [464, 476, 235, 218, 229], [821, 216, 668, 36, 57], [166, 244, 302, 843, 802]], ![[0, 1], [654, 158, 64, 770, 676], [909, 663, 459, 599, 157], [901, 394, 12, 413, 324], [364, 561, 681, 421, 847], [669, 443, 672, 630, 32], [616, 647, 394, 18, 338], [238, 298, 640, 641, 416], [791, 146, 30, 505, 938], [926, 597, 689, 930, 333]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [695, 600, 819, 479], [], [], []]
 b := ![[], [597, 766, 237, 301, 412], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A941 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 941 1 where
 D := ![[641, 250, 0, 916, 0, 1]]; D' := ![[641, 250, 0, 916, 0, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9]
 n := ![5]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P941P0

def C9410 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A941.D 0) 941 where
  n := 5
  w := ![![941, 0, 0, 0, 0], ![941, 0, 0, 4705, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K941 : KummerData 941 ![I941N0] ![737816081880701] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A941
  C := by
    intro i
    match i with
    | 0 => exact C9410
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 941 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp947 : Fact (Nat.Prime 947) := {out := by norm_num}

def I947N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![947, 0, 0, 0, 0], ![899, 227, 1, 0, 0]] i)))

def I947N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![947, 0, 0, 0, 0], ![243, 414, 720, 5, 0]] i)))

def P947P0 : CertificateIrreducibleZModOfList' 947 2 2 9 [899, 227, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [720, 946], [0, 1]]
 g := ![![[15, 550], [905, 717], [536], [936], [929, 429], [900, 36], [453], [798, 480], [720, 1]], ![[169, 397], [83, 230], [536], [936], [140, 518], [304, 911], [453], [743, 467], [493, 946]]]
 h' := ![![[720, 946], [825, 509], [11, 552], [679, 196], [83, 414], [585, 581], [756, 6], [424, 310], [468, 439], [0, 1]], ![[0, 1], [816, 438], [658, 395], [696, 751], [805, 533], [331, 366], [341, 941], [132, 637], [250, 508], [720, 946]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [614]]
 b := ![[], [279, 307]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P947P1 : CertificateIrreducibleZModOfList' 947 3 2 9 [243, 414, 720, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [678, 238, 520], [496, 708, 427], [0, 1]]
 g := ![![[687, 444, 619], [541, 930, 356], [696, 718], [711, 479], [153, 700, 532], [140, 623, 165], [687, 145], [122, 236, 391], [1]], ![[802, 527, 750, 454], [752, 619, 276, 854], [835, 942], [897, 743], [521, 563, 679, 39], [702, 290, 546, 762], [414, 797], [708, 366, 691, 548], [481, 91, 101, 281]], ![[133, 63, 690, 717], [772, 855, 907, 369], [99, 481], [490, 352], [505, 549, 911, 65], [442, 916, 924, 419], [477, 315], [75, 466, 657, 792], [755, 131, 278, 666]]]
 h' := ![![[678, 238, 520], [170, 771, 293], [134, 9, 718], [436, 347, 80], [701, 916, 612], [72, 365, 370], [863, 696, 877], [658, 437, 195], [704, 533, 227], [0, 1]], ![[496, 708, 427], [805, 941, 390], [777, 711, 697], [32, 333, 330], [256, 102, 496], [635, 375, 41], [200, 751, 797], [798, 641, 705], [74, 626, 362], [678, 238, 520]], ![[0, 1], [108, 182, 264], [278, 227, 479], [140, 267, 537], [348, 876, 786], [222, 207, 536], [708, 447, 220], [297, 816, 47], [398, 735, 358], [496, 708, 427]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [713, 192], []]
 b := ![[], [630, 650, 393], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A947 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 947 2 where
 D := ![[899, 227, 1], [243, 414, 720, 1]]; D' := ![[899, 227, 1], [243, 414, 720, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P947P0
  | 1 => exact P947P1

def C9470 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A947.D 0) 947 where
  n := 2
  w := ![![947, 0, 0, 0, 0], ![899, 227, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C9471 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A947.D 1) 947 where
  n := 3
  w := ![![947, 0, 0, 0, 0], ![243, 414, 720, 5, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K947 : KummerData 947 ![I947N0, I947N1] ![896809, 849278123] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A947
  C := by
    intro i
    match i with
    | 0 => exact C9470
    | 1 => exact C9471
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 947 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp953 : Fact (Nat.Prime 953) := {out := by norm_num}

def I953N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![953, 0, 0, 0, 0], ![662, 1, 0, 0, 0]] i)))

def I953N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![953, 0, 0, 0, 0], ![678, 1, 0, 0, 0]] i)))

def I953N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![953, 0, 0, 0, 0], ![810, 1, 0, 0, 0]] i)))

def I953N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![953, 0, 0, 0, 0], ![519, 709, 1, 0, 0]] i)))

def P953P0 : CertificateIrreducibleZModOfList' 953 1 2 9 [662, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [231], [110], [604], [], [464], [817, 291, 1]]]
 h' := ![![[0, 1], [1], [952], [511], [561], [412], [669], [651], [450], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P953P1 : CertificateIrreducibleZModOfList' 953 1 2 9 [678, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [860], [780], [151], [], [818], [338, 275, 1]]]
 h' := ![![[0, 1], [952], [511], [156], [75], [546], [811], [42], [509], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P953P2 : CertificateIrreducibleZModOfList' 953 1 2 9 [810, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [261], [874], [819], [], [399], [436, 143, 1]]]
 h' := ![![[0, 1], [952], [511], [156], [139], [851], [834], [830], [403], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P953P3 : CertificateIrreducibleZModOfList' 953 2 2 9 [519, 709, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [244, 952], [0, 1]]
 g := ![![[510, 917], [945], [924], [79, 228], [797, 210], [505, 662], [639], [584, 949], [244, 1]], ![[303, 36], [945], [924], [437, 725], [575, 743], [23, 291], [639], [561, 4], [488, 952]]]
 h' := ![![[244, 952], [751, 746], [287, 360], [931, 784], [912, 108], [933, 46], [814, 137], [911, 96], [113, 884], [0, 1]], ![[0, 1], [752, 207], [451, 593], [674, 169], [580, 845], [721, 907], [887, 816], [510, 857], [431, 69], [244, 952]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [776]]
 b := ![[], [314, 388]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A953 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 953 4 where
 D := ![[662, 1], [678, 1], [810, 1], [519, 709, 1]]; D' := ![[662, 1], [678, 1], [810, 1], [519, 709, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9, 9, 9]
 n := ![1, 1, 1, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P953P0
  | 1 => exact P953P1
  | 2 => exact P953P2
  | 3 => exact P953P3

def C9530 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A953.D 0) 953 where
  n := 1
  w := ![![953, 0, 0, 0, 0], ![662, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C9531 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A953.D 1) 953 where
  n := 1
  w := ![![953, 0, 0, 0, 0], ![678, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C9532 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A953.D 2) 953 where
  n := 1
  w := ![![953, 0, 0, 0, 0], ![810, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C9533 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A953.D 3) 953 where
  n := 2
  w := ![![953, 0, 0, 0, 0], ![519, 709, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K953 : KummerData 953 ![I953N0, I953N1, I953N2, I953N3] ![953, 953, 953, 908209] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A953
  C := by
    intro i
    match i with
    | 0 => exact C9530
    | 1 => exact C9531
    | 2 => exact C9532
    | 3 => exact C9533
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 953 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


lemma PB1045I17_primes (p : ℕ) :
  p ∈ Set.range ![887, 907, 911, 919, 929, 937, 941, 947, 953] ↔ Nat.Prime p ∧ 883 < p ∧ p ≤ 953 := by
  rw [← List.mem_ofFn']
  convert primes_range 883 953 (by omega)
  decide

def PB1045I17 : PrimesBelowBoundCertificateInterval O 883 953 1045 where
  m := 9
  g := ![2, 4, 3, 1, 1, 2, 1, 2, 4]
  P := ![887, 907, 911, 919, 929, 937, 941, 947, 953]
  hP := PB1045I17_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I887N0, I887N1]
    · exact ![I907N0, I907N1, I907N2, I907N3]
    · exact ![I911N0, I911N1, I911N2]
    · exact ![I919N0]
    · exact ![I929N0]
    · exact ![I937N0, I937N1]
    · exact ![I941N0]
    · exact ![I947N0, I947N1]
    · exact ![I953N0, I953N1, I953N2, I953N3]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · convert (containsPrimesAbove_of_KummerData K887) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K907) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K911) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K919) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K929) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K937) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K941) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K947) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K953) <;> rfl
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![887, 619005459361]
    · exact ![907, 907, 907, 822649]
    · exact ![911, 829921, 829921]
    · exact ![655507336820599]
    · exact ![691956144175649]
    · exact ![937, 770829564961]
    · exact ![737816081880701]
    · exact ![896809, 849278123]
    · exact ![953, 953, 953, 908209]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact (card_quot_of_KummerData K887)
    · exact (card_quot_of_KummerData K907)
    · exact (card_quot_of_KummerData K911)
    · exact (card_quot_of_KummerData K919)
    · exact (card_quot_of_KummerData K929)
    · exact (card_quot_of_KummerData K937)
    · exact (card_quot_of_KummerData K941)
    · exact (card_quot_of_KummerData K947)
    · exact (card_quot_of_KummerData K953)
  β := ![I887N0, I907N0, I907N1, I907N2, I911N0, I937N0, I953N0, I953N1, I953N2]
  Il := ![[I887N0], [I907N0, I907N1, I907N2], [I911N0], [], [], [I937N0], [], [], [I953N0, I953N1, I953N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
