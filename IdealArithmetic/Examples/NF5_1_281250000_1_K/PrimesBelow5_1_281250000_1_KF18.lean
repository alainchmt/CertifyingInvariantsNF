
import IdealArithmetic.Examples.NF5_1_281250000_1_K.RI5_1_281250000_1_K
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 

instance hp967 : Fact (Nat.Prime 967) := {out := by norm_num}

def I967N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![967, 0, 0, 0, 0], ![17, 1, 0, 0, 0]] i)))

def I967N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![967, 0, 0, 0, 0], ![153, 347, 269, 4750, 10]] i)))

def P967P0 : CertificateIrreducibleZModOfList' 967 1 2 9 [17, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [512], [724], [], [], [], [714], [282], [289, 950, 1]]]
 h' := ![![[0, 1], [966], [263], [336], [277], [858], [433], [41], [889], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P967P1 : CertificateIrreducibleZModOfList' 967 4 2 9 [153, 347, 264, 950, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [490, 363, 499, 272], [160, 548, 547, 780], [334, 55, 888, 882], [0, 1]]
 g := ![![[60, 129, 532, 25], [634, 960, 736, 450], [530, 136, 398, 602], [661, 691, 292], [558, 634, 123], [82, 261, 888], [413, 713, 857, 410], [425, 25, 17, 1], []], ![[676, 303, 788, 684, 411, 8], [145, 305, 635, 649, 583, 494], [858, 348, 41, 357, 853, 470], [107, 277, 153], [68, 323, 301], [31, 227, 904], [798, 808, 16, 15, 935, 452], [187, 495, 258, 727, 490, 168], [350, 195, 745, 752, 294, 378]], ![[560, 872, 441, 887, 657, 192], [83, 799, 631, 803, 550, 592], [302, 275, 207, 568, 940, 951], [244, 897, 397], [613, 315, 321], [936, 650, 31], [512, 355, 59, 67, 243, 896], [825, 9, 53, 428, 227, 96], [81, 594, 576, 629, 284, 618]], ![[935, 755, 84, 199, 262, 375], [317, 14, 183, 571, 115, 659], [556, 578, 528, 332, 942, 873], [194, 735, 225], [203, 454, 431], [356, 441, 482], [88, 841, 149, 304, 43, 359], [305, 853, 863, 564, 469, 199], [219, 874, 745, 51, 806, 887]]]
 h' := ![![[490, 363, 499, 272], [665, 286, 881, 5], [138, 210, 216, 660], [689, 691, 463, 405], [883, 367, 168, 560], [376, 648, 759, 136], [633, 564, 454, 317], [731, 519, 300, 375], [0, 0, 0, 1], [0, 1]], ![[160, 548, 547, 780], [321, 516, 175, 16], [743, 847, 899, 277], [198, 804, 226, 448], [179, 851, 311, 842], [93, 54, 418, 760], [1, 530, 918, 638], [281, 235, 477, 618], [514, 370, 906, 141], [490, 363, 499, 272]], ![[334, 55, 888, 882], [821, 273, 842, 525], [286, 74, 111, 943], [687, 326, 582, 279], [302, 789, 591, 517], [407, 824, 609, 777], [362, 718, 811, 511], [715, 378, 171, 408], [933, 578, 863, 54], [160, 548, 547, 780]], ![[0, 1], [550, 859, 36, 421], [877, 803, 708, 54], [585, 113, 663, 802], [331, 894, 864, 15], [406, 408, 148, 261], [836, 122, 718, 468], [448, 802, 19, 533], [565, 19, 165, 771], [334, 55, 888, 882]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [812, 412, 89], []]
 b := ![[], [], [946, 570, 132, 802], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A967 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 967 2 where
 D := ![[17, 1], [153, 347, 264, 950, 1]]; D' := ![[17, 1], [153, 347, 264, 950, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P967P0
  | 1 => exact P967P1

def C9670 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A967.D 0) 967 where
  n := 1
  w := ![![967, 0, 0, 0, 0], ![17, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C9671 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A967.D 1) 967 where
  n := 4
  w := ![![967, 0, 0, 0, 0], ![153, 347, 269, 4750, 10]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K967 : KummerData 967 ![I967N0, I967N1] ![967, 874391437921] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A967
  C := by
    intro i
    match i with
    | 0 => exact C9670
    | 1 => exact C9671
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 967 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp971 : Fact (Nat.Prime 971) := {out := by norm_num}

def I971N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![971, 0, 0, 0, 0], ![971, 0, 0, 4855, 0]] i)))

def P971P0 : CertificateIrreducibleZModOfList' 971 5 2 9 [671, 250, 0, 946, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [477, 115, 400, 300, 629], [178, 41, 308, 694, 867], [956, 350, 577, 893, 953], [331, 464, 657, 55, 464], [0, 1]]
 g := ![![[691, 526, 871, 779, 409], [215, 603, 369, 730, 898], [314, 69, 128, 789], [294, 23, 708, 835, 567], [340, 157, 917, 747], [311, 577, 762, 16], [790, 699, 801], [25, 0, 1], []], ![[534, 442, 338, 255, 66, 442, 339, 843], [121, 940, 106, 911, 541, 46, 671, 459], [163, 490, 394, 412], [620, 693, 279, 922, 120, 123, 806, 766], [97, 124, 940, 663], [320, 471, 322, 88], [193, 254, 876, 601, 391, 576, 952, 957], [576, 759, 625, 345, 50, 386, 137, 281], [519, 189, 6, 908, 262, 289, 519, 599]], ![[792, 969, 580, 222, 399, 230, 808, 507], [739, 229, 421, 886, 416, 64, 142, 17], [884, 950, 63, 108], [327, 536, 261, 106, 766, 345, 23, 388], [246, 789, 40, 249], [600, 608, 158, 393], [164, 526, 11, 52, 627, 843, 593, 108], [764, 466, 689, 81, 777, 646, 99, 382], [637, 881, 321, 872, 174, 540, 451, 525]], ![[775, 729, 503, 912, 67, 117, 256, 733], [353, 813, 94, 554, 426, 190, 78, 612], [184, 513, 2, 826], [739, 761, 627, 108, 399, 255, 806, 156], [101, 217, 826, 80], [227, 109, 419, 740], [545, 236, 613, 618, 45, 368, 736, 364], [84, 430, 736, 664, 831, 517, 238, 103], [437, 843, 65, 107, 431, 89, 893, 965]], ![[837, 809, 61, 232, 55, 366, 568, 335], [1, 172, 866, 694, 859, 68, 75, 504], [854, 224, 239, 63], [897, 41, 161, 970, 301, 884, 511, 203], [853, 529, 520, 780], [559, 14, 565, 283], [395, 7, 78, 468, 185, 320, 29, 903], [34, 576, 401, 948, 427, 829, 341, 8], [44, 605, 420, 598, 349, 836, 776, 864]]]
 h' := ![![[477, 115, 400, 300, 629], [414, 416, 904, 647, 288], [688, 607, 137, 561, 82], [810, 865, 459, 715, 728], [230, 356, 59, 278, 852], [34, 277, 202, 194, 135], [76, 518, 543, 633, 967], [703, 547, 300, 375], [0, 0, 0, 1], [0, 1]], ![[178, 41, 308, 694, 867], [834, 645, 181, 789, 230], [578, 391, 916, 318, 511], [708, 480, 801, 459, 817], [253, 172, 647, 864, 598], [625, 431, 532, 356, 465], [524, 67, 362, 276, 567], [53, 369, 27, 232, 456], [90, 669, 653, 536, 256], [477, 115, 400, 300, 629]], ![[956, 350, 577, 893, 953], [448, 399, 212, 658, 115], [407, 221, 835, 907, 317], [100, 890, 608, 580, 324], [138, 46, 617, 463, 315], [842, 709, 129, 963, 483], [96, 811, 842, 755, 130], [675, 604, 381, 597, 800], [968, 691, 183, 859, 682], [178, 41, 308, 694, 867]], ![[331, 464, 657, 55, 464], [131, 189, 565, 955, 109], [122, 147, 32, 453, 192], [562, 235, 518, 497, 760], [574, 556, 346, 927, 477], [474, 653, 5, 651, 554], [866, 821, 784, 461, 903], [296, 697, 227, 712, 81], [524, 239, 8, 515, 454], [956, 350, 577, 893, 953]], ![[0, 1], [923, 293, 80, 835, 229], [836, 576, 22, 674, 840], [968, 443, 527, 662, 284], [343, 812, 273, 381, 671], [292, 843, 103, 749, 305], [693, 696, 382, 788, 346], [281, 696, 36, 26, 605], [360, 343, 127, 31, 550], [331, 464, 657, 55, 464]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [361, 470, 843, 55], [], [], []]
 b := ![[], [510, 184, 657, 201, 3], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A971 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 971 1 where
 D := ![[671, 250, 0, 946, 0, 1]]; D' := ![[671, 250, 0, 946, 0, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9]
 n := ![5]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P971P0

def C9710 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A971.D 0) 971 where
  n := 5
  w := ![![971, 0, 0, 0, 0], ![971, 0, 0, 4855, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K971 : KummerData 971 ![I971N0] ![863169625893851] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A971
  C := by
    intro i
    match i with
    | 0 => exact C9710
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 971 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp977 : Fact (Nat.Prime 977) := {out := by norm_num}

def I977N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![977, 0, 0, 0, 0], ![240, 1, 0, 0, 0]] i)))

def I977N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![977, 0, 0, 0, 0], ![243, 688, 914, 3685, 10]] i)))

def P977P0 : CertificateIrreducibleZModOfList' 977 1 2 9 [240, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [], [678], [], [702], [607], [934, 737, 1]]]
 h' := ![![[0, 1], [1], [976], [252], [439], [558], [541], [870], [550], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P977P1 : CertificateIrreducibleZModOfList' 977 4 2 9 [243, 688, 909, 737, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [427, 671, 674, 818], [624, 670, 662, 78], [166, 612, 618, 81], [0, 1]]
 g := ![![[537, 134, 583, 464], [6, 959, 894], [877, 719, 202], [801, 674, 790], [968, 911, 104, 262], [748, 679, 198], [22, 874, 802, 914], [138, 25, 240, 1], []], ![[487, 304, 101, 904, 678, 739], [196, 873, 542], [271, 426, 930], [335, 11, 573], [923, 841, 398, 90, 105, 116], [615, 805, 567], [976, 753, 861, 247, 241, 230], [793, 293, 586, 487, 152, 508], [822, 637, 374, 920, 623, 676]], ![[388, 616, 535, 953, 799, 196], [436, 750, 275], [350, 718, 313], [128, 574, 273], [934, 714, 483, 260, 341, 862], [719, 43, 313], [413, 523, 968, 736, 230, 896], [757, 284, 182, 506, 503, 77], [821, 125, 791, 160, 924, 707]], ![[666, 483, 302, 815, 620, 930], [240, 191, 433], [710, 501, 752], [446, 578, 255], [595, 936, 150, 278, 276, 343], [126, 588, 185], [372, 759, 19, 78, 888, 319], [421, 940, 31, 936, 425, 638], [240, 311, 494, 780, 888, 930]]]
 h' := ![![[427, 671, 674, 818], [374, 428, 580, 377], [53, 481, 406, 359], [334, 92, 309, 661], [233, 834, 966, 61], [470, 660, 570, 466], [516, 325, 565, 160], [661, 589, 300, 375], [0, 0, 0, 1], [0, 1]], ![[624, 670, 662, 78], [681, 407, 135, 492], [650, 401, 679, 284], [900, 557, 193, 248], [640, 465, 970, 401], [97, 290, 20, 557], [914, 259, 105, 170], [874, 561, 318, 140], [823, 363, 317, 203], [427, 671, 674, 818]], ![[166, 612, 618, 81], [862, 392, 494, 27], [65, 105, 657, 392], [677, 3, 852, 196], [813, 179, 163, 562], [170, 166, 855, 856], [2, 533, 778, 196], [226, 170, 625, 466], [299, 140, 374, 902], [624, 670, 662, 78]], ![[0, 1], [670, 727, 745, 81], [134, 967, 212, 919], [309, 325, 600, 849], [697, 476, 832, 930], [218, 838, 509, 75], [189, 837, 506, 451], [42, 634, 711, 973], [282, 474, 286, 848], [166, 612, 618, 81]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [311, 702, 795], []]
 b := ![[], [], [787, 721, 455, 328], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A977 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 977 2 where
 D := ![[240, 1], [243, 688, 909, 737, 1]]; D' := ![[240, 1], [243, 688, 909, 737, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P977P0
  | 1 => exact P977P1

def C9770 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A977.D 0) 977 where
  n := 1
  w := ![![977, 0, 0, 0, 0], ![240, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C9771 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A977.D 1) 977 where
  n := 4
  w := ![![977, 0, 0, 0, 0], ![243, 688, 914, 3685, 10]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K977 : KummerData 977 ![I977N0, I977N1] ![977, 911125611841] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A977
  C := by
    intro i
    match i with
    | 0 => exact C9770
    | 1 => exact C9771
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 977 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp983 : Fact (Nat.Prime 983) := {out := by norm_num}

def I983N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![983, 0, 0, 0, 0], ![394, 481, 1, 0, 0]] i)))

def I983N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![983, 0, 0, 0, 0], ![608, 920, 502, 5, 0]] i)))

def P983P0 : CertificateIrreducibleZModOfList' 983 2 2 9 [394, 481, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [502, 982], [0, 1]]
 g := ![![[847, 753], [313, 145], [150, 43], [706], [311, 830], [712], [588, 376], [269, 461], [502, 1]], ![[398, 230], [361, 838], [110, 940], [706], [179, 153], [712], [604, 607], [686, 522], [21, 982]]]
 h' := ![![[502, 982], [536, 368], [863, 388], [312, 224], [341, 824], [200, 441], [316, 793], [178, 344], [778, 945], [0, 1]], ![[0, 1], [468, 615], [22, 595], [698, 759], [146, 159], [407, 542], [287, 190], [841, 639], [379, 38], [502, 982]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [477]]
 b := ![[], [591, 730]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P983P1 : CertificateIrreducibleZModOfList' 983 3 2 9 [608, 920, 502, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [506, 107, 560], [958, 875, 423], [0, 1]]
 g := ![![[966, 210, 574], [923, 275, 1], [808, 657, 943], [374, 510], [333, 188, 801], [188, 448], [623, 804, 472], [395, 837, 356], [1]], ![[256, 497, 969, 102], [109, 97, 512, 388], [166, 371, 923, 732], [537, 888], [534, 293, 117, 646], [832, 112], [197, 570, 671, 683], [317, 896, 560, 341], [913, 162, 916, 101]], ![[120, 900, 885, 733], [255, 933, 389, 892], [608, 31, 982, 415], [920, 79], [535, 96, 52, 882], [812, 25], [14, 789, 932, 129], [864, 360, 807, 266], [858, 382, 981, 882]]]
 h' := ![![[506, 107, 560], [109, 710, 102], [236, 103, 982], [837, 977, 226], [34, 744, 570], [818, 554, 230], [654, 144, 331], [675, 664, 786], [375, 63, 481], [0, 1]], ![[958, 875, 423], [379, 312, 265], [228, 757, 774], [954, 125, 739], [654, 632, 217], [316, 835, 330], [866, 799, 657], [69, 295, 899], [22, 218, 43], [506, 107, 560]], ![[0, 1], [262, 944, 616], [155, 123, 210], [602, 864, 18], [932, 590, 196], [199, 577, 423], [209, 40, 978], [604, 24, 281], [412, 702, 459], [958, 875, 423]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [253, 769], []]
 b := ![[], [374, 593, 39], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A983 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 983 2 where
 D := ![[394, 481, 1], [608, 920, 502, 1]]; D' := ![[394, 481, 1], [608, 920, 502, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P983P0
  | 1 => exact P983P1

def C9830 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A983.D 0) 983 where
  n := 2
  w := ![![983, 0, 0, 0, 0], ![394, 481, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C9831 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A983.D 1) 983 where
  n := 3
  w := ![![983, 0, 0, 0, 0], ![608, 920, 502, 5, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K983 : KummerData 983 ![I983N0, I983N1] ![966289, 949862087] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A983
  C := by
    intro i
    match i with
    | 0 => exact C9830
    | 1 => exact C9831
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 983 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp991 : Fact (Nat.Prime 991) := {out := by norm_num}

def I991N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![991, 0, 0, 0, 0], ![208, 1, 0, 0, 0]] i)))

def I991N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![991, 0, 0, 0, 0], ![803, 1, 0, 0, 0]] i)))

def I991N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![991, 0, 0, 0, 0], ![66, 830, 971, 5, 0]] i)))

def P991P0 : CertificateIrreducibleZModOfList' 991 1 2 9 [208, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [81], [729], [786], [42], [], [623], [51], [651, 783, 1]]]
 h' := ![![[0, 1], [990], [982], [27], [183], [673], [237], [293], [359], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P991P1 : CertificateIrreducibleZModOfList' 991 1 2 9 [803, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [311], [695], [430], [261], [], [199], [289], [659, 188, 1]]]
 h' := ![![[0, 1], [990], [839], [569], [509], [65], [745], [818], [17], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P991P2 : CertificateIrreducibleZModOfList' 991 3 2 9 [66, 830, 971, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [322, 661, 620], [689, 329, 371], [0, 1]]
 g := ![![[866, 266, 639], [79, 437, 816], [474, 76, 590], [703, 966, 954], [615, 32, 917], [175, 290], [975, 812, 528], [892, 566, 400], [1]], ![[698, 277, 749, 353], [113, 980, 290, 771], [726, 461, 671, 428], [411, 623, 295, 76], [348, 871, 775, 101], [399, 841], [907, 316, 289, 937], [801, 400, 877, 722], [663, 372, 524, 428]], ![[355, 47, 301, 153], [404, 977, 775, 136], [794, 364, 956, 410], [169, 763, 649, 592], [414, 581, 91, 181], [444, 517], [507, 876, 175, 262], [653, 503, 604, 854], [118, 492, 791, 563]]]
 h' := ![![[322, 661, 620], [732, 573, 776], [428, 275, 445], [179, 567, 514], [41, 688, 285], [603, 870, 780], [65, 204, 489], [588, 611, 863], [925, 161, 20], [0, 1]], ![[689, 329, 371], [116, 798, 108], [675, 825, 776], [35, 895, 371], [72, 892, 50], [297, 139, 247], [157, 61, 962], [191, 15, 759], [295, 558, 363], [322, 661, 620]], ![[0, 1], [282, 611, 107], [932, 882, 761], [245, 520, 106], [529, 402, 656], [743, 973, 955], [351, 726, 531], [69, 365, 360], [386, 272, 608], [689, 329, 371]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24, 26], []]
 b := ![[], [626, 921, 553], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A991 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 991 3 where
 D := ![[208, 1], [803, 1], [66, 830, 971, 1]]; D' := ![[208, 1], [803, 1], [66, 830, 971, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9, 9]
 n := ![1, 1, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P991P0
  | 1 => exact P991P1
  | 2 => exact P991P2

def C9910 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A991.D 0) 991 where
  n := 1
  w := ![![991, 0, 0, 0, 0], ![208, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C9911 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A991.D 1) 991 where
  n := 1
  w := ![![991, 0, 0, 0, 0], ![803, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C9912 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A991.D 2) 991 where
  n := 3
  w := ![![991, 0, 0, 0, 0], ![66, 830, 971, 5, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K991 : KummerData 991 ![I991N0, I991N1, I991N2] ![991, 991, 973242271] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A991
  C := by
    intro i
    match i with
    | 0 => exact C9910
    | 1 => exact C9911
    | 2 => exact C9912
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 991 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp997 : Fact (Nat.Prime 997) := {out := by norm_num}

def I997N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![997, 0, 0, 0, 0], ![331, 806, 1, 0, 0]] i)))

def I997N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![997, 0, 0, 0, 0], ![225, 233, 191, 5, 0]] i)))

def P997P0 : CertificateIrreducibleZModOfList' 997 2 2 9 [331, 806, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [191, 996], [0, 1]]
 g := ![![[891, 747], [300], [96, 593], [729], [672], [728, 529], [624, 713], [781, 762], [191, 1]], ![[0, 250], [300], [698, 404], [729], [672], [73, 468], [218, 284], [761, 235], [382, 996]]]
 h' := ![![[191, 996], [832, 194], [128, 439], [563, 568], [814, 970], [306, 147], [832, 23], [709, 244], [587, 258], [0, 1]], ![[0, 1], [0, 803], [229, 558], [378, 429], [642, 27], [467, 850], [240, 974], [454, 753], [15, 739], [191, 996]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [723]]
 b := ![[], [621, 860]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P997P1 : CertificateIrreducibleZModOfList' 997 3 2 9 [225, 233, 191, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [127, 678, 651], [679, 318, 346], [0, 1]]
 g := ![![[735, 190, 922], [306, 222], [22, 648, 219], [690, 502], [274, 88], [19, 74, 363], [692, 475, 314], [674, 435, 589], [1]], ![[982, 460, 792, 497], [52, 101], [284, 74, 302, 652], [340, 102], [574, 409], [660, 235, 483, 260], [928, 142, 285, 374], [952, 329, 918, 650], [362, 355, 696, 623]], ![[178, 514, 350, 104], [581, 507], [829, 913, 133, 656], [996, 382], [941, 477], [850, 986, 76, 599], [40, 359, 337, 148], [28, 57, 851, 935], [975, 447, 73, 374]]]
 h' := ![![[127, 678, 651], [171, 303, 54], [35, 127, 333], [947, 963, 387], [779, 383, 730], [710, 168, 852], [829, 351, 782], [891, 93, 459], [772, 764, 806], [0, 1]], ![[679, 318, 346], [777, 422, 70], [446, 984, 138], [862, 869, 235], [568, 397, 919], [64, 988, 447], [848, 142, 611], [333, 397, 126], [849, 385, 937], [127, 678, 651]], ![[0, 1], [178, 272, 873], [374, 883, 526], [292, 162, 375], [678, 217, 345], [286, 838, 695], [45, 504, 601], [263, 507, 412], [768, 845, 251], [679, 318, 346]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [260, 160], []]
 b := ![[], [976, 898, 571], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A997 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 997 2 where
 D := ![[331, 806, 1], [225, 233, 191, 1]]; D' := ![[331, 806, 1], [225, 233, 191, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P997P0
  | 1 => exact P997P1

def C9970 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A997.D 0) 997 where
  n := 2
  w := ![![997, 0, 0, 0, 0], ![331, 806, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C9971 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A997.D 1) 997 where
  n := 3
  w := ![![997, 0, 0, 0, 0], ![225, 233, 191, 5, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K997 : KummerData 997 ![I997N0, I997N1] ![994009, 991026973] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A997
  C := by
    intro i
    match i with
    | 0 => exact C9970
    | 1 => exact C9971
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 997 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp1009 : Fact (Nat.Prime 1009) := {out := by norm_num}

def I1009N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1009, 0, 0, 0, 0], ![194, 1, 0, 0, 0]] i)))

def I1009N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1009, 0, 0, 0, 0], ![408, 1, 0, 0, 0]] i)))

def I1009N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1009, 0, 0, 0, 0], ![672, 707, 407, 5, 0]] i)))

def P1009P0 : CertificateIrreducibleZModOfList' 1009 1 2 9 [194, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [], [259], [766], [709], [1006], [303, 815, 1]]]
 h' := ![![[0, 1], [1008], [469], [247], [204], [728], [687], [582], [749], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P1009P1 : CertificateIrreducibleZModOfList' 1009 1 2 9 [408, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [], [270], [222], [675], [829], [988, 601, 1]]]
 h' := ![![[0, 1], [1008], [469], [762], [830], [234], [57], [792], [496], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P1009P2 : CertificateIrreducibleZModOfList' 1009 3 2 9 [672, 707, 407, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [732, 180, 674], [879, 828, 335], [0, 1]]
 g := ![![[89, 849, 343], [409, 583], [370, 913], [91, 627], [460, 404, 123], [239, 605, 719], [866, 812, 147], [526, 587, 173], [1]], ![[576, 8, 458, 845], [921, 964], [7, 512], [714, 696], [433, 41, 337, 391], [126, 523, 219, 627], [12, 13, 623, 835], [196, 712, 258, 1005], [75, 607, 70, 974]], ![[854, 997, 526, 889], [224, 467], [372, 382], [730, 369], [652, 806, 118, 937], [630, 50, 480, 42], [2, 15, 946, 681], [302, 160, 459, 443], [716, 976, 261, 35]]]
 h' := ![![[732, 180, 674], [408, 722, 694], [703, 431, 51], [156, 591, 517], [643, 670, 567], [832, 165, 688], [241, 163, 460], [687, 46, 34], [337, 302, 602], [0, 1]], ![[879, 828, 335], [171, 156, 801], [334, 31, 761], [925, 589, 39], [754, 290, 848], [987, 601, 808], [19, 903, 368], [360, 304, 634], [702, 268, 749], [732, 180, 674]], ![[0, 1], [842, 131, 523], [488, 547, 197], [128, 838, 453], [907, 49, 603], [931, 243, 522], [950, 952, 181], [638, 659, 341], [743, 439, 667], [879, 828, 335]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77, 709], []]
 b := ![[], [358, 771, 225], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A1009 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 1009 3 where
 D := ![[194, 1], [408, 1], [672, 707, 407, 1]]; D' := ![[194, 1], [408, 1], [672, 707, 407, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9, 9]
 n := ![1, 1, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P1009P0
  | 1 => exact P1009P1
  | 2 => exact P1009P2

def C10090 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A1009.D 0) 1009 where
  n := 1
  w := ![![1009, 0, 0, 0, 0], ![194, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C10091 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A1009.D 1) 1009 where
  n := 1
  w := ![![1009, 0, 0, 0, 0], ![408, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C10092 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A1009.D 2) 1009 where
  n := 3
  w := ![![1009, 0, 0, 0, 0], ![672, 707, 407, 5, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K1009 : KummerData 1009 ![I1009N0, I1009N1, I1009N2] ![1009, 1009, 1027243729] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A1009
  C := by
    intro i
    match i with
    | 0 => exact C10090
    | 1 => exact C10091
    | 2 => exact C10092
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 1009 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp1013 : Fact (Nat.Prime 1013) := {out := by norm_num}

def I1013N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1013, 0, 0, 0, 0], ![110, 1, 0, 0, 0]] i)))

def I1013N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1013, 0, 0, 0, 0], ![734, 806, 937, 4515, 10]] i)))

def P1013P0 : CertificateIrreducibleZModOfList' 1013 1 2 9 [110, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [617], [], [483], [340], [214], [646], [957, 903, 1]]]
 h' := ![![[0, 1], [1], [1], [477], [559], [81], [772], [863], [82], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P1013P1 : CertificateIrreducibleZModOfList' 1013 4 2 9 [734, 806, 932, 903, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [273, 152, 821, 363], [861, 699, 651, 881], [1002, 161, 554, 782], [0, 1]]
 g := ![![[404, 533, 807, 169], [948, 946, 140], [1009, 333, 88, 902], [963, 151, 387], [875, 862, 185, 809], [46, 379, 310, 135], [738, 393, 354, 831], [724, 25, 110, 1], []], ![[656, 682, 886, 413, 620, 489], [415, 50, 44], [401, 180, 984, 197, 267, 906], [361, 11, 312], [675, 844, 220, 542, 74, 986], [958, 870, 715, 321, 115, 517], [813, 80, 700, 718, 377, 236], [485, 842, 925, 191, 325, 147], [205, 326, 343, 802, 69, 313]], ![[879, 119, 575, 658, 536, 888], [414, 1008, 387], [882, 849, 957, 636, 729, 786], [978, 99, 957], [653, 659, 498, 916, 987, 31], [503, 549, 619, 73, 247, 313], [251, 256, 1, 414, 917, 767], [1005, 885, 337, 273, 634, 447], [289, 612, 391, 291, 646, 555]], ![[944, 343, 565, 549, 384, 257], [701, 754, 76], [131, 409, 996, 718, 901, 637], [212, 914, 433], [590, 1008, 234, 792, 372, 788], [383, 535, 940, 734, 553, 534], [668, 131, 201, 776, 249, 199], [960, 583, 39, 922, 953, 620], [496, 226, 36, 826, 387, 806]]]
 h' := ![![[273, 152, 821, 363], [578, 144, 368, 13], [910, 394, 760, 469], [296, 424, 911, 188], [1005, 1010, 415, 575], [678, 66, 8, 591], [263, 182, 938, 232], [409, 841, 300, 375], [0, 0, 0, 1], [0, 1]], ![[861, 699, 651, 881], [567, 505, 554, 836], [940, 847, 813, 949], [417, 557, 273, 610], [441, 752, 526, 419], [887, 520, 117, 264], [41, 698, 156, 619], [133, 977, 308, 159], [779, 773, 29, 644], [273, 152, 821, 363]], ![[1002, 161, 554, 782], [814, 835, 350, 607], [512, 516, 998, 575], [278, 809, 104, 31], [795, 484, 630, 903], [897, 952, 959, 450], [981, 367, 697, 6], [349, 178, 50, 469], [867, 957, 110, 901], [861, 699, 651, 881]], ![[0, 1], [446, 542, 754, 570], [615, 269, 468, 33], [345, 236, 738, 184], [315, 793, 455, 129], [416, 488, 942, 721], [917, 779, 235, 156], [96, 30, 355, 10], [298, 296, 874, 480], [1002, 161, 554, 782]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [87, 515, 37], []]
 b := ![[], [], [760, 67, 861, 54], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A1013 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 1013 2 where
 D := ![[110, 1], [734, 806, 932, 903, 1]]; D' := ![[110, 1], [734, 806, 932, 903, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P1013P0
  | 1 => exact P1013P1

def C10130 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A1013.D 0) 1013 where
  n := 1
  w := ![![1013, 0, 0, 0, 0], ![110, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C10131 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A1013.D 1) 1013 where
  n := 4
  w := ![![1013, 0, 0, 0, 0], ![734, 806, 937, 4515, 10]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K1013 : KummerData 1013 ![I1013N0, I1013N1] ![1013, 1053022816561] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A1013
  C := by
    intro i
    match i with
    | 0 => exact C10130
    | 1 => exact C10131
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 1013 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp1019 : Fact (Nat.Prime 1019) := {out := by norm_num}

def I1019N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1019, 0, 0, 0, 0], ![370, 1, 0, 0, 0]] i)))

def I1019N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1019, 0, 0, 0, 0], ![436, 1, 0, 0, 0]] i)))

def I1019N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1019, 0, 0, 0, 0], ![249, 190, 213, 5, 0]] i)))

def P1019P0 : CertificateIrreducibleZModOfList' 1019 1 2 9 [370, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [168], [], [821], [896], [367], [748], [718], [354, 649, 1]]]
 h' := ![![[0, 1], [1018], [455], [911], [674], [756], [408], [299], [471], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P1019P1 : CertificateIrreducibleZModOfList' 1019 1 2 9 [436, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [610], [], [210], [1017], [745], [145], [642], [562, 583, 1]]]
 h' := ![![[0, 1], [1018], [82], [150], [872], [241], [977], [313], [547], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P1019P2 : CertificateIrreducibleZModOfList' 1019 3 2 9 [249, 190, 213, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [412, 18, 615], [394, 1000, 404], [0, 1]]
 g := ![![[559, 334, 168], [54, 678, 253], [404, 888], [829, 289, 215], [992, 835, 280], [269, 483, 42], [57, 341, 497], [173, 19, 533], [1]], ![[665, 503, 231, 415], [83, 512, 87, 743], [100, 484], [761, 310, 541, 408], [781, 761, 57, 925], [245, 552, 548, 120], [289, 272, 722, 944], [260, 595, 887, 412], [360, 591, 88, 226]], ![[597, 133, 896, 929], [350, 738, 372, 224], [47, 694], [295, 515, 152, 154], [519, 76, 724, 561], [933, 62, 809, 215], [328, 691, 97, 413], [796, 610, 931, 45], [507, 436, 403, 793]]]
 h' := ![![[412, 18, 615], [820, 295, 455], [847, 6, 726], [436, 788, 247], [609, 138, 802], [273, 49, 66], [73, 444, 737], [740, 963, 926], [770, 829, 806], [0, 1]], ![[394, 1000, 404], [23, 624, 569], [21, 568, 86], [495, 897, 997], [146, 345, 340], [337, 368, 349], [62, 554, 231], [559, 550, 954], [590, 740, 306], [412, 18, 615]], ![[0, 1], [245, 100, 1014], [402, 445, 207], [756, 353, 794], [636, 536, 896], [889, 602, 604], [950, 21, 51], [658, 525, 158], [679, 469, 926], [394, 1000, 404]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [273, 858], []]
 b := ![[], [577, 744, 441], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A1019 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 1019 3 where
 D := ![[370, 1], [436, 1], [249, 190, 213, 1]]; D' := ![[370, 1], [436, 1], [249, 190, 213, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9, 9]
 n := ![1, 1, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P1019P0
  | 1 => exact P1019P1
  | 2 => exact P1019P2

def C10190 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A1019.D 0) 1019 where
  n := 1
  w := ![![1019, 0, 0, 0, 0], ![370, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C10191 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A1019.D 1) 1019 where
  n := 1
  w := ![![1019, 0, 0, 0, 0], ![436, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C10192 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A1019.D 2) 1019 where
  n := 3
  w := ![![1019, 0, 0, 0, 0], ![249, 190, 213, 5, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K1019 : KummerData 1019 ![I1019N0, I1019N1, I1019N2] ![1019, 1019, 1058089859] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A1019
  C := by
    intro i
    match i with
    | 0 => exact C10190
    | 1 => exact C10191
    | 2 => exact C10192
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 1019 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


lemma PB1045I18_primes (p : ℕ) :
  p ∈ Set.range ![967, 971, 977, 983, 991, 997, 1009, 1013, 1019] ↔ Nat.Prime p ∧ 953 < p ∧ p ≤ 1019 := by
  rw [← List.mem_ofFn']
  convert primes_range 953 1019 (by omega)
  decide

def PB1045I18 : PrimesBelowBoundCertificateInterval O 953 1019 1045 where
  m := 9
  g := ![2, 1, 2, 2, 3, 2, 3, 2, 3]
  P := ![967, 971, 977, 983, 991, 997, 1009, 1013, 1019]
  hP := PB1045I18_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I967N0, I967N1]
    · exact ![I971N0]
    · exact ![I977N0, I977N1]
    · exact ![I983N0, I983N1]
    · exact ![I991N0, I991N1, I991N2]
    · exact ![I997N0, I997N1]
    · exact ![I1009N0, I1009N1, I1009N2]
    · exact ![I1013N0, I1013N1]
    · exact ![I1019N0, I1019N1, I1019N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · convert (containsPrimesAbove_of_KummerData K967) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K971) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K977) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K983) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K991) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K997) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K1009) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K1013) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K1019) <;> rfl
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![967, 874391437921]
    · exact ![863169625893851]
    · exact ![977, 911125611841]
    · exact ![966289, 949862087]
    · exact ![991, 991, 973242271]
    · exact ![994009, 991026973]
    · exact ![1009, 1009, 1027243729]
    · exact ![1013, 1053022816561]
    · exact ![1019, 1019, 1058089859]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact (card_quot_of_KummerData K967)
    · exact (card_quot_of_KummerData K971)
    · exact (card_quot_of_KummerData K977)
    · exact (card_quot_of_KummerData K983)
    · exact (card_quot_of_KummerData K991)
    · exact (card_quot_of_KummerData K997)
    · exact (card_quot_of_KummerData K1009)
    · exact (card_quot_of_KummerData K1013)
    · exact (card_quot_of_KummerData K1019)
  β := ![I967N0, I977N0, I991N0, I991N1, I1009N0, I1009N1, I1013N0, I1019N0, I1019N1]
  Il := ![[I967N0], [], [I977N0], [], [I991N0, I991N1], [], [I1009N0, I1009N1], [I1013N0], [I1019N0, I1019N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
