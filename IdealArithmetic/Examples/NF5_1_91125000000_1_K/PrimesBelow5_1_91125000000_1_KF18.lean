
import IdealArithmetic.Examples.NF5_1_91125000000_1_K.RI5_1_91125000000_1_K
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 

instance hp967 : Fact (Nat.Prime 967) := {out := by norm_num}

def I967N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![967, 0, 0, 0, 0], ![362, 801, 1, 0, 0]] i)))

def I967N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![967, 0, 0, 0, 0], ![10, 119, 166, 2, 0]] i)))

def P967P0 : CertificateIrreducibleZModOfList' 967 2 2 9 [362, 801, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [166, 966], [0, 1]]
 g := ![![[459, 772], [440, 9], [557, 585], [349], [860], [672], [453, 144], [564, 386], [166, 1]], ![[0, 195], [0, 958], [0, 382], [349], [860], [672], [182, 823], [818, 581], [332, 966]]]
 h' := ![![[166, 966], [275, 610], [469, 3], [48, 757], [941, 895], [213, 323], [404, 584], [836, 12], [829, 118], [0, 1]], ![[0, 1], [0, 357], [0, 964], [0, 210], [593, 72], [646, 644], [648, 383], [894, 955], [110, 849], [166, 966]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [801, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P967P1 : CertificateIrreducibleZModOfList' 967 3 2 9 [10, 118, 166, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [451, 145, 675], [350, 821, 292], [0, 1]]
 g := ![![[245, 584, 920], [894, 823, 410], [491, 55, 445], [572, 698], [665, 375], [477, 4], [239, 787, 664], [364, 110, 480], [1]], ![[800, 224, 42, 219], [189, 775, 439, 453], [753, 77, 144, 823], [354, 351], [87, 306], [847, 34], [34, 671, 604, 464], [715, 784, 810, 493], [100, 59, 744, 261]], ![[57, 616, 557, 728], [199, 907, 123, 815], [49, 568, 213, 953], [886, 510], [923, 338], [551, 280], [944, 5, 424, 358], [360, 440, 97, 841], [208, 536, 686, 706]]]
 h' := ![![[451, 145, 675], [730, 207, 403], [892, 351, 375], [135, 727, 400], [632, 276, 267], [96, 752, 697], [511, 440, 965], [228, 530, 549], [957, 849, 801], [0, 1]], ![[350, 821, 292], [565, 25, 626], [642, 131, 379], [174, 467, 76], [167, 302, 334], [694, 308, 665], [837, 290, 423], [556, 876, 67], [330, 83, 672], [451, 145, 675]], ![[0, 1], [76, 735, 905], [531, 485, 213], [222, 740, 491], [122, 389, 366], [252, 874, 572], [149, 237, 546], [427, 528, 351], [8, 35, 461], [350, 821, 292]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [714, 583], []]
 b := ![[], [904, 633, 714], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A967 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 967 2 where
 D := ![[362, 801, 1], [10, 118, 166, 1]]; D' := ![[362, 801, 1], [10, 118, 166, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P967P0
  | 1 => exact P967P1

def C9670 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A967.D 0) 967 where
  n := 2
  w := ![![967, 0, 0, 0, 0], ![362, 801, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C9671 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A967.D 1) 967 where
  n := 3
  w := ![![967, 0, 0, 0, 0], ![10, 119, 166, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K967 : KummerData 967 ![I967N0, I967N1] ![935089, 904231063] where
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

def I971N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![971, 0, 0, 0, 0], ![400, 1, 0, 0, 0]] i)))

def I971N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![971, 0, 0, 0, 0], ![763, 1, 0, 0, 0]] i)))

def I971N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![971, 0, 0, 0, 0], ![615, 632, 779, 2, 0]] i)))

def P971P0 : CertificateIrreducibleZModOfList' 971 1 2 9 [400, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [653], [], [229], [], [], [674], [781], [756, 571, 1]]]
 h' := ![![[0, 1], [970], [437], [645], [862], [637], [338], [262], [552], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P971P1 : CertificateIrreducibleZModOfList' 971 1 2 9 [763, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [957], [], [243], [], [], [963], [814], [540, 208, 1]]]
 h' := ![![[0, 1], [1], [762], [52], [485], [575], [278], [358], [655], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P971P2 : CertificateIrreducibleZModOfList' 971 3 2 9 [615, 631, 779, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [487, 745, 208], [676, 225, 763], [0, 1]]
 g := ![![[926, 394, 119], [740, 782, 799], [591, 938], [844, 631, 445], [757, 310], [158, 57], [372, 453, 425], [305, 715, 937], [1]], ![[195, 29, 335, 352], [816, 483, 55, 112], [224, 426], [813, 536, 391, 653], [332, 475], [11, 501], [919, 717, 948, 625], [717, 496, 300, 146], [151, 717, 448, 655]], ![[860, 406, 819, 366], [696, 124, 409, 288], [359, 931], [678, 808, 543, 635], [329, 705], [532, 484], [408, 318, 256, 327], [667, 432, 578, 530], [918, 88, 845, 316]]]
 h' := ![![[487, 745, 208], [299, 613, 327], [679, 934, 173], [425, 633, 560], [447, 43, 651], [511, 920, 281], [376, 786, 617], [799, 447, 499], [356, 340, 192], [0, 1]], ![[676, 225, 763], [368, 885, 82], [129, 76, 157], [742, 281, 349], [110, 619, 59], [737, 346, 183], [507, 696, 332], [234, 814, 370], [233, 658, 313], [487, 745, 208]], ![[0, 1], [970, 444, 562], [44, 932, 641], [817, 57, 62], [404, 309, 261], [152, 676, 507], [153, 460, 22], [751, 681, 102], [446, 944, 466], [676, 225, 763]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [901, 128], []]
 b := ![[], [218, 571, 821], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A971 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 971 3 where
 D := ![[400, 1], [763, 1], [615, 631, 779, 1]]; D' := ![[400, 1], [763, 1], [615, 631, 779, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9, 9]
 n := ![1, 1, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P971P0
  | 1 => exact P971P1
  | 2 => exact P971P2

def C9710 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A971.D 0) 971 where
  n := 1
  w := ![![971, 0, 0, 0, 0], ![400, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C9711 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A971.D 1) 971 where
  n := 1
  w := ![![971, 0, 0, 0, 0], ![763, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C9712 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A971.D 2) 971 where
  n := 3
  w := ![![971, 0, 0, 0, 0], ![615, 632, 779, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K971 : KummerData 971 ![I971N0, I971N1, I971N2] ![971, 971, 915498611] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A971
  C := by
    intro i
    match i with
    | 0 => exact C9710
    | 1 => exact C9711
    | 2 => exact C9712
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 971 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp977 : Fact (Nat.Prime 977) := {out := by norm_num}

def I977N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![977, 0, 0, 0, 0], ![369, 831, 1, 0, 0]] i)))

def I977N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![977, 0, 0, 0, 0], ![13, 431, 146, 2, 0]] i)))

def P977P0 : CertificateIrreducibleZModOfList' 977 2 2 9 [369, 831, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [146, 976], [0, 1]]
 g := ![![[177, 715], [914], [318], [89], [258, 228], [573], [187, 854], [544, 247], [146, 1]], ![[28, 262], [914], [318], [89], [328, 749], [573], [792, 123], [457, 730], [292, 976]]]
 h' := ![![[146, 976], [910, 785], [285, 602], [282, 920], [544, 745], [196, 808], [364, 576], [526, 763], [838, 430], [0, 1]], ![[0, 1], [234, 192], [247, 375], [753, 57], [867, 232], [924, 169], [438, 401], [546, 214], [113, 547], [146, 976]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [495]]
 b := ![[], [7, 736]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P977P1 : CertificateIrreducibleZModOfList' 977 3 2 9 [13, 430, 146, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [213, 18, 178], [618, 958, 799], [0, 1]]
 g := ![![[660, 394, 64], [501, 698], [274, 404], [48, 157], [582, 747, 142], [935, 265], [135, 614, 682], [580, 113, 799], [1]], ![[68, 485, 258, 760], [730, 480], [109, 820], [516, 130], [83, 178, 634, 349], [714, 261], [11, 705, 241, 57], [76, 145, 830, 624], [90, 410, 293, 508]], ![[431, 950, 165, 396], [243, 969], [532, 759], [230, 98], [497, 739, 457, 312], [4, 513], [137, 231, 348, 619], [27, 140, 390, 774], [755, 349, 401, 469]]]
 h' := ![![[213, 18, 178], [227, 975, 8], [455, 251, 385], [325, 567, 421], [250, 195, 109], [90, 308, 747], [199, 374, 292], [276, 389, 395], [964, 547, 831], [0, 1]], ![[618, 958, 799], [569, 234, 469], [17, 170, 237], [307, 234, 112], [468, 594, 398], [626, 224, 574], [423, 955, 450], [882, 549, 186], [874, 522, 486], [213, 18, 178]], ![[0, 1], [666, 745, 500], [359, 556, 355], [327, 176, 444], [85, 188, 470], [857, 445, 633], [834, 625, 235], [849, 39, 396], [442, 885, 637], [618, 958, 799]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35, 240], []]
 b := ![[], [929, 102, 317], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A977 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 977 2 where
 D := ![[369, 831, 1], [13, 430, 146, 1]]; D' := ![[369, 831, 1], [13, 430, 146, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P977P0
  | 1 => exact P977P1

def C9770 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A977.D 0) 977 where
  n := 2
  w := ![![977, 0, 0, 0, 0], ![369, 831, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C9771 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A977.D 1) 977 where
  n := 3
  w := ![![977, 0, 0, 0, 0], ![13, 431, 146, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K977 : KummerData 977 ![I977N0, I977N1] ![954529, 932574833] where
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

def I983N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![983, 0, 0, 0, 0], ![829, 1, 0, 0, 0]] i)))

def I983N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![983, 0, 0, 0, 0], ![1082, 2575, 11019, -2730, 22728]] i)))

def P983P0 : CertificateIrreducibleZModOfList' 983 1 2 9 [829, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [300], [389], [], [589], [], [461], [587], [124, 154, 1]]]
 h' := ![![[0, 1], [982], [926], [158], [270], [340], [218], [945], [419], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P983P1 : CertificateIrreducibleZModOfList' 983 4 2 9 [434, 319, 124, 154, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [486, 174, 604, 873], [81, 787, 782, 971], [262, 21, 580, 122], [0, 1]]
 g := ![![[17, 383, 307, 754], [945, 733, 859, 322], [129, 562, 701, 434], [164, 421, 326], [979, 259, 744, 266], [231, 154, 289], [716, 194, 258, 189], [100, 0, 829, 1], []], ![[703, 611, 633, 811, 671, 605], [146, 873, 206, 538, 862, 418], [867, 790, 184, 37, 397, 702], [852, 534, 79], [504, 528, 177, 959, 906, 591], [91, 668, 809], [433, 405, 248, 53, 438, 546], [572, 345, 814, 107, 663, 229], [59, 875, 92, 480, 191, 965]], ![[585, 240, 634, 365, 932, 569], [33, 531, 525, 598, 434, 759], [808, 549, 61, 887, 771, 946], [210, 225, 118], [53, 132, 891, 954, 178, 254], [773, 232, 534], [689, 517, 164, 562, 124, 852], [790, 158, 456, 608, 175, 314], [832, 395, 889, 649, 374, 238]], ![[326, 156, 618, 370, 201, 662], [842, 328, 658, 839, 153, 210], [253, 735, 562, 293, 453, 962], [822, 165, 613], [124, 391, 260, 919, 532, 916], [359, 828, 621], [664, 223, 690, 752, 639, 445], [418, 261, 523, 946, 545, 605], [520, 620, 90, 7, 341, 247]]]
 h' := ![![[486, 174, 604, 873], [764, 755, 46, 400], [45, 583, 678, 802], [401, 582, 519, 799], [753, 864, 495, 632], [689, 835, 593, 496], [867, 272, 504, 17], [835, 539, 371, 853], [0, 0, 0, 1], [0, 1]], ![[81, 787, 782, 971], [573, 795, 704, 507], [264, 61, 747, 240], [701, 962, 617, 843], [907, 393, 885, 196], [107, 489, 110, 841], [199, 605, 203, 662], [236, 850, 103, 784], [400, 98, 545, 914], [486, 174, 604, 873]], ![[262, 21, 580, 122], [651, 421, 652, 610], [854, 67, 975, 221], [714, 411, 928, 109], [49, 310, 700, 393], [814, 603, 859, 515], [191, 571, 864, 50], [597, 902, 827, 627], [294, 21, 188, 333], [81, 787, 782, 971]], ![[0, 1], [570, 978, 564, 449], [50, 272, 549, 703], [405, 11, 885, 215], [18, 399, 869, 745], [495, 39, 404, 114], [2, 518, 395, 254], [194, 658, 665, 685], [170, 864, 250, 718], [262, 21, 580, 122]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [896, 277, 919], []]
 b := ![[], [], [5, 424, 356, 650], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A983 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 983 2 where
 D := ![[829, 1], [434, 319, 124, 154, 1]]; D' := ![[829, 1], [434, 319, 124, 154, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P983P0
  | 1 => exact P983P1

def C9830 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A983.D 0) 983 where
  n := 1
  w := ![![983, 0, 0, 0, 0], ![829, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C9831 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A983.D 1) 983 where
  n := 4
  w := ![![983, 0, 0, 0, 0], ![1082, 2575, 11019, -2730, 22728]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K983 : KummerData 983 ![I983N0, I983N1] ![983, 933714431521] where
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

def I991N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![991, 0, 0, 0, 0], ![25, 1, 0, 0, 0]] i)))

def I991N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![991, 0, 0, 0, 0], ![350, 1, 0, 0, 0]] i)))

def I991N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![991, 0, 0, 0, 0], ![697, 73, 616, 2, 0]] i)))

def P991P0 : CertificateIrreducibleZModOfList' 991 1 2 9 [25, 1] where
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
 g := ![![[], [555], [111], [187], [576], [], [492], [838], [625, 966, 1]]]
 h' := ![![[0, 1], [990], [198], [280], [465], [967], [583], [852], [231], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P991P1 : CertificateIrreducibleZModOfList' 991 1 2 9 [350, 1] where
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
 g := ![![[], [739], [208], [963], [261], [], [441], [654], [607, 641, 1]]]
 h' := ![![[0, 1], [1], [534], [881], [813], [65], [246], [21], [615], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P991P2 : CertificateIrreducibleZModOfList' 991 3 2 9 [697, 72, 616, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [491, 237, 875], [875, 753, 116], [0, 1]]
 g := ![![[632, 57, 964], [626, 637, 290], [671, 807, 10], [777, 952, 179], [133, 83, 559], [374, 793], [70, 746, 13], [367, 797, 894], [1]], ![[355, 495, 563, 366], [135, 471, 231, 30], [681, 982, 705, 732], [96, 462, 364, 381], [380, 33, 837, 540], [22, 637], [707, 565, 54, 509], [693, 430, 441, 874], [636, 68, 234, 920]], ![[343, 33, 892, 565], [611, 149, 542, 202], [259, 95, 21, 903], [116, 76, 164, 620], [371, 171, 856, 810], [358, 543], [493, 771, 562, 84], [704, 314, 247, 361], [643, 726, 29, 71]]]
 h' := ![![[491, 237, 875], [709, 754, 681], [65, 69, 502], [508, 50, 694], [453, 516, 223], [793, 220, 249], [760, 4, 409], [870, 3, 468], [294, 919, 375], [0, 1]], ![[875, 753, 116], [432, 771, 190], [645, 390, 359], [225, 197, 471], [934, 6, 44], [222, 778, 444], [288, 85, 303], [62, 935, 251], [461, 242, 364], [491, 237, 875]], ![[0, 1], [695, 457, 120], [505, 532, 130], [937, 744, 817], [989, 469, 724], [71, 984, 298], [290, 902, 279], [16, 53, 272], [681, 821, 252], [875, 753, 116]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 974], []]
 b := ![[], [496, 512, 128], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A991 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 991 3 where
 D := ![[25, 1], [350, 1], [697, 72, 616, 1]]; D' := ![[25, 1], [350, 1], [697, 72, 616, 1]]
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
  w := ![![991, 0, 0, 0, 0], ![25, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C9911 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A991.D 1) 991 where
  n := 1
  w := ![![991, 0, 0, 0, 0], ![350, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C9912 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A991.D 2) 991 where
  n := 3
  w := ![![991, 0, 0, 0, 0], ![697, 73, 616, 2, 0]]
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

def I997N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![997, 0, 0, 0, 0], ![918, 1, 0, 0, 0]] i)))

def I997N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![997, 0, 0, 0, 0], ![1478, 2602, 11154, -2880, 22728]] i)))

def P997P0 : CertificateIrreducibleZModOfList' 997 1 2 9 [918, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [366], [], [], [491], [165], [257], [259, 79, 1]]]
 h' := ![![[0, 1], [1], [1], [823], [860], [903], [74], [363], [521], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P997P1 : CertificateIrreducibleZModOfList' 997 4 2 9 [830, 421, 259, 79, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [748, 747, 630, 786], [971, 222, 512, 719], [196, 27, 852, 489], [0, 1]]
 g := ![![[100, 144, 994, 27], [197, 163, 137], [788, 838, 19, 171], [276, 191, 542], [263, 683, 417], [758, 27, 222, 555], [492, 944, 79, 287], [100, 0, 918, 1], []], ![[445, 938, 601, 262, 384, 283], [708, 853, 75], [647, 889, 270, 528, 185, 719], [686, 914, 596], [953, 329, 983], [393, 941, 743, 100, 461, 367], [245, 304, 844, 26, 84, 95], [787, 765, 598, 44, 232, 129], [866, 533, 835, 286, 492, 800]], ![[205, 685, 438, 524, 673, 879], [226, 943, 324], [263, 459, 951, 421, 656, 649], [243, 489, 331], [746, 750, 453], [744, 22, 751, 452, 183, 176], [430, 500, 547, 947, 743, 323], [282, 314, 265, 39, 717, 533], [889, 42, 793, 865, 881, 398]], ![[838, 636, 926, 317, 275, 600], [492, 263, 182], [168, 808, 651, 968, 491, 601], [420, 776, 866], [631, 940, 785], [937, 276, 836, 101, 14, 335], [205, 945, 901, 833, 205, 704], [883, 777, 519, 670, 700, 965], [340, 850, 987, 90, 184, 15]]]
 h' := ![![[748, 747, 630, 786], [62, 329, 376, 32], [989, 49, 933, 179], [318, 499, 257, 519], [145, 38, 682, 560], [964, 50, 694, 86], [410, 553, 686, 620], [748, 771, 787, 601], [0, 0, 0, 1], [0, 1]], ![[971, 222, 512, 719], [793, 945, 588, 542], [119, 130, 5, 279], [63, 654, 79, 36], [681, 58, 937, 381], [433, 294, 456, 232], [820, 716, 478, 646], [818, 372, 867, 994], [353, 921, 336, 525], [748, 747, 630, 786]], ![[196, 27, 852, 489], [543, 276, 25, 868], [248, 98, 786, 979], [923, 93, 521, 889], [333, 844, 659, 406], [734, 898, 727, 525], [689, 564, 819, 366], [700, 885, 42, 643], [280, 210, 889, 229], [971, 222, 512, 719]], ![[0, 1], [7, 444, 8, 552], [671, 720, 270, 557], [619, 748, 140, 550], [106, 57, 713, 647], [417, 752, 117, 154], [260, 161, 11, 362], [966, 963, 298, 753], [143, 863, 769, 242], [196, 27, 852, 489]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [171, 996, 623], []]
 b := ![[], [], [52, 303, 825, 13], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A997 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 997 2 where
 D := ![[918, 1], [830, 421, 259, 79, 1]]; D' := ![[918, 1], [830, 421, 259, 79, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P997P0
  | 1 => exact P997P1

def C9970 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A997.D 0) 997 where
  n := 1
  w := ![![997, 0, 0, 0, 0], ![918, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C9971 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A997.D 1) 997 where
  n := 4
  w := ![![997, 0, 0, 0, 0], ![1478, 2602, 11154, -2880, 22728]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K997 : KummerData 997 ![I997N0, I997N1] ![997, 988053892081] where
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

def I1009N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1009, 0, 0, 0, 0], ![938, 1, 0, 0, 0]] i)))

def I1009N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1009, 0, 0, 0, 0], ![32, 531, 1, 0, 0]] i)))

def I1009N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1009, 0, 0, 0, 0], ![46, 549, 1, 0, 0]] i)))

def P1009P0 : CertificateIrreducibleZModOfList' 1009 1 2 9 [938, 1] where
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
 g := ![![[], [], [], [], [913], [661], [769], [945], [1005, 71, 1]]]
 h' := ![![[0, 1], [1], [1008], [469], [247], [517], [113], [501], [725], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P1009P1 : CertificateIrreducibleZModOfList' 1009 2 2 9 [32, 531, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [478, 1008], [0, 1]]
 g := ![![[931, 473], [991], [766], [350], [406, 331], [973, 30], [357, 3], [725, 167], [478, 1]], ![[0, 536], [991], [766], [350], [211, 678], [178, 979], [782, 1006], [840, 842], [956, 1008]]]
 h' := ![![[478, 1008], [256, 181], [684, 165], [389, 322], [125, 107], [143, 683], [684, 78], [7, 860], [848, 418], [0, 1]], ![[0, 1], [0, 828], [852, 844], [937, 687], [821, 902], [710, 326], [635, 931], [424, 149], [870, 591], [478, 1008]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [188]]
 b := ![[], [741, 94]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P1009P2 : CertificateIrreducibleZModOfList' 1009 2 2 9 [46, 549, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [460, 1008], [0, 1]]
 g := ![![[999, 829], [561], [649], [700], [271, 897], [384, 216], [769, 72], [631, 897], [460, 1]], ![[937, 180], [561], [649], [700], [210, 112], [862, 793], [592, 937], [570, 112], [920, 1008]]]
 h' := ![![[460, 1008], [834, 513], [189, 672], [109, 809], [651, 450], [498, 673], [950, 35], [235, 616], [29, 673], [0, 1]], ![[0, 1], [708, 496], [555, 337], [937, 200], [806, 559], [315, 336], [906, 974], [66, 393], [855, 336], [460, 1008]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [860]]
 b := ![[], [991, 430]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A1009 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 1009 3 where
 D := ![[938, 1], [32, 531, 1], [46, 549, 1]]; D' := ![[938, 1], [32, 531, 1], [46, 549, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9, 9]
 n := ![1, 2, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P1009P0
  | 1 => exact P1009P1
  | 2 => exact P1009P2

def C10090 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A1009.D 0) 1009 where
  n := 1
  w := ![![1009, 0, 0, 0, 0], ![938, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C10091 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A1009.D 1) 1009 where
  n := 2
  w := ![![1009, 0, 0, 0, 0], ![32, 531, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C10092 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A1009.D 2) 1009 where
  n := 2
  w := ![![1009, 0, 0, 0, 0], ![46, 549, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K1009 : KummerData 1009 ![I1009N0, I1009N1, I1009N2] ![1009, 1018081, 1018081] where
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

def I1013N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1013, 0, 0, 0, 0], ![844, 1, 0, 0, 0]] i)))

def I1013N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1013, 0, 0, 0, 0], ![759, 3048, 11092, -2700, 22728]] i)))

def P1013P0 : CertificateIrreducibleZModOfList' 1013 1 2 9 [844, 1] where
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
 g := ![![[], [], [6], [], [163], [539], [331], [262], [197, 169, 1]]]
 h' := ![![[0, 1], [1], [1], [935], [196], [934], [224], [719], [877], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P1013P1 : CertificateIrreducibleZModOfList' 1013 4 2 9 [111, 777, 197, 169, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [320, 386, 786, 448], [573, 368, 204, 659], [964, 258, 23, 919], [0, 1]]
 g := ![![[61, 245, 146, 240], [366, 988, 899], [26, 858, 886, 998], [755, 248, 231], [463, 33, 52, 309], [97, 697, 177, 796], [75, 841, 512, 538], [100, 0, 844, 1], []], ![[975, 382, 416, 332, 447, 381], [336, 770, 322], [782, 711, 412, 543, 557, 787], [987, 850, 110], [28, 268, 443, 979, 469, 776], [768, 756, 528, 718, 622, 819], [642, 508, 208, 274, 284, 599], [805, 222, 783, 83, 154, 672], [693, 70, 995, 394, 362, 499]], ![[179, 1007, 432, 798, 892, 598], [998, 118, 873], [38, 746, 452, 662, 663, 516], [604, 426, 437], [66, 969, 60, 521, 763, 908], [690, 225, 432, 100, 254, 443], [930, 884, 45, 84, 532, 731], [313, 992, 586, 528, 657, 234], [678, 725, 988, 202, 945, 445]], ![[710, 447, 40, 229, 622, 989], [960, 468, 809], [470, 241, 296, 930, 228, 992], [456, 817, 208], [383, 876, 533, 822, 89, 235], [805, 446, 933, 249, 193, 998], [369, 584, 753, 846, 10, 782], [755, 586, 904, 129, 918, 657], [811, 472, 802, 733, 183, 76]]]
 h' := ![![[320, 386, 786, 448], [4, 324, 623, 366], [153, 971, 233, 839], [238, 914, 173, 572], [270, 822, 560, 850], [376, 444, 995, 377], [792, 147, 805, 828], [43, 301, 72, 846], [0, 0, 0, 1], [0, 1]], ![[573, 368, 204, 659], [228, 16, 746, 98], [146, 944, 896, 933], [939, 767, 80, 132], [363, 219, 294, 860], [631, 697, 409, 898], [495, 517, 687, 958], [533, 782, 379, 386], [554, 235, 585, 974], [320, 386, 786, 448]], ![[964, 258, 23, 919], [1012, 849, 742, 930], [921, 450, 462, 845], [784, 579, 883, 277], [521, 892, 577, 67], [340, 328, 906, 406], [537, 853, 382, 181], [450, 688, 483, 783], [900, 23, 861, 84], [573, 368, 204, 659]], ![[0, 1], [108, 837, 928, 632], [207, 674, 435, 422], [69, 779, 890, 32], [741, 93, 595, 249], [856, 557, 729, 345], [636, 509, 152, 59], [62, 255, 79, 11], [1008, 755, 580, 967], [964, 258, 23, 919]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [48, 735, 537], []]
 b := ![[], [], [613, 496, 509, 405], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A1013 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 1013 2 where
 D := ![[844, 1], [111, 777, 197, 169, 1]]; D' := ![[844, 1], [111, 777, 197, 169, 1]]
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
  w := ![![1013, 0, 0, 0, 0], ![844, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C10131 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A1013.D 1) 1013 where
  n := 4
  w := ![![1013, 0, 0, 0, 0], ![759, 3048, 11092, -2700, 22728]]
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

def I1019N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1019, 0, 0, 0, 0], ![416, 1, 0, 0, 0]] i)))

def I1019N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1019, 0, 0, 0, 0], ![727, 1, 0, 0, 0]] i)))

def I1019N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1019, 0, 0, 0, 0], ![485, 303, 895, 2, 0]] i)))

def P1019P0 : CertificateIrreducibleZModOfList' 1019 1 2 9 [416, 1] where
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
 g := ![![[], [267], [], [886], [543], [735], [829], [206], [845, 603, 1]]]
 h' := ![![[0, 1], [1018], [513], [302], [330], [959], [577], [919], [35], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P1019P1 : CertificateIrreducibleZModOfList' 1019 1 2 9 [727, 1] where
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
 g := ![![[], [171], [], [277], [42], [329], [718], [979], [687, 292, 1]]]
 h' := ![![[0, 1], [1], [972], [383], [36], [282], [761], [548], [880], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P1019P2 : CertificateIrreducibleZModOfList' 1019 3 2 9 [485, 302, 895, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [87, 333, 919], [37, 685, 100], [0, 1]]
 g := ![![[773, 798, 621], [815, 936, 326], [930, 591], [247, 379, 670], [833, 655, 876], [854, 255, 542], [71, 779, 818], [697, 585, 91], [1]], ![[432, 249, 633, 550], [314, 700, 1000, 194], [438, 685], [571, 287, 587, 647], [917, 418, 347, 524], [118, 2, 347, 306], [357, 818, 268, 962], [408, 999, 480, 195], [423, 83, 815, 658]], ![[764, 333, 765, 931], [794, 52, 81, 224], [810, 322], [146, 631, 742, 426], [919, 199, 769, 134], [607, 590, 541, 502], [207, 527, 799, 296], [871, 1016, 464, 383], [947, 293, 774, 361]]]
 h' := ![![[87, 333, 919], [97, 467, 429], [452, 46, 767], [447, 465, 126], [538, 738, 236], [543, 227, 550], [211, 68, 729], [263, 851, 618], [534, 717, 124], [0, 1]], ![[37, 685, 100], [36, 949, 567], [287, 832, 86], [697, 67, 69], [519, 656, 226], [54, 2, 457], [531, 1008, 388], [306, 592, 941], [912, 585, 1012], [87, 333, 919]], ![[0, 1], [10, 622, 23], [70, 141, 166], [352, 487, 824], [552, 644, 557], [761, 790, 12], [167, 962, 921], [662, 595, 479], [996, 736, 902], [37, 685, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [130, 359], []]
 b := ![[], [388, 541, 401], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A1019 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 1019 3 where
 D := ![[416, 1], [727, 1], [485, 302, 895, 1]]; D' := ![[416, 1], [727, 1], [485, 302, 895, 1]]
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
  w := ![![1019, 0, 0, 0, 0], ![416, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C10191 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A1019.D 1) 1019 where
  n := 1
  w := ![![1019, 0, 0, 0, 0], ![727, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C10192 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A1019.D 2) 1019 where
  n := 3
  w := ![![1019, 0, 0, 0, 0], ![485, 303, 895, 2, 0]]
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


lemma PB18792I18_primes (p : ℕ) :
  p ∈ Set.range ![967, 971, 977, 983, 991, 997, 1009, 1013, 1019] ↔ Nat.Prime p ∧ 953 < p ∧ p ≤ 1019 := by
  rw [← List.mem_ofFn']
  convert primes_range 953 1019 (by omega)
  decide

def PB18792I18 : PrimesBelowBoundCertificateInterval O 953 1019 18792 where
  m := 9
  g := ![2, 3, 2, 2, 3, 2, 3, 2, 3]
  P := ![967, 971, 977, 983, 991, 997, 1009, 1013, 1019]
  hP := PB18792I18_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I967N0, I967N1]
    · exact ![I971N0, I971N1, I971N2]
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
    · exact ![935089, 904231063]
    · exact ![971, 971, 915498611]
    · exact ![954529, 932574833]
    · exact ![983, 933714431521]
    · exact ![991, 991, 973242271]
    · exact ![997, 988053892081]
    · exact ![1009, 1018081, 1018081]
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
  β := ![I971N0, I971N1, I983N0, I991N0, I991N1, I997N0, I1009N0, I1013N0, I1019N0, I1019N1]
  Il := ![[], [I971N0, I971N1], [], [I983N0], [I991N0, I991N1], [I997N0], [I1009N0], [I1013N0], [I1019N0, I1019N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
