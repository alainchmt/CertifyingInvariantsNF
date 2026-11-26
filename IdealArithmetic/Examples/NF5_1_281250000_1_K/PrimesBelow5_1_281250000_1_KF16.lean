
import IdealArithmetic.Examples.NF5_1_281250000_1_K.RI5_1_281250000_1_K
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 

instance hp829 : Fact (Nat.Prime 829) := {out := by norm_num}

def I829N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![829, 0, 0, 0, 0], ![618, 1, 0, 0, 0]] i)))

def I829N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![829, 0, 0, 0, 0], ![533, 361, 1, 0, 0]] i)))

def I829N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![829, 0, 0, 0, 0], ![291, 679, 1, 0, 0]] i)))

def P829P0 : CertificateIrreducibleZModOfList' 829 1 2 9 [618, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [55], [205], [399], [765], [], [], [584, 211, 1]]]
 h' := ![![[0, 1], [1], [828], [147], [460], [589], [310], [335], [532], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P829P1 : CertificateIrreducibleZModOfList' 829 2 2 9 [533, 361, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [468, 828], [0, 1]]
 g := ![![[80, 14], [275], [188, 297], [676, 443], [149, 418], [469, 335], [310], [585], [468, 1]], ![[0, 815], [275], [741, 532], [750, 386], [129, 411], [568, 494], [310], [585], [107, 828]]]
 h' := ![![[468, 828], [406, 527], [105, 720], [307, 368], [167, 389], [381, 678], [566, 532], [492, 335], [85, 464], [0, 1]], ![[0, 1], [0, 302], [491, 109], [99, 461], [668, 440], [178, 151], [13, 297], [591, 494], [39, 365], [468, 828]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [233]]
 b := ![[], [96, 531]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P829P2 : CertificateIrreducibleZModOfList' 829 2 2 9 [291, 679, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [150, 828], [0, 1]]
 g := ![![[555, 245], [411], [99, 350], [769, 375], [269, 41], [511, 637], [244], [432], [150, 1]], ![[0, 584], [411], [372, 479], [647, 454], [616, 788], [726, 192], [244], [432], [300, 828]]]
 h' := ![![[150, 828], [761, 321], [206, 159], [51, 681], [476, 169], [519, 666], [801, 350], [594, 571], [287, 655], [0, 1]], ![[0, 1], [0, 508], [15, 670], [234, 148], [127, 660], [110, 163], [245, 479], [28, 258], [715, 174], [150, 828]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [251]]
 b := ![[], [121, 540]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A829 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 829 3 where
 D := ![[618, 1], [533, 361, 1], [291, 679, 1]]; D' := ![[618, 1], [533, 361, 1], [291, 679, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9, 9]
 n := ![1, 2, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P829P0
  | 1 => exact P829P1
  | 2 => exact P829P2

def C8290 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A829.D 0) 829 where
  n := 1
  w := ![![829, 0, 0, 0, 0], ![618, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C8291 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A829.D 1) 829 where
  n := 2
  w := ![![829, 0, 0, 0, 0], ![533, 361, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C8292 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A829.D 2) 829 where
  n := 2
  w := ![![829, 0, 0, 0, 0], ![291, 679, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K829 : KummerData 829 ![I829N0, I829N1, I829N2] ![829, 687241, 687241] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A829
  C := by
    intro i
    match i with
    | 0 => exact C8290
    | 1 => exact C8291
    | 2 => exact C8292
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 829 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp839 : Fact (Nat.Prime 839) := {out := by norm_num}

def I839N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![839, 0, 0, 0, 0], ![588, 1, 0, 0, 0]] i)))

def I839N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![839, 0, 0, 0, 0], ![796, 1, 0, 0, 0]] i)))

def I839N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![839, 0, 0, 0, 0], ![665, 108, 294, 5, 0]] i)))

def P839P0 : CertificateIrreducibleZModOfList' 839 1 2 9 [588, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [361], [147], [], [], [], [159], [], [76, 251, 1]]]
 h' := ![![[0, 1], [838], [820], [552], [438], [46], [476], [179], [618], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P839P1 : CertificateIrreducibleZModOfList' 839 1 2 9 [796, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [800], [806], [], [], [], [423], [], [171, 43, 1]]]
 h' := ![![[0, 1], [1], [259], [244], [60], [207], [570], [610], [641], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P839P2 : CertificateIrreducibleZModOfList' 839 3 2 9 [665, 108, 294, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [415, 714, 501], [130, 124, 338], [0, 1]]
 g := ![![[94, 582, 14], [663, 789, 805], [290, 36, 635], [531, 541], [301, 621], [544, 150], [421, 26, 86], [27, 19], [1]], ![[621, 805, 611, 830], [456, 281, 746, 326], [818, 264, 171, 214], [776, 467], [193, 676], [370, 685], [689, 183, 630, 277], [568, 626], [234, 170, 139, 503]], ![[139, 67, 62, 377], [202, 833, 91, 271], [509, 405, 809, 795], [724, 516], [213, 826], [715, 23], [358, 777, 304, 138], [245, 108], [677, 722, 280, 336]]]
 h' := ![![[415, 714, 501], [419, 377, 458], [120, 173, 228], [264, 656, 95], [477, 233, 103], [11, 581, 122], [261, 226, 767], [575, 561, 42], [174, 731, 545], [0, 1]], ![[130, 124, 338], [834, 72, 681], [149, 339, 2], [550, 704, 641], [38, 374, 299], [835, 95, 813], [667, 52, 262], [87, 202, 170], [248, 280, 48], [415, 714, 501]], ![[0, 1], [300, 390, 539], [798, 327, 609], [666, 318, 103], [218, 232, 437], [665, 163, 743], [452, 561, 649], [689, 76, 627], [836, 667, 246], [130, 124, 338]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [414, 809], []]
 b := ![[], [26, 300, 407], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A839 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 839 3 where
 D := ![[588, 1], [796, 1], [665, 108, 294, 1]]; D' := ![[588, 1], [796, 1], [665, 108, 294, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9, 9]
 n := ![1, 1, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P839P0
  | 1 => exact P839P1
  | 2 => exact P839P2

def C8390 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A839.D 0) 839 where
  n := 1
  w := ![![839, 0, 0, 0, 0], ![588, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C8391 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A839.D 1) 839 where
  n := 1
  w := ![![839, 0, 0, 0, 0], ![796, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C8392 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A839.D 2) 839 where
  n := 3
  w := ![![839, 0, 0, 0, 0], ![665, 108, 294, 5, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K839 : KummerData 839 ![I839N0, I839N1, I839N2] ![839, 839, 590589719] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A839
  C := by
    intro i
    match i with
    | 0 => exact C8390
    | 1 => exact C8391
    | 2 => exact C8392
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 839 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp853 : Fact (Nat.Prime 853) := {out := by norm_num}

def I853N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![853, 0, 0, 0, 0], ![69, 1, 0, 0, 0]] i)))

def I853N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![853, 0, 0, 0, 0], ![144, 768, 476, 3920, 10]] i)))

def P853P0 : CertificateIrreducibleZModOfList' 853 1 2 9 [69, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [136], [], [732], [], [318], [], [496, 784, 1]]]
 h' := ![![[0, 1], [1], [852], [347], [672], [251], [236], [580], [749], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P853P1 : CertificateIrreducibleZModOfList' 853 4 2 9 [144, 768, 471, 784, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [830, 236, 274, 126], [575, 222, 719, 85], [370, 394, 713, 642], [0, 1]]
 g := ![![[788, 265, 176, 140], [254, 760, 503], [102, 132, 2, 169], [655, 724, 665], [2, 503, 472, 236], [388, 827, 123], [568, 475, 430, 361], [25, 69, 1], []], ![[55, 703, 62, 548, 314, 724], [304, 331, 218], [317, 693, 271, 106, 290, 289], [93, 641, 93], [669, 53, 609, 823, 105, 504], [123, 120, 730], [724, 680, 744, 457, 25, 642], [688, 362, 268], [697, 204, 275, 233, 333, 91]], ![[266, 303, 285, 516, 111, 772], [515, 773, 724], [784, 267, 347, 834, 707, 228], [314, 633, 231], [226, 617, 140, 542, 418, 249], [502, 390, 181], [634, 709, 228, 281, 156, 83], [781, 564, 424], [525, 315, 8, 113, 159, 818]], ![[613, 352, 586, 175, 482, 560], [376, 264, 506], [393, 478, 37, 91, 467, 306], [477, 276, 593], [107, 497, 38, 621, 109, 395], [597, 29, 496], [586, 305, 427, 363, 394, 555], [254, 232, 837], [148, 600, 287, 534, 459, 158]]]
 h' := ![![[830, 236, 274, 126], [99, 714, 130, 121], [666, 379, 588, 806], [566, 502, 350, 840], [565, 790, 208, 361], [259, 675, 174, 33], [96, 723, 151, 178], [665, 719, 770, 19], [0, 0, 0, 1], [0, 1]], ![[575, 222, 719, 85], [220, 703, 460, 530], [195, 563, 780, 574], [427, 297, 99, 110], [821, 276, 360, 409], [611, 172, 445, 851], [807, 267, 453, 436], [185, 636, 767, 662], [61, 79, 438, 176], [830, 236, 274, 126]], ![[370, 394, 713, 642], [245, 463, 207, 79], [462, 321, 793, 616], [223, 276, 812, 409], [44, 251, 314, 250], [468, 234, 653, 149], [617, 542, 267, 308], [154, 440, 733, 549], [729, 389, 581, 197], [575, 222, 719, 85]], ![[0, 1], [290, 679, 56, 123], [49, 443, 398, 563], [213, 631, 445, 347], [116, 389, 824, 686], [250, 625, 434, 673], [770, 174, 835, 784], [696, 764, 289, 476], [167, 385, 687, 479], [370, 394, 713, 642]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [344, 596, 10], []]
 b := ![[], [], [574, 83, 57, 602], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A853 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 853 2 where
 D := ![[69, 1], [144, 768, 471, 784, 1]]; D' := ![[69, 1], [144, 768, 471, 784, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P853P0
  | 1 => exact P853P1

def C8530 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A853.D 0) 853 where
  n := 1
  w := ![![853, 0, 0, 0, 0], ![69, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C8531 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A853.D 1) 853 where
  n := 4
  w := ![![853, 0, 0, 0, 0], ![144, 768, 476, 3920, 10]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K853 : KummerData 853 ![I853N0, I853N1] ![853, 529414856881] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A853
  C := by
    intro i
    match i with
    | 0 => exact C8530
    | 1 => exact C8531
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 853 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp857 : Fact (Nat.Prime 857) := {out := by norm_num}

def I857N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![857, 0, 0, 0, 0], ![360, 249, 1, 0, 0]] i)))

def I857N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![857, 0, 0, 0, 0], ![142, 769, 608, 5, 0]] i)))

def P857P0 : CertificateIrreducibleZModOfList' 857 2 2 9 [360, 249, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [608, 856], [0, 1]]
 g := ![![[722, 576], [261], [271], [711, 369], [551, 223], [60], [431, 778], [541], [608, 1]], ![[417, 281], [261], [271], [529, 488], [729, 634], [60], [391, 79], [541], [359, 856]]]
 h' := ![![[608, 856], [175, 833], [526, 465], [283, 544], [464, 85], [817, 306], [814, 600], [538, 460], [512, 794], [0, 1]], ![[0, 1], [152, 24], [436, 392], [233, 313], [724, 772], [39, 551], [532, 257], [836, 397], [773, 63], [608, 856]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [747, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P857P1 : CertificateIrreducibleZModOfList' 857 3 2 9 [142, 769, 608, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [109, 524, 32], [140, 332, 825], [0, 1]]
 g := ![![[645, 789, 299], [614, 338], [458, 740], [593, 547, 418], [490, 352, 821], [767, 470], [200, 482, 133], [368, 297], [1]], ![[657, 691, 798, 651], [411, 53], [195, 345], [563, 671, 114, 72], [348, 630, 752, 439], [54, 194], [757, 30, 448, 848], [167, 378], [3, 35, 17, 202]], ![[668, 259, 199, 30], [508, 593], [143, 454], [126, 740, 19, 61], [579, 751, 515, 23], [174, 617], [348, 447, 436, 822], [217, 232], [11, 387, 339, 655]]]
 h' := ![![[109, 524, 32], [570, 806, 823], [504, 374, 452], [637, 222, 748], [694, 177, 596], [374, 415, 385], [738, 718, 224], [474, 355, 805], [715, 88, 249], [0, 1]], ![[140, 332, 825], [548, 490, 792], [781, 95, 59], [719, 111, 54], [712, 546, 427], [832, 698, 552], [780, 838, 503], [704, 486, 95], [533, 767, 641], [109, 524, 32]], ![[0, 1], [92, 418, 99], [343, 388, 346], [848, 524, 55], [140, 134, 691], [832, 601, 777], [49, 158, 130], [625, 16, 814], [38, 2, 824], [140, 332, 825]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [809, 24], []]
 b := ![[], [322, 783, 642], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A857 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 857 2 where
 D := ![[360, 249, 1], [142, 769, 608, 1]]; D' := ![[360, 249, 1], [142, 769, 608, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P857P0
  | 1 => exact P857P1

def C8570 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A857.D 0) 857 where
  n := 2
  w := ![![857, 0, 0, 0, 0], ![360, 249, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C8571 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A857.D 1) 857 where
  n := 3
  w := ![![857, 0, 0, 0, 0], ![142, 769, 608, 5, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K857 : KummerData 857 ![I857N0, I857N1] ![734449, 629422793] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A857
  C := by
    intro i
    match i with
    | 0 => exact C8570
    | 1 => exact C8571
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 857 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp859 : Fact (Nat.Prime 859) := {out := by norm_num}

def I859N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![859, 0, 0, 0, 0], ![156, 1, 0, 0, 0]] i)))

def I859N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![859, 0, 0, 0, 0], ![230, 1, 0, 0, 0]] i)))

def I859N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![859, 0, 0, 0, 0], ![418, 562, 473, 5, 0]] i)))

def P859P0 : CertificateIrreducibleZModOfList' 859 1 2 9 [156, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [435], [], [290], [361], [], [291], [], [284, 703, 1]]]
 h' := ![![[0, 1], [1], [764], [287], [378], [840], [131], [210], [364], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P859P1 : CertificateIrreducibleZModOfList' 859 1 2 9 [230, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [676], [], [666], [260], [], [524], [], [501, 629, 1]]]
 h' := ![![[0, 1], [858], [833], [581], [330], [598], [599], [773], [735], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P859P2 : CertificateIrreducibleZModOfList' 859 3 2 9 [418, 562, 473, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [733, 428, 281], [512, 430, 578], [0, 1]]
 g := ![![[736, 733, 46], [741, 352, 621], [344, 265], [186, 536, 343], [332, 532, 121], [756, 838], [857, 69, 231], [619, 389], [1]], ![[318, 309, 818, 700], [89, 758, 603, 317], [610, 682], [836, 136, 781, 210], [781, 107, 725, 688], [749, 390], [658, 385, 808, 471], [233, 413], [670, 536, 649, 71]], ![[526, 690, 25, 288], [684, 171, 655, 247], [650, 318], [115, 731, 31, 360], [669, 469, 586, 490], [821, 329], [418, 182, 424, 826], [732, 700], [497, 291, 411, 788]]]
 h' := ![![[733, 428, 281], [361, 53, 42], [807, 714, 541], [421, 311, 615], [382, 319, 585], [633, 537, 848], [836, 37, 468], [164, 584, 579], [441, 297, 386], [0, 1]], ![[512, 430, 578], [133, 498, 311], [429, 140, 328], [460, 44, 510], [328, 49, 166], [738, 117, 137], [798, 796, 323], [404, 428, 754], [209, 567, 327], [733, 428, 281]], ![[0, 1], [485, 308, 506], [273, 5, 849], [836, 504, 593], [258, 491, 108], [286, 205, 733], [173, 26, 68], [789, 706, 385], [828, 854, 146], [512, 430, 578]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [68, 287], []]
 b := ![[], [546, 706, 537], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A859 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 859 3 where
 D := ![[156, 1], [230, 1], [418, 562, 473, 1]]; D' := ![[156, 1], [230, 1], [418, 562, 473, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9, 9]
 n := ![1, 1, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P859P0
  | 1 => exact P859P1
  | 2 => exact P859P2

def C8590 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A859.D 0) 859 where
  n := 1
  w := ![![859, 0, 0, 0, 0], ![156, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C8591 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A859.D 1) 859 where
  n := 1
  w := ![![859, 0, 0, 0, 0], ![230, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C8592 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A859.D 2) 859 where
  n := 3
  w := ![![859, 0, 0, 0, 0], ![418, 562, 473, 5, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K859 : KummerData 859 ![I859N0, I859N1, I859N2] ![859, 859, 633839779] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A859
  C := by
    intro i
    match i with
    | 0 => exact C8590
    | 1 => exact C8591
    | 2 => exact C8592
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 859 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp863 : Fact (Nat.Prime 863) := {out := by norm_num}

def I863N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![863, 0, 0, 0, 0], ![432, 198, 1, 0, 0]] i)))

def I863N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![863, 0, 0, 0, 0], ![263, 775, 665, 5, 0]] i)))

def P863P0 : CertificateIrreducibleZModOfList' 863 2 2 9 [432, 198, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [665, 862], [0, 1]]
 g := ![![[396, 2], [151, 841], [718, 848], [264, 288], [648, 296], [36], [246, 269], [517], [665, 1]], ![[0, 861], [192, 22], [236, 15], [198, 575], [724, 567], [36], [490, 594], [517], [467, 862]]]
 h' := ![![[665, 862], [356, 612], [504, 834], [731, 780], [539, 423], [440, 389], [740, 857], [481, 802], [99, 800], [0, 1]], ![[0, 1], [0, 251], [205, 29], [768, 83], [496, 440], [225, 474], [202, 6], [477, 61], [491, 63], [665, 862]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [174]]
 b := ![[], [846, 87]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P863P1 : CertificateIrreducibleZModOfList' 863 3 2 9 [263, 775, 665, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [120, 90, 773], [78, 772, 90], [0, 1]]
 g := ![![[518, 106, 780], [144, 58, 779], [131, 647, 130], [689, 539, 830], [733, 444, 103], [253, 790], [530, 833, 210], [35, 369], [1]], ![[439, 727, 507, 762], [267, 410, 287, 697], [613, 155, 285, 154], [346, 718, 575, 655], [634, 803, 259, 744], [199, 593], [735, 234, 683, 420], [369, 578], [494, 364, 86, 235]], ![[248, 168, 391, 559], [439, 187, 137, 621], [540, 811, 833, 351], [218, 32, 217, 810], [366, 427, 357, 760], [129, 210], [115, 462, 123, 277], [230, 62], [197, 178, 641, 628]]]
 h' := ![![[120, 90, 773], [100, 181, 327], [67, 688, 766], [23, 159, 472], [533, 308, 181], [368, 828, 285], [416, 587, 544], [417, 414, 819], [600, 88, 198], [0, 1]], ![[78, 772, 90], [630, 513, 555], [636, 727, 413], [422, 175, 559], [671, 17, 685], [296, 494, 516], [266, 717, 363], [841, 730, 401], [665, 568, 815], [120, 90, 773]], ![[0, 1], [462, 169, 844], [9, 311, 547], [104, 529, 695], [369, 538, 860], [399, 404, 62], [758, 422, 819], [164, 582, 506], [734, 207, 713], [78, 772, 90]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [432, 105], []]
 b := ![[], [96, 598, 145], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A863 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 863 2 where
 D := ![[432, 198, 1], [263, 775, 665, 1]]; D' := ![[432, 198, 1], [263, 775, 665, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P863P0
  | 1 => exact P863P1

def C8630 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A863.D 0) 863 where
  n := 2
  w := ![![863, 0, 0, 0, 0], ![432, 198, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C8631 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A863.D 1) 863 where
  n := 3
  w := ![![863, 0, 0, 0, 0], ![263, 775, 665, 5, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K863 : KummerData 863 ![I863N0, I863N1] ![744769, 642735647] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A863
  C := by
    intro i
    match i with
    | 0 => exact C8630
    | 1 => exact C8631
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 863 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp877 : Fact (Nat.Prime 877) := {out := by norm_num}

def I877N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![877, 0, 0, 0, 0], ![494, 1, 0, 0, 0]] i)))

def I877N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![877, 0, 0, 0, 0], ![42, 462, 210, 1915, 10]] i)))

def P877P0 : CertificateIrreducibleZModOfList' 877 1 2 9 [494, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [698], [652], [], [780], [690], [], [230, 383, 1]]]
 h' := ![![[0, 1], [876], [726], [648], [511], [560], [293], [379], [390], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P877P1 : CertificateIrreducibleZModOfList' 877 4 2 9 [42, 462, 205, 383, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [97, 555, 485, 272], [26, 156, 99, 866], [371, 165, 293, 616], [0, 1]]
 g := ![![[645, 598, 796, 172], [742, 438, 290], [333, 870, 318, 733], [852, 619, 281, 855], [163, 720, 497], [372, 555, 311, 64], [37, 328, 447, 799], [25, 494, 1], []], ![[300, 647, 343, 705, 814, 781], [74, 524, 535], [308, 72, 607, 302, 475, 751], [347, 201, 45, 285, 693, 326], [466, 542, 347], [38, 575, 158, 35, 59, 612], [345, 558, 586, 495, 200, 451], [411, 411, 324], [475, 632, 426, 560, 565, 6]], ![[839, 265, 814, 613, 803, 138], [217, 699, 843], [856, 669, 720, 152, 93, 91], [71, 29, 383, 308, 757, 398], [698, 435, 467], [140, 311, 515, 330, 530, 204], [402, 43, 636, 679, 590, 434], [656, 623, 379], [389, 796, 65, 498, 216, 423]], ![[579, 686, 380, 495, 654, 813], [209, 644, 652], [250, 386, 185, 336, 863, 671], [34, 810, 344, 543, 465, 670], [108, 785, 385], [662, 233, 124, 766, 862, 65], [115, 573, 92, 119, 653, 23], [608, 638, 773], [10, 146, 696, 96, 197, 717]]]
 h' := ![![[97, 555, 485, 272], [770, 621, 395, 655], [46, 34, 612, 243], [173, 753, 117, 58], [104, 851, 776, 748], [162, 55, 516, 169], [200, 813, 510, 8], [704, 151, 764, 72], [0, 0, 0, 1], [0, 1]], ![[26, 156, 99, 866], [473, 256, 53, 289], [52, 644, 313, 677], [240, 454, 85, 86], [374, 60, 471, 74], [511, 868, 741, 280], [725, 41, 465, 437], [739, 794, 787, 368], [814, 577, 415, 859], [97, 555, 485, 272]], ![[371, 165, 293, 616], [485, 69, 716, 196], [506, 259, 433, 323], [455, 238, 547, 258], [596, 291, 229, 602], [473, 100, 833, 753], [613, 373, 182, 110], [160, 835, 394, 384], [361, 609, 870, 487], [26, 156, 99, 866]], ![[0, 1], [870, 808, 590, 614], [1, 817, 396, 511], [128, 309, 128, 475], [614, 552, 278, 330], [309, 731, 541, 552], [768, 527, 597, 322], [538, 851, 686, 53], [189, 568, 469, 407], [371, 165, 293, 616]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [177, 581, 77], []]
 b := ![[], [], [355, 310, 405, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A877 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 877 2 where
 D := ![[494, 1], [42, 462, 205, 383, 1]]; D' := ![[494, 1], [42, 462, 205, 383, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P877P0
  | 1 => exact P877P1

def C8770 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A877.D 0) 877 where
  n := 1
  w := ![![877, 0, 0, 0, 0], ![494, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C8771 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A877.D 1) 877 where
  n := 4
  w := ![![877, 0, 0, 0, 0], ![42, 462, 210, 1915, 10]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K877 : KummerData 877 ![I877N0, I877N1] ![877, 591559418641] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A877
  C := by
    intro i
    match i with
    | 0 => exact C8770
    | 1 => exact C8771
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 877 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp881 : Fact (Nat.Prime 881) := {out := by norm_num}

def I881N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![881, 0, 0, 0, 0], ![881, 0, 0, 4405, 0]] i)))

def P881P0 : CertificateIrreducibleZModOfList' 881 5 2 9 [581, 250, 0, 856, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [591, 660, 566, 663, 245], [131, 650, 668, 519, 410], [412, 878, 661, 393, 71], [628, 454, 748, 187, 155], [0, 1]]
 g := ![![[557, 624, 858, 432, 2], [614, 124, 719, 250], [168, 387, 107, 99], [567, 14, 828, 703], [557, 427, 705, 224, 443], [228, 365, 403, 836, 743], [233, 23, 482, 0, 625], [0, 1], []], ![[107, 686, 373, 222, 61, 365, 167, 563], [119, 402, 211, 241], [702, 550, 120, 658], [576, 824, 363, 72], [146, 463, 597, 696, 755, 560, 777, 168], [637, 148, 831, 539, 275, 164, 443, 640], [237, 648, 713, 729, 873, 382, 786, 673], [418, 854, 241, 664], [91, 792, 767, 227, 787, 184, 129, 473]], ![[538, 362, 276, 309, 589, 599, 387, 772], [373, 549, 649, 410], [262, 774, 867, 134], [466, 789, 379, 441], [656, 92, 296, 542, 452, 184, 766, 332], [493, 287, 511, 100, 324, 198, 809, 408], [500, 20, 554, 231, 106, 303, 778, 110], [572, 51, 311, 784], [562, 409, 735, 438, 325, 349, 696, 370]], ![[459, 520, 179, 503, 102, 73, 440, 533], [544, 635, 715, 618], [19, 791, 722, 542], [393, 584, 617, 872], [708, 94, 605, 802, 337, 161, 448, 380], [642, 551, 559, 555, 637, 508, 368, 607], [180, 531, 60, 509, 224, 628, 153, 51], [225, 813, 689, 784], [614, 536, 872, 48, 832, 151, 113, 225]], ![[481, 660, 780, 255, 216, 248, 727, 583], [235, 619, 467, 50], [317, 830, 356, 282], [69, 564, 117, 572], [70, 388, 1, 490, 806, 73, 40, 754], [197, 436, 776, 723, 433, 715, 251, 155], [245, 406, 355, 216, 614, 331, 851, 312], [549, 67, 579, 664], [831, 410, 533, 632, 835, 878, 487, 769]]]
 h' := ![![[591, 660, 566, 663, 245], [261, 114, 352, 750, 839], [74, 608, 495, 78, 575], [472, 120, 344, 577, 549], [591, 112, 261, 614, 434], [563, 379, 405, 67, 383], [301, 629, 533, 874, 192], [0, 300, 631, 0, 25], [0, 0, 0, 1], [0, 1]], ![[131, 650, 668, 519, 410], [373, 304, 202, 74, 21], [783, 435, 869, 749, 116], [530, 696, 676, 196, 270], [785, 644, 623, 415, 252], [355, 399, 787, 434, 346], [679, 708, 638, 365, 833], [428, 442, 651, 417, 682], [593, 76, 735, 136, 775], [591, 660, 566, 663, 245]], ![[412, 878, 661, 393, 71], [385, 530, 631, 525, 675], [720, 171, 809, 409, 605], [858, 575, 344, 433, 647], [16, 474, 391, 851, 860], [183, 74, 847, 262, 126], [288, 647, 795, 168, 87], [16, 174, 563, 313, 144], [108, 747, 554, 273, 28], [131, 650, 668, 519, 410]], ![[628, 454, 748, 187, 155], [299, 501, 783, 877, 12], [814, 449, 797, 9, 676], [20, 827, 555, 745, 833], [44, 46, 469, 289, 280], [569, 99, 638, 607, 442], [392, 362, 89, 423, 649], [864, 387, 172, 802, 170], [819, 210, 851, 381, 853], [412, 878, 661, 393, 71]], ![[0, 1], [39, 313, 675, 417, 215], [851, 99, 554, 517, 671], [755, 425, 724, 692, 344], [610, 486, 18, 474, 817], [853, 811, 847, 392, 465], [491, 297, 588, 813, 1], [371, 459, 626, 230, 741], [242, 729, 503, 90, 106], [628, 454, 748, 187, 155]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [567, 412, 219, 440], [], [], []]
 b := ![[], [419, 556, 59, 589, 178], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A881 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 881 1 where
 D := ![[581, 250, 0, 856, 0, 1]]; D' := ![[581, 250, 0, 856, 0, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9]
 n := ![5]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P881P0

def C8810 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A881.D 0) 881 where
  n := 5
  w := ![![881, 0, 0, 0, 0], ![881, 0, 0, 4405, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K881 : KummerData 881 ![I881N0] ![530737216068401] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A881
  C := by
    intro i
    match i with
    | 0 => exact C8810
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 881 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp883 : Fact (Nat.Prime 883) := {out := by norm_num}

def I883N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![883, 0, 0, 0, 0], ![3, 641, 1, 0, 0]] i)))

def I883N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![883, 0, 0, 0, 0], ![783, 258, 242, 5, 0]] i)))

def P883P0 : CertificateIrreducibleZModOfList' 883 2 2 9 [3, 641, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [242, 882], [0, 1]]
 g := ![![[508, 473], [71, 860], [123], [111], [110, 36], [288, 857], [95, 690], [619], [242, 1]], ![[184, 410], [686, 23], [123], [111], [875, 847], [177, 26], [188, 193], [619], [484, 882]]]
 h' := ![![[242, 882], [670, 367], [512, 303], [841, 130], [553, 383], [19, 6], [598, 794], [717, 250], [157, 283], [0, 1]], ![[0, 1], [301, 516], [549, 580], [513, 753], [524, 500], [588, 877], [252, 89], [290, 633], [652, 600], [242, 882]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [116]]
 b := ![[], [46, 58]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P883P1 : CertificateIrreducibleZModOfList' 883 3 2 9 [783, 258, 242, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [799, 646, 257], [725, 236, 626], [0, 1]]
 g := ![![[423, 535, 838], [253, 463, 686], [380, 824], [115, 116], [652, 105, 174], [434, 249, 734], [523, 802, 293], [31, 286], [1]], ![[62, 405, 286, 503], [692, 596, 452, 190], [754, 878], [766, 278], [410, 11, 419, 722], [715, 18, 624, 292], [42, 520, 529, 110], [426, 186], [414, 831, 226, 684]], ![[165, 836, 550, 472], [583, 529, 204, 261], [236, 293], [714, 327], [869, 299, 513, 738], [807, 772, 590, 671], [553, 436, 545, 860], [749, 717], [541, 56, 302, 199]]]
 h' := ![![[799, 646, 257], [576, 94, 269], [396, 250, 642], [759, 470, 66], [741, 370, 266], [133, 53, 140], [203, 728, 50], [738, 790, 450], [100, 625, 641], [0, 1]], ![[725, 236, 626], [502, 726, 225], [247, 93, 310], [294, 27, 384], [554, 127, 692], [415, 58, 745], [155, 813, 221], [430, 729, 180], [571, 519, 202], [799, 646, 257]], ![[0, 1], [800, 63, 389], [773, 540, 814], [339, 386, 433], [318, 386, 808], [741, 772, 881], [654, 225, 612], [405, 247, 253], [286, 622, 40], [725, 236, 626]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [139, 697], []]
 b := ![[], [707, 243, 200], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A883 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 883 2 where
 D := ![[3, 641, 1], [783, 258, 242, 1]]; D' := ![[3, 641, 1], [783, 258, 242, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P883P0
  | 1 => exact P883P1

def C8830 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A883.D 0) 883 where
  n := 2
  w := ![![883, 0, 0, 0, 0], ![3, 641, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C8831 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A883.D 1) 883 where
  n := 3
  w := ![![883, 0, 0, 0, 0], ![783, 258, 242, 5, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K883 : KummerData 883 ![I883N0, I883N1] ![779689, 688465387] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A883
  C := by
    intro i
    match i with
    | 0 => exact C8830
    | 1 => exact C8831
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 883 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


lemma PB1045I16_primes (p : ℕ) :
  p ∈ Set.range ![829, 839, 853, 857, 859, 863, 877, 881, 883] ↔ Nat.Prime p ∧ 827 < p ∧ p ≤ 883 := by
  rw [← List.mem_ofFn']
  convert primes_range 827 883 (by omega)
  decide

def PB1045I16 : PrimesBelowBoundCertificateInterval O 827 883 1045 where
  m := 9
  g := ![3, 3, 2, 2, 3, 2, 2, 1, 2]
  P := ![829, 839, 853, 857, 859, 863, 877, 881, 883]
  hP := PB1045I16_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I829N0, I829N1, I829N2]
    · exact ![I839N0, I839N1, I839N2]
    · exact ![I853N0, I853N1]
    · exact ![I857N0, I857N1]
    · exact ![I859N0, I859N1, I859N2]
    · exact ![I863N0, I863N1]
    · exact ![I877N0, I877N1]
    · exact ![I881N0]
    · exact ![I883N0, I883N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · convert (containsPrimesAbove_of_KummerData K829) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K839) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K853) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K857) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K859) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K863) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K877) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K881) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K883) <;> rfl
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![829, 687241, 687241]
    · exact ![839, 839, 590589719]
    · exact ![853, 529414856881]
    · exact ![734449, 629422793]
    · exact ![859, 859, 633839779]
    · exact ![744769, 642735647]
    · exact ![877, 591559418641]
    · exact ![530737216068401]
    · exact ![779689, 688465387]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact (card_quot_of_KummerData K829)
    · exact (card_quot_of_KummerData K839)
    · exact (card_quot_of_KummerData K853)
    · exact (card_quot_of_KummerData K857)
    · exact (card_quot_of_KummerData K859)
    · exact (card_quot_of_KummerData K863)
    · exact (card_quot_of_KummerData K877)
    · exact (card_quot_of_KummerData K881)
    · exact (card_quot_of_KummerData K883)
  β := ![I829N0, I839N0, I839N1, I853N0, I859N0, I859N1, I877N0]
  Il := ![[I829N0], [I839N0, I839N1], [I853N0], [], [I859N0, I859N1], [], [I877N0], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
