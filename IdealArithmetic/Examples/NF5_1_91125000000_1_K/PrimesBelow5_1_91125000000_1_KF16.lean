
import IdealArithmetic.Examples.NF5_1_91125000000_1_K.RI5_1_91125000000_1_K
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 

instance hp829 : Fact (Nat.Prime 829) := {out := by norm_num}

def I829N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![829, 0, 0, 0, 0], ![742, 1, 0, 0, 0]] i)))

def I829N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![829, 0, 0, 0, 0], ![791, 1, 0, 0, 0]] i)))

def I829N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![829, 0, 0, 0, 0], ![743, 714, 125, 2, 0]] i)))

def P829P0 : CertificateIrreducibleZModOfList' 829 1 2 9 [742, 1] where
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
 g := ![![[], [], [60], [340], [320], [335], [], [], [108, 87, 1]]]
 h' := ![![[0, 1], [828], [246], [565], [483], [130], [297], [461], [277], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P829P1 : CertificateIrreducibleZModOfList' 829 1 2 9 [791, 1] where
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
 g := ![![[], [], [240], [712], [207], [505], [], [], [615, 38, 1]]]
 h' := ![![[0, 1], [1], [1], [528], [405], [123], [546], [94], [158], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P829P2 : CertificateIrreducibleZModOfList' 829 3 2 9 [743, 713, 125, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [391, 97, 501], [313, 731, 328], [0, 1]]
 g := ![![[554, 219, 661], [339, 715], [97, 118, 492], [794, 721, 178], [347, 736, 778], [141, 307, 593], [23, 205], [14, 703], [1]], ![[190, 68, 654, 341], [667, 586], [464, 505, 332, 445], [692, 242, 421, 536], [298, 56, 274, 366], [245, 427, 783, 513], [241, 232], [815, 682], [818, 10, 559, 491]], ![[372, 39, 681, 631], [533, 425], [117, 617, 654, 98], [581, 58, 422, 10], [338, 710, 95, 139], [819, 614, 51, 496], [699, 197], [751, 436], [228, 371, 828, 338]]]
 h' := ![![[391, 97, 501], [356, 121, 726], [52, 634, 718], [306, 749, 247], [827, 69, 617], [520, 524, 402], [256, 674, 744], [310, 792, 460], [86, 116, 704], [0, 1]], ![[313, 731, 328], [730, 363, 250], [657, 233, 228], [398, 529, 376], [37, 619, 631], [124, 593, 127], [300, 666, 311], [392, 534, 216], [480, 499, 730], [391, 97, 501]], ![[0, 1], [467, 345, 682], [450, 791, 712], [749, 380, 206], [364, 141, 410], [411, 541, 300], [629, 318, 603], [557, 332, 153], [128, 214, 224], [313, 731, 328]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [449, 331], []]
 b := ![[], [103, 168, 691], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A829 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 829 3 where
 D := ![[742, 1], [791, 1], [743, 713, 125, 1]]; D' := ![[742, 1], [791, 1], [743, 713, 125, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9, 9]
 n := ![1, 1, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P829P0
  | 1 => exact P829P1
  | 2 => exact P829P2

def C8290 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A829.D 0) 829 where
  n := 1
  w := ![![829, 0, 0, 0, 0], ![742, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C8291 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A829.D 1) 829 where
  n := 1
  w := ![![829, 0, 0, 0, 0], ![791, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C8292 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A829.D 2) 829 where
  n := 3
  w := ![![829, 0, 0, 0, 0], ![743, 714, 125, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K829 : KummerData 829 ![I829N0, I829N1, I829N2] ![829, 829, 569722789] where
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

def I839N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![839, 0, 0, 0, 0], ![2, 1, 0, 0, 0]] i)))

def I839N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![839, 0, 0, 0, 0], ![742, 1, 0, 0, 0]] i)))

def I839N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![839, 0, 0, 0, 0], ![600, 830, 95, 2, 0]] i)))

def P839P0 : CertificateIrreducibleZModOfList' 839 1 2 9 [2, 1] where
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
 g := ![![[], [420], [622], [], [], [], [740], [], [4, 837, 1]]]
 h' := ![![[0, 1], [838], [434], [222], [423], [610], [198], [64], [831], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P839P1 : CertificateIrreducibleZModOfList' 839 1 2 9 [742, 1] where
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
 g := ![![[], [666], [75], [], [], [], [575], [], [180, 97, 1]]]
 h' := ![![[0, 1], [838], [563], [634], [147], [552], [401], [111], [680], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P839P2 : CertificateIrreducibleZModOfList' 839 3 2 9 [600, 829, 95, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [124, 803, 126], [620, 35, 713], [0, 1]]
 g := ![![[162, 636, 456], [451, 354, 674], [690, 373, 674], [447, 742], [521, 756], [635, 530], [584, 438, 752], [700, 635], [1]], ![[360, 805, 268, 686], [410, 593, 578, 141], [239, 220, 541, 414], [562, 75], [611, 672], [280, 541], [183, 469, 624, 211], [78, 427], [410, 801, 605, 200]], ![[494, 797, 186, 340], [516, 321, 152, 176], [352, 255, 407, 299], [12, 95], [493, 722], [143, 303], [670, 367, 819, 17], [443, 760], [667, 28, 429, 639]]]
 h' := ![![[124, 803, 126], [397, 37, 594], [466, 411, 309], [329, 111, 309], [7, 146, 763], [498, 46, 686], [302, 116, 802], [408, 779, 254], [239, 10, 744], [0, 1]], ![[620, 35, 713], [561, 514, 282], [509, 190, 515], [88, 83, 470], [510, 765, 634], [299, 55, 441], [498, 356, 736], [503, 164, 491], [243, 664, 452], [124, 803, 126]], ![[0, 1], [687, 288, 802], [168, 238, 15], [289, 645, 60], [457, 767, 281], [148, 738, 551], [89, 367, 140], [388, 735, 94], [824, 165, 482], [620, 35, 713]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [423, 477], []]
 b := ![[], [477, 541, 176], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A839 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 839 3 where
 D := ![[2, 1], [742, 1], [600, 829, 95, 1]]; D' := ![[2, 1], [742, 1], [600, 829, 95, 1]]
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
  w := ![![839, 0, 0, 0, 0], ![2, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C8391 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A839.D 1) 839 where
  n := 1
  w := ![![839, 0, 0, 0, 0], ![742, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C8392 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A839.D 2) 839 where
  n := 3
  w := ![![839, 0, 0, 0, 0], ![600, 830, 95, 2, 0]]
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

def I853N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![853, 0, 0, 0, 0], ![563, 1, 0, 0, 0]] i)))

def I853N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![853, 0, 0, 0, 0], ![1114, 3169, 11401, -2458, 22728]] i)))

def P853P0 : CertificateIrreducibleZModOfList' 853 1 2 9 [563, 1] where
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
 g := ![![[], [], [443], [], [553], [], [812], [], [506, 290, 1]]]
 h' := ![![[0, 1], [852], [520], [36], [6], [145], [52], [576], [24], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P853P1 : CertificateIrreducibleZModOfList' 853 4 2 9 [466, 777, 506, 290, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [171, 674, 227, 342], [293, 388, 300, 291], [99, 643, 326, 220], [0, 1]]
 g := ![![[298, 169, 343, 445], [370, 97, 675], [729, 723, 342, 183], [434, 747, 516], [652, 204, 396, 119], [53, 822, 632], [460, 342, 281, 617], [0, 563, 1], []], ![[153, 779, 484, 328, 568, 573], [810, 227, 315], [300, 809, 729, 544, 109, 791], [206, 632, 819], [371, 114, 692, 434, 493, 2], [162, 96, 34], [104, 745, 136, 375, 843, 386], [334, 752, 296], [377, 660, 264, 822, 185, 253]], ![[680, 633, 83, 428, 378, 24], [315, 804, 174], [33, 618, 344, 331, 353, 182], [524, 625, 123], [3, 137, 175, 605, 600, 247], [187, 573, 271], [753, 713, 42, 172, 744, 711], [5, 789, 770], [92, 184, 118, 386, 452, 707]], ![[738, 52, 56, 419, 192, 300], [393, 221, 531], [22, 132, 614, 142, 460, 570], [461, 181, 619], [461, 36, 601, 805, 311, 364], [288, 689, 787], [22, 797, 369, 144, 716, 412], [323, 111, 751], [755, 690, 517, 35, 234, 1]]]
 h' := ![![[171, 674, 227, 342], [518, 603, 388, 513], [633, 396, 492, 349], [370, 744, 206, 552], [689, 717, 423, 816], [407, 625, 472, 93], [596, 126, 74, 633], [0, 366, 525, 100], [0, 0, 0, 1], [0, 1]], ![[293, 388, 300, 291], [663, 573, 111, 806], [764, 79, 119, 245], [740, 373, 381, 626], [181, 326, 778, 198], [702, 160, 727, 80], [315, 420, 313, 253], [270, 656, 396, 393], [814, 483, 363, 507], [171, 674, 227, 342]], ![[99, 643, 326, 220], [703, 343, 574, 96], [280, 141, 330, 636], [611, 434, 606, 338], [374, 729, 804, 178], [338, 252, 189, 642], [569, 2, 608, 728], [312, 306, 70, 8], [271, 716, 243, 175], [293, 388, 300, 291]], ![[0, 1], [35, 187, 633, 291], [376, 237, 765, 476], [156, 155, 513, 190], [97, 787, 554, 514], [706, 669, 318, 38], [121, 305, 711, 92], [693, 378, 715, 352], [44, 507, 247, 170], [99, 643, 326, 220]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [662, 121, 511], []]
 b := ![[], [], [723, 183, 651, 819], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A853 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 853 2 where
 D := ![[563, 1], [466, 777, 506, 290, 1]]; D' := ![[563, 1], [466, 777, 506, 290, 1]]
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
  w := ![![853, 0, 0, 0, 0], ![563, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C8531 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A853.D 1) 853 where
  n := 4
  w := ![![853, 0, 0, 0, 0], ![1114, 3169, 11401, -2458, 22728]]
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

def I857N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![857, 0, 0, 0, 0], ![136, 1, 0, 0, 0]] i)))

def I857N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![857, 0, 0, 0, 0], ![438, 1, 0, 0, 0]] i)))

def I857N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![857, 0, 0, 0, 0], ![775, 1, 0, 0, 0]] i)))

def I857N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![857, 0, 0, 0, 0], ![745, 365, 1, 0, 0]] i)))

def P857P0 : CertificateIrreducibleZModOfList' 857 1 2 9 [136, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [513], [263], [], [814], [], [499, 721, 1]]]
 h' := ![![[0, 1], [856], [650], [506], [226], [519], [706], [211], [696], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P857P1 : CertificateIrreducibleZModOfList' 857 1 2 9 [438, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [110], [780], [], [122], [], [733, 419, 1]]]
 h' := ![![[0, 1], [856], [207], [669], [303], [362], [555], [201], [321], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P857P2 : CertificateIrreducibleZModOfList' 857 1 2 9 [775, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [324], [690], [], [408], [], [725, 82, 1]]]
 h' := ![![[0, 1], [1], [1], [1], [18], [232], [33], [220], [317], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P857P3 : CertificateIrreducibleZModOfList' 857 2 2 9 [745, 365, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [492, 856], [0, 1]]
 g := ![![[35, 771], [9], [529], [745, 842], [575, 645], [293], [459, 517], [46], [492, 1]], ![[573, 86], [9], [529], [221, 15], [825, 212], [293], [294, 340], [46], [127, 856]]]
 h' := ![![[492, 856], [176, 113], [852, 3], [311, 834], [125, 461], [394, 430], [845, 61], [414, 274], [256, 502], [0, 1]], ![[0, 1], [67, 744], [614, 854], [136, 23], [689, 396], [275, 427], [5, 796], [673, 583], [424, 355], [492, 856]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [767]]
 b := ![[], [786, 812]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A857 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 857 4 where
 D := ![[136, 1], [438, 1], [775, 1], [745, 365, 1]]; D' := ![[136, 1], [438, 1], [775, 1], [745, 365, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9, 9, 9]
 n := ![1, 1, 1, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P857P0
  | 1 => exact P857P1
  | 2 => exact P857P2
  | 3 => exact P857P3

def C8570 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A857.D 0) 857 where
  n := 1
  w := ![![857, 0, 0, 0, 0], ![136, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C8571 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A857.D 1) 857 where
  n := 1
  w := ![![857, 0, 0, 0, 0], ![438, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C8572 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A857.D 2) 857 where
  n := 1
  w := ![![857, 0, 0, 0, 0], ![775, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C8573 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A857.D 3) 857 where
  n := 2
  w := ![![857, 0, 0, 0, 0], ![745, 365, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K857 : KummerData 857 ![I857N0, I857N1, I857N2, I857N3] ![857, 857, 857, 734449] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A857
  C := by
    intro i
    match i with
    | 0 => exact C8570
    | 1 => exact C8571
    | 2 => exact C8572
    | 3 => exact C8573
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 857 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp859 : Fact (Nat.Prime 859) := {out := by norm_num}

def I859N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![859, 0, 0, 0, 0], ![16321, 859, 859, 0, 0]] i)))

def P859P0 : CertificateIrreducibleZModOfList' 859 5 2 9 [601, 334, 759, 0, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [597, 245, 159, 483, 672], [763, 117, 422, 382, 142], [782, 470, 846, 26, 563], [435, 26, 291, 827, 341], [0, 1]]
 g := ![![[272, 337, 695, 312, 662], [846, 706, 152, 557, 731], [802, 449, 350, 370], [574, 524, 827, 732, 406], [331, 252, 408, 487, 503], [665, 499, 438, 305], [805, 202, 551], [0, 1], []], ![[787, 445, 831, 430, 698, 338, 277, 154], [124, 463, 426, 214, 242, 759, 785, 423], [59, 754, 434, 36], [193, 107, 70, 92, 250, 384, 722, 799], [380, 681, 61, 704, 728, 398, 535, 125], [87, 81, 234, 510], [305, 594, 299, 5, 294, 608, 276, 683], [69, 634, 83, 856], [751, 852, 788, 410, 575, 544, 248, 364]], ![[211, 327, 779, 363, 549, 280, 76, 39], [204, 547, 115, 108, 481, 450, 536, 794], [473, 843, 793, 325], [169, 408, 156, 108, 736, 648, 819, 141], [159, 116, 190, 785, 333, 379, 553, 372], [158, 692, 234, 401], [50, 655, 533, 183, 298, 0, 211, 813], [480, 612, 670, 659], [503, 94, 54, 44, 490, 233, 844, 241]], ![[377, 62, 152, 82, 454, 164, 434, 104], [31, 309, 480, 286, 298, 838, 6, 341], [280, 495, 126, 152], [466, 647, 607, 333, 385, 639, 75, 434], [814, 160, 789, 669, 435, 180, 521, 331], [607, 853, 199, 260], [612, 668, 598, 3, 290, 21, 848, 582], [669, 765, 148, 119], [785, 762, 36, 599, 788, 231, 703, 592]], ![[89, 418, 664, 8, 677, 30, 341, 388], [65, 449, 49, 675, 585, 586, 623, 459], [336, 591, 253, 364], [658, 443, 493, 429, 845, 299, 354, 104], [583, 640, 505, 510, 173, 656, 374, 138], [278, 285, 462, 753], [33, 488, 715, 758, 688, 23, 349, 241], [151, 626, 417, 457], [340, 822, 4, 556, 183, 560, 588, 381]]]
 h' := ![![[597, 245, 159, 483, 672], [82, 219, 262, 4, 39], [550, 63, 720, 213, 209], [344, 487, 252, 215, 700], [357, 706, 375, 795, 558], [754, 424, 574, 594, 555], [671, 573, 570, 656, 439], [0, 258, 525, 100], [0, 0, 0, 1], [0, 1]], ![[763, 117, 422, 382, 142], [312, 187, 128, 362, 335], [855, 145, 560, 456, 736], [186, 812, 612, 752, 6], [557, 139, 392, 458, 33], [691, 30, 87, 9, 154], [130, 461, 105, 630, 37], [500, 708, 173, 161, 31], [638, 740, 600, 667, 521], [597, 245, 159, 483, 672]], ![[782, 470, 846, 26, 563], [488, 489, 769, 392, 543], [839, 434, 82, 646, 578], [262, 402, 250, 494, 419], [719, 664, 8, 339, 700], [92, 616, 6, 597, 233], [684, 549, 735, 83, 167], [496, 593, 50, 318, 344], [99, 384, 231, 196, 383], [763, 117, 422, 382, 142]], ![[435, 26, 291, 827, 341], [794, 420, 359, 262, 794], [29, 841, 624, 118, 594], [117, 588, 45, 89, 242], [560, 283, 136, 54, 330], [550, 412, 486, 496, 5], [752, 55, 605, 100, 598], [203, 211, 597, 783, 673], [261, 651, 761, 104, 678], [782, 470, 846, 26, 563]], ![[0, 1], [229, 403, 200, 698, 7], [762, 235, 591, 285, 460], [278, 288, 559, 168, 351], [273, 785, 807, 72, 97], [189, 236, 565, 22, 771], [541, 80, 562, 249, 477], [454, 807, 373, 356, 670], [161, 802, 126, 750, 136], [435, 26, 291, 827, 341]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [160, 649, 158, 822], [], [], []]
 b := ![[], [508, 556, 545, 211, 574], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A859 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 859 1 where
 D := ![[601, 334, 759, 0, 0, 1]]; D' := ![[601, 334, 759, 0, 0, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9]
 n := ![5]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P859P0

def C8590 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A859.D 0) 859 where
  n := 5
  w := ![![859, 0, 0, 0, 0], ![16321, 859, 859, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K859 : KummerData 859 ![I859N0] ![467698329968299] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A859
  C := by
    intro i
    match i with
    | 0 => exact C8590
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 859 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp863 : Fact (Nat.Prime 863) := {out := by norm_num}

def I863N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![863, 0, 0, 0, 0], ![461, 1, 0, 0, 0]] i)))

def I863N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![863, 0, 0, 0, 0], ![1022, 3161, 11118, -2234, 22728]] i)))

def P863P0 : CertificateIrreducibleZModOfList' 863 1 2 9 [461, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [629], [214], [121], [848], [], [289], [], [223, 402, 1]]]
 h' := ![![[0, 1], [862], [591], [314], [11], [780], [536], [17], [757], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P863P1 : CertificateIrreducibleZModOfList' 863 4 2 9 [374, 657, 223, 402, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [669, 36, 676, 4], [741, 459, 315, 345], [777, 367, 735, 514], [0, 1]]
 g := ![![[642, 848, 630, 796], [455, 796, 624, 646], [60, 27, 462, 284], [311, 666, 552, 108], [653, 136, 616, 483], [717, 551, 294], [755, 612, 431, 507], [0, 461, 1], []], ![[133, 230, 659, 751, 37, 165], [380, 21, 428, 689, 371, 514], [578, 142, 72, 670, 704, 365], [647, 828, 773, 242, 450, 639], [666, 110, 756, 274, 269, 779], [449, 751, 280], [607, 783, 845, 450, 832, 696], [358, 663, 489], [571, 772, 314, 361, 679, 64]], ![[584, 816, 335, 424, 335, 732], [758, 452, 28, 63, 543, 256], [599, 367, 604, 268, 541, 453], [592, 679, 247, 51, 630, 507], [850, 513, 319, 296, 809, 527], [714, 238, 433], [54, 62, 842, 56, 0, 76], [328, 307, 784], [746, 233, 509, 440, 186, 359]], ![[598, 275, 535, 358, 839, 658], [592, 453, 20, 611, 679, 289], [532, 549, 735, 194, 279, 365], [766, 458, 423, 703, 504, 315], [95, 805, 763, 816, 202, 707], [56, 130, 114], [805, 465, 438, 366, 331, 636], [457, 680, 655], [95, 180, 809, 354, 662, 242]]]
 h' := ![![[669, 36, 676, 4], [704, 561, 377, 368], [861, 771, 591, 137], [191, 576, 559, 348], [7, 324, 787, 710], [317, 463, 829, 816], [694, 860, 181, 359], [0, 186, 525, 100], [0, 0, 0, 1], [0, 1]], ![[741, 459, 315, 345], [404, 19, 277, 230], [129, 534, 854, 477], [145, 83, 298, 310], [584, 319, 105, 261], [812, 374, 166, 480], [296, 555, 209, 748], [777, 718, 224, 796], [66, 593, 52, 378], [669, 36, 676, 4]], ![[777, 367, 735, 514], [628, 37, 464, 512], [437, 79, 310, 69], [588, 775, 338, 18], [466, 623, 96, 216], [158, 804, 48, 350], [194, 146, 264, 827], [529, 460, 574, 816], [512, 827, 238, 835], [741, 459, 315, 345]], ![[0, 1], [550, 246, 608, 616], [802, 342, 834, 180], [669, 292, 531, 187], [468, 460, 738, 539], [845, 85, 683, 80], [314, 165, 209, 655], [198, 362, 403, 14], [691, 306, 573, 512], [777, 367, 735, 514]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [611, 362, 859], []]
 b := ![[], [], [621, 75, 242, 843], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A863 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 863 2 where
 D := ![[461, 1], [374, 657, 223, 402, 1]]; D' := ![[461, 1], [374, 657, 223, 402, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P863P0
  | 1 => exact P863P1

def C8630 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A863.D 0) 863 where
  n := 1
  w := ![![863, 0, 0, 0, 0], ![461, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C8631 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A863.D 1) 863 where
  n := 4
  w := ![![863, 0, 0, 0, 0], ![1022, 3161, 11118, -2234, 22728]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K863 : KummerData 863 ![I863N0, I863N1] ![863, 554680863361] where
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

def I877N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![877, 0, 0, 0, 0], ![32, 1, 0, 0, 0]] i)))

def I877N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![877, 0, 0, 0, 0], ![1253, 3405, 11042, -1348, 22728]] i)))

def P877P0 : CertificateIrreducibleZModOfList' 877 1 2 9 [32, 1] where
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
 g := ![![[], [], [361], [849], [], [203], [841], [], [147, 845, 1]]]
 h' := ![![[0, 1], [876], [726], [19], [284], [520], [275], [29], [558], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P877P1 : CertificateIrreducibleZModOfList' 877 4 2 9 [605, 458, 147, 845, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [109, 742, 783, 827], [329, 445, 628, 389], [471, 566, 343, 538], [0, 1]]
 g := ![![[771, 655, 334, 750], [645, 619, 712], [817, 186, 357, 225], [93, 238, 334, 432], [799, 664, 592], [280, 41, 396, 541], [528, 415, 532, 353], [0, 32, 1], []], ![[670, 92, 850, 169, 91, 188], [214, 672, 415], [505, 396, 145, 570, 477, 11], [317, 429, 479, 518, 707, 246], [439, 167, 212], [594, 667, 631, 424, 363, 403], [632, 129, 257, 7, 33, 805], [847, 666, 766], [142, 828, 571, 130, 105, 411]], ![[759, 861, 601, 530, 544, 152], [226, 254, 790], [2, 184, 178, 792, 169, 516], [612, 220, 370, 6, 784, 839], [622, 678, 488], [800, 570, 617, 780, 294, 160], [592, 261, 564, 139, 65, 621], [587, 705, 586], [768, 209, 323, 675, 149, 506]], ![[369, 693, 392, 410, 651, 545], [63, 855, 876], [658, 625, 812, 767, 450, 173], [175, 324, 434, 143, 112, 719], [46, 686, 149], [186, 215, 749, 106, 758, 200], [214, 678, 448, 614, 40, 337], [596, 141, 247], [827, 688, 537, 427, 291, 752]]]
 h' := ![![[109, 742, 783, 827], [171, 299, 132, 794], [343, 371, 396, 106], [740, 804, 35, 15], [736, 509, 244, 321], [738, 647, 492, 616], [665, 852, 675, 285], [0, 811, 525, 100], [0, 0, 0, 1], [0, 1]], ![[329, 445, 628, 389], [364, 213, 205, 449], [712, 716, 758, 193], [427, 844, 824, 276], [426, 646, 199, 471], [243, 253, 273, 844], [283, 554, 231, 26], [146, 404, 189, 352], [613, 860, 832, 187], [109, 742, 783, 827]], ![[471, 566, 343, 538], [73, 528, 651, 413], [453, 691, 478, 427], [133, 268, 507, 452], [621, 631, 496, 48], [229, 192, 68, 161], [420, 107, 286, 577], [59, 240, 188, 681], [874, 852, 830, 164], [329, 445, 628, 389]], ![[0, 1], [253, 714, 766, 98], [721, 853, 122, 151], [833, 715, 388, 134], [495, 845, 815, 37], [797, 662, 44, 133], [506, 241, 562, 866], [825, 299, 852, 621], [9, 42, 92, 525], [471, 566, 343, 538]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [319, 142, 218], []]
 b := ![[], [], [445, 227, 225, 155], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A877 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 877 2 where
 D := ![[32, 1], [605, 458, 147, 845, 1]]; D' := ![[32, 1], [605, 458, 147, 845, 1]]
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
  w := ![![877, 0, 0, 0, 0], ![32, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C8771 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A877.D 1) 877 where
  n := 4
  w := ![![877, 0, 0, 0, 0], ![1253, 3405, 11042, -1348, 22728]]
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

def I881N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![881, 0, 0, 0, 0], ![15858, 881, 881, 0, 0]] i)))

def P881P0 : CertificateIrreducibleZModOfList' 881 5 2 9 [138, 356, 781, 0, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 76, 318, 369, 6], [519, 30, 308, 65, 323], [790, 771, 90, 222, 323], [445, 3, 165, 225, 229], [0, 1]]
 g := ![![[217, 446, 575, 3, 691], [585, 724, 751, 830], [578, 568, 467, 839], [23, 530, 519, 119], [729, 82, 564, 558, 795], [409, 534, 785, 70, 742], [464, 161, 309], [0, 1], []], ![[260, 328, 468, 693, 105, 116, 86, 379], [821, 770, 35, 485], [749, 120, 134, 512], [741, 580, 608, 26], [742, 535, 461, 511, 856, 124, 457, 731], [655, 164, 366, 354, 573, 219, 784, 854], [340, 506, 597, 111, 174, 241, 375, 789], [325, 814, 63, 139], [254, 708, 49, 526, 631, 822, 207, 216]], ![[26, 226, 10, 316, 195, 733, 339, 337], [490, 245, 621, 739], [575, 152, 43, 180], [637, 106, 229, 871], [47, 467, 620, 90, 720, 297, 52, 609], [879, 736, 281, 471, 794, 508, 252, 867], [46, 423, 693, 560, 561, 578, 474, 454], [402, 55, 524, 656], [188, 543, 474, 791, 4, 113, 103, 17]], ![[367, 585, 817, 864, 466, 608, 801, 502], [13, 659, 452, 662], [55, 139, 80, 607], [697, 327, 639, 561], [806, 155, 581, 336, 740, 790, 550, 417], [631, 333, 652, 276, 748, 581, 763, 350], [668, 137, 161, 67, 127, 866, 343, 323], [48, 108, 111, 45], [13, 536, 73, 827, 285, 446, 406, 17]], ![[474, 661, 434, 709, 341, 286, 722, 727], [241, 745, 195, 503], [433, 323, 575, 49], [577, 143, 694, 174], [625, 338, 710, 181, 508, 162, 358, 646], [297, 470, 550, 69, 246, 665, 584, 374], [309, 648, 790, 12, 309, 27, 691, 582], [368, 54, 123, 102], [345, 399, 447, 650, 531, 649, 857, 78]]]
 h' := ![![[8, 76, 318, 369, 6], [499, 339, 182, 641, 446], [85, 514, 239, 405, 250], [382, 850, 337, 566, 51], [713, 348, 858, 76, 612], [823, 625, 701, 607, 716], [281, 251, 183, 25, 530], [0, 743, 525, 100], [0, 0, 0, 1], [0, 1]], ![[519, 30, 308, 65, 323], [359, 24, 271, 632, 112], [84, 65, 435, 17, 597], [169, 408, 232, 143, 672], [477, 721, 274, 828, 94], [36, 27, 334, 867, 708], [709, 442, 237, 862, 594], [245, 474, 125, 30, 817], [700, 21, 629, 543, 718], [8, 76, 318, 369, 6]], ![[790, 771, 90, 222, 323], [710, 171, 854, 556, 229], [825, 318, 544, 623, 301], [879, 326, 688, 692, 487], [749, 813, 681, 144, 426], [584, 115, 776, 754, 404], [240, 138, 851, 747, 299], [36, 782, 17, 870, 343], [3, 873, 238, 817, 519], [519, 30, 308, 65, 323]], ![[445, 3, 165, 225, 229], [187, 762, 310, 614, 803], [813, 665, 123, 709, 767], [117, 737, 196, 465, 559], [393, 12, 629, 822, 674], [393, 47, 563, 630, 483], [119, 260, 290, 476, 252], [831, 121, 31, 828, 1], [533, 826, 739, 566, 197], [790, 771, 90, 222, 323]], ![[0, 1], [198, 466, 145, 200, 172], [226, 200, 421, 8, 728], [629, 322, 309, 777, 874], [67, 749, 201, 773, 837], [864, 67, 269, 666, 332], [805, 671, 201, 533, 87], [696, 523, 183, 815, 601], [826, 42, 156, 716, 328], [445, 3, 165, 225, 229]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [856, 400, 111, 373], [], [], []]
 b := ![[], [101, 644, 315, 501, 672], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A881 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 881 1 where
 D := ![[138, 356, 781, 0, 0, 1]]; D' := ![[138, 356, 781, 0, 0, 1]]
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
  w := ![![881, 0, 0, 0, 0], ![15858, 881, 881, 0, 0]]
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

def I883N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![883, 0, 0, 0, 0], ![537, 491, 1, 0, 0]] i)))

def I883N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![883, 0, 0, 0, 0], ![760, 369, 392, 2, 0]] i)))

def P883P0 : CertificateIrreducibleZModOfList' 883 2 2 9 [537, 491, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [392, 882], [0, 1]]
 g := ![![[338, 682], [855, 796], [360], [159], [793, 601], [667, 878], [706, 261], [325], [392, 1]], ![[133, 201], [305, 87], [360], [159], [624, 282], [473, 5], [590, 622], [325], [784, 882]]]
 h' := ![![[392, 882], [25, 523], [10, 291], [747, 521], [648, 697], [319, 461], [568, 499], [72, 484], [533, 368], [0, 1]], ![[0, 1], [185, 360], [175, 592], [123, 362], [142, 186], [16, 422], [150, 384], [838, 399], [860, 515], [392, 882]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [520]]
 b := ![[], [254, 260]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P883P1 : CertificateIrreducibleZModOfList' 883 3 2 9 [760, 368, 392, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [491, 668, 65], [0, 214, 818], [0, 1]]
 g := ![![[205], [14, 69, 331], [174, 386], [326, 316], [69, 103, 646], [30, 420, 253], [733, 592, 424], [860, 22], [1]], ![[42, 489, 433, 694], [571, 184, 248, 248], [574, 342], [519, 857], [177, 599, 548, 65], [214, 336, 98, 454], [614, 2, 611, 175], [134, 543], [870, 530, 407, 12]], ![[0, 56, 744, 189], [14, 722, 326, 84], [534, 189], [67, 40], [671, 282, 776, 745], [115, 719, 233, 361], [576, 258, 706, 202], [677, 394], [626, 123, 163, 871]]]
 h' := ![![[491, 668, 65], [839, 240], [63, 840, 431], [573, 140, 787], [540, 762, 326], [158, 704, 533], [93, 293, 179], [821, 112, 177], [123, 515, 491], [0, 1]], ![[0, 214, 818], [357, 497, 589], [747, 736, 256], [294, 334, 35], [764, 407, 89], [721, 620, 882], [141, 659, 839], [203, 657, 125], [373, 155, 801], [491, 668, 65]], ![[0, 1], [839, 146, 294], [774, 190, 196], [388, 409, 61], [414, 597, 468], [17, 442, 351], [208, 814, 748], [693, 114, 581], [177, 213, 474], [0, 214, 818]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [105, 452], []]
 b := ![[], [805, 243, 387], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A883 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 883 2 where
 D := ![[537, 491, 1], [760, 368, 392, 1]]; D' := ![[537, 491, 1], [760, 368, 392, 1]]
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
  w := ![![883, 0, 0, 0, 0], ![537, 491, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C8831 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A883.D 1) 883 where
  n := 3
  w := ![![883, 0, 0, 0, 0], ![760, 369, 392, 2, 0]]
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


lemma PB18792I16_primes (p : ℕ) :
  p ∈ Set.range ![829, 839, 853, 857, 859, 863, 877, 881, 883] ↔ Nat.Prime p ∧ 827 < p ∧ p ≤ 883 := by
  rw [← List.mem_ofFn']
  convert primes_range 827 883 (by omega)
  decide

def PB18792I16 : PrimesBelowBoundCertificateInterval O 827 883 18792 where
  m := 9
  g := ![3, 3, 2, 4, 1, 2, 2, 1, 2]
  P := ![829, 839, 853, 857, 859, 863, 877, 881, 883]
  hP := PB18792I16_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I829N0, I829N1, I829N2]
    · exact ![I839N0, I839N1, I839N2]
    · exact ![I853N0, I853N1]
    · exact ![I857N0, I857N1, I857N2, I857N3]
    · exact ![I859N0]
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
    · exact ![829, 829, 569722789]
    · exact ![839, 839, 590589719]
    · exact ![853, 529414856881]
    · exact ![857, 857, 857, 734449]
    · exact ![467698329968299]
    · exact ![863, 554680863361]
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
  β := ![I829N0, I829N1, I839N0, I839N1, I853N0, I857N0, I857N1, I857N2, I863N0, I877N0]
  Il := ![[I829N0, I829N1], [I839N0, I839N1], [I853N0], [I857N0, I857N1, I857N2], [], [I863N0], [I877N0], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
