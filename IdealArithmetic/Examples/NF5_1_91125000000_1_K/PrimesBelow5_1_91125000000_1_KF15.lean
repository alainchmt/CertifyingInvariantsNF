
import IdealArithmetic.Examples.NF5_1_91125000000_1_K.RI5_1_91125000000_1_K
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 

instance hp769 : Fact (Nat.Prime 769) := {out := by norm_num}

def I769N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![769, 0, 0, 0, 0], ![16149, 769, 769, 0, 0]] i)))

def P769P0 : CertificateIrreducibleZModOfList' 769 5 2 9 [429, 244, 669, 0, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [738, 182, 740, 706, 194], [696, 328, 369, 291, 550], [194, 110, 100, 750, 709], [679, 148, 329, 560, 85], [0, 1]]
 g := ![![[450, 251, 636, 681, 54], [191, 51, 345, 692], [216, 683, 58, 54], [464, 311, 702, 242], [145, 162, 304, 600], [634, 643, 357, 82], [416, 3], [0, 1], []], ![[61, 442, 730, 373, 556, 39, 647, 630], [432, 38, 368, 313], [23, 408, 214, 487], [244, 176, 496, 544], [651, 657, 119, 231], [56, 160, 315, 8], [149, 756, 595, 738], [203, 149, 33, 17], [55, 601, 608, 243, 74, 721, 46, 498]], ![[476, 647, 672, 128, 726, 640, 716, 280], [636, 595, 147, 679], [720, 733, 133, 136], [363, 733, 207, 452], [283, 490, 399, 135], [561, 299, 498, 20], [629, 710, 283, 544], [356, 359, 494, 589], [101, 587, 487, 388, 214, 493, 210, 312]], ![[588, 360, 545, 721, 355, 698, 280, 54], [639, 548, 218, 625], [621, 702, 218, 243], [5, 303, 437, 95], [543, 490, 455, 36], [346, 748, 112, 678], [344, 500, 515, 456], [321, 556, 35, 60], [211, 462, 180, 674, 757, 709, 123, 89]], ![[394, 288, 267, 665, 104, 540, 452, 45], [429, 630, 100, 82], [591, 480, 553, 587], [312, 313, 411, 577], [554, 260, 716, 516], [697, 41, 315, 425], [351, 99, 623, 356], [179, 143, 647, 153], [543, 517, 94, 292, 628, 597, 104, 463]]]
 h' := ![![[738, 182, 740, 706, 194], [617, 190, 607, 385, 681], [122, 480, 167, 214, 114], [132, 219, 451, 446, 88], [111, 627, 351, 220, 75], [300, 759, 189, 399, 37], [713, 255, 361, 484, 651], [0, 340, 525, 100], [0, 0, 0, 1], [0, 1]], ![[696, 328, 369, 291, 550], [192, 507, 541, 261, 361], [224, 532, 434, 282, 137], [720, 113, 386, 122, 45], [245, 359, 654, 718, 161], [675, 370, 49, 221, 89], [478, 72, 68, 50, 503], [82, 24, 435, 671, 354], [444, 456, 507, 447, 111], [738, 182, 740, 706, 194]], ![[194, 110, 100, 750, 709], [27, 284, 619, 637, 445], [61, 133, 699, 486, 425], [82, 448, 80, 601, 304], [330, 736, 356, 509, 566], [128, 523, 697, 483, 84], [10, 134, 242, 599, 184], [78, 433, 443, 226, 608], [601, 298, 84, 259, 381], [696, 328, 369, 291, 550]], ![[679, 148, 329, 560, 85], [27, 442, 144, 589, 342], [548, 715, 190, 334, 744], [402, 35, 489, 52, 638], [657, 547, 749, 502, 352], [380, 653, 71, 102, 6], [717, 8, 297, 41, 414], [708, 365, 294, 487, 734], [721, 4, 372, 240, 713], [194, 110, 100, 750, 709]], ![[0, 1], [594, 115, 396, 435, 478], [269, 447, 48, 222, 118], [327, 723, 132, 317, 463], [471, 38, 197, 358, 384], [553, 2, 532, 333, 553], [555, 300, 570, 364, 555], [679, 376, 610, 54, 611], [72, 11, 575, 591, 333], [679, 148, 329, 560, 85]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [613, 353, 202, 60], [], [], []]
 b := ![[], [421, 385, 390, 408, 515], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A769 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 769 1 where
 D := ![[429, 244, 669, 0, 0, 1]]; D' := ![[429, 244, 669, 0, 0, 1]]
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
  w := ![![769, 0, 0, 0, 0], ![16149, 769, 769, 0, 0]]
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

def I773N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![773, 0, 0, 0, 0], ![761, 388, 1, 0, 0]] i)))

def I773N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![773, 0, 0, 0, 0], ![537, 595, 385, 2, 0]] i)))

def P773P0 : CertificateIrreducibleZModOfList' 773 2 2 9 [761, 388, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [385, 772], [0, 1]]
 g := ![![[483, 349], [403], [277, 86], [251], [276], [413], [620], [348], [385, 1]], ![[346, 424], [403], [148, 687], [251], [276], [413], [620], [348], [770, 772]]]
 h' := ![![[385, 772], [685, 260], [232, 71], [164, 515], [439, 741], [153, 557], [202, 266], [635, 511], [755, 594], [0, 1]], ![[0, 1], [295, 513], [512, 702], [551, 258], [487, 32], [477, 216], [576, 507], [255, 262], [637, 179], [385, 772]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [746]]
 b := ![[], [473, 373]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P773P1 : CertificateIrreducibleZModOfList' 773 3 2 9 [537, 594, 385, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [165, 289, 212], [223, 483, 561], [0, 1]]
 g := ![![[587, 691, 437], [632, 267], [467, 527, 655], [174, 44], [355, 772], [563, 155], [24, 328], [637, 582], [1]], ![[324, 14, 675, 158], [753, 331], [511, 768, 515, 637], [32, 612], [360, 165], [317, 272], [630, 178], [380, 313], [682, 718, 486, 130]], ![[264, 183, 307, 662], [303, 717], [52, 443, 212, 206], [383, 351], [632, 568], [474, 691], [183, 152], [33, 576], [120, 532, 730, 643]]]
 h' := ![![[165, 289, 212], [218, 378, 248], [446, 82, 296], [733, 725, 508], [144, 634, 717], [324, 656, 456], [612, 667, 642], [410, 381, 675], [236, 179, 388], [0, 1]], ![[223, 483, 561], [106, 129, 486], [742, 664, 341], [749, 644, 196], [145, 476, 686], [535, 502, 648], [224, 499, 58], [604, 166, 199], [390, 625, 409], [165, 289, 212]], ![[0, 1], [571, 266, 39], [233, 27, 136], [451, 177, 69], [245, 436, 143], [722, 388, 442], [608, 380, 73], [268, 226, 672], [601, 742, 749], [223, 483, 561]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [300, 384], []]
 b := ![[], [490, 427, 567], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A773 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 773 2 where
 D := ![[761, 388, 1], [537, 594, 385, 1]]; D' := ![[761, 388, 1], [537, 594, 385, 1]]
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
  w := ![![773, 0, 0, 0, 0], ![761, 388, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C7731 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A773.D 1) 773 where
  n := 3
  w := ![![773, 0, 0, 0, 0], ![537, 595, 385, 2, 0]]
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

def I787N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![787, 0, 0, 0, 0], ![346, 1, 0, 0, 0]] i)))

def I787N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![787, 0, 0, 0, 0], ![367, 1, 0, 0, 0]] i)))

def I787N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![787, 0, 0, 0, 0], ![408, 1, 0, 0, 0]] i)))

def I787N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![787, 0, 0, 0, 0], ![600, 453, 1, 0, 0]] i)))

def P787P0 : CertificateIrreducibleZModOfList' 787 1 2 9 [346, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [116], [], [], [319], [], [], [], [92, 441, 1]]]
 h' := ![![[0, 1], [1], [712], [647], [593], [716], [188], [345], [435], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P787P1 : CertificateIrreducibleZModOfList' 787 1 2 9 [367, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [594], [], [], [118], [], [], [], [112, 420, 1]]]
 h' := ![![[0, 1], [1], [92], [441], [766], [539], [375], [133], [607], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P787P2 : CertificateIrreducibleZModOfList' 787 1 2 9 [408, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [407], [], [], [1], [], [], [], [407, 379, 1]]]
 h' := ![![[0, 1], [1], [379], [407], [379], [1], [1], [1], [1], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P787P3 : CertificateIrreducibleZModOfList' 787 2 2 9 [600, 453, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [334, 786], [0, 1]]
 g := ![![[107, 101], [590, 257], [110], [374], [381, 204], [561], [517], [121], [334, 1]], ![[0, 686], [645, 530], [110], [374], [48, 583], [561], [517], [121], [668, 786]]]
 h' := ![![[334, 786], [150, 730], [95, 562], [644, 132], [417, 560], [82, 609], [115, 608], [755, 303], [285, 776], [0, 1]], ![[0, 1], [0, 57], [497, 225], [660, 655], [151, 227], [442, 178], [141, 179], [434, 484], [546, 11], [334, 786]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [704]]
 b := ![[], [241, 352]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A787 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 787 4 where
 D := ![[346, 1], [367, 1], [408, 1], [600, 453, 1]]; D' := ![[346, 1], [367, 1], [408, 1], [600, 453, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9, 9, 9]
 n := ![1, 1, 1, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P787P0
  | 1 => exact P787P1
  | 2 => exact P787P2
  | 3 => exact P787P3

def C7870 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A787.D 0) 787 where
  n := 1
  w := ![![787, 0, 0, 0, 0], ![346, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C7871 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A787.D 1) 787 where
  n := 1
  w := ![![787, 0, 0, 0, 0], ![367, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C7872 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A787.D 2) 787 where
  n := 1
  w := ![![787, 0, 0, 0, 0], ![408, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C7873 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A787.D 3) 787 where
  n := 2
  w := ![![787, 0, 0, 0, 0], ![600, 453, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K787 : KummerData 787 ![I787N0, I787N1, I787N2, I787N3] ![787, 787, 787, 619369] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A787
  C := by
    intro i
    match i with
    | 0 => exact C7870
    | 1 => exact C7871
    | 2 => exact C7872
    | 3 => exact C7873
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 787 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp797 : Fact (Nat.Prime 797) := {out := by norm_num}

def I797N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![797, 0, 0, 0, 0], ![100, 1, 0, 0, 0]] i)))

def I797N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![797, 0, 0, 0, 0], ![534, 1, 0, 0, 0]] i)))

def I797N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![797, 0, 0, 0, 0], ![544, 1, 0, 0, 0]] i)))

def I797N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![797, 0, 0, 0, 0], ![311, 416, 1, 0, 0]] i)))

def P797P0 : CertificateIrreducibleZModOfList' 797 1 2 9 [100, 1] where
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
 g := ![![[], [], [534], [691], [360], [], [], [], [436, 697, 1]]]
 h' := ![![[0, 1], [1], [796], [239], [662], [503], [425], [232], [235], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P797P1 : CertificateIrreducibleZModOfList' 797 1 2 9 [534, 1] where
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
 g := ![![[], [], [100], [203], [414], [], [], [], [627, 263, 1]]]
 h' := ![![[0, 1], [1], [796], [787], [490], [225], [782], [505], [719], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P797P2 : CertificateIrreducibleZModOfList' 797 1 2 9 [544, 1] where
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
 g := ![![[], [], [4], [126], [679], [], [], [], [249, 253, 1]]]
 h' := ![![[0, 1], [796], [215], [795], [432], [93], [564], [359], [34], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P797P3 : CertificateIrreducibleZModOfList' 797 2 2 9 [311, 416, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [381, 796], [0, 1]]
 g := ![![[478, 756], [294], [554, 109], [262, 482], [658, 525], [315], [24], [172], [381, 1]], ![[0, 41], [294], [639, 688], [594, 315], [636, 272], [315], [24], [172], [762, 796]]]
 h' := ![![[381, 796], [460, 254], [655, 517], [609, 747], [191, 125], [331, 54], [587, 223], [9, 80], [262, 593], [0, 1]], ![[0, 1], [0, 543], [773, 280], [687, 50], [793, 672], [183, 743], [271, 574], [203, 717], [644, 204], [381, 796]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [722]]
 b := ![[], [170, 361]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A797 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 797 4 where
 D := ![[100, 1], [534, 1], [544, 1], [311, 416, 1]]; D' := ![[100, 1], [534, 1], [544, 1], [311, 416, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9, 9, 9]
 n := ![1, 1, 1, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P797P0
  | 1 => exact P797P1
  | 2 => exact P797P2
  | 3 => exact P797P3

def C7970 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A797.D 0) 797 where
  n := 1
  w := ![![797, 0, 0, 0, 0], ![100, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C7971 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A797.D 1) 797 where
  n := 1
  w := ![![797, 0, 0, 0, 0], ![534, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C7972 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A797.D 2) 797 where
  n := 1
  w := ![![797, 0, 0, 0, 0], ![544, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C7973 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A797.D 3) 797 where
  n := 2
  w := ![![797, 0, 0, 0, 0], ![311, 416, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K797 : KummerData 797 ![I797N0, I797N1, I797N2, I797N3] ![797, 797, 797, 635209] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A797
  C := by
    intro i
    match i with
    | 0 => exact C7970
    | 1 => exact C7971
    | 2 => exact C7972
    | 3 => exact C7973
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 797 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp809 : Fact (Nat.Prime 809) := {out := by norm_num}

def I809N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![809, 0, 0, 0, 0], ![16180, 809, 809, 0, 0]] i)))

def P809P0 : CertificateIrreducibleZModOfList' 809 5 2 9 [460, 284, 709, 0, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [623, 129, 321, 537, 282], [660, 417, 650, 200, 201], [615, 522, 508, 107, 590], [529, 549, 139, 774, 545], [0, 1]]
 g := ![![[222, 271, 327, 724, 91], [481, 245, 244, 255], [74, 362, 655, 321], [284, 222, 375, 394, 73], [129, 15, 155, 676], [670, 332, 512, 663, 324], [639, 292], [0, 1], []], ![[446, 627, 31, 386, 169, 716, 666, 619], [629, 207, 403, 400], [58, 798, 715, 781], [199, 279, 583, 497, 688, 711, 17, 213], [402, 27, 667, 657], [1, 69, 438, 769, 346, 699, 364, 748], [216, 106, 684, 711], [642, 344, 102, 194], [610, 225, 313, 132, 108, 615, 733, 288]], ![[236, 277, 207, 163, 486, 522, 511, 10], [120, 484, 405, 90], [702, 314, 640, 683], [699, 162, 433, 353, 171, 498, 277, 630], [472, 338, 431, 26], [705, 384, 25, 437, 165, 396, 45, 380], [396, 553, 672, 422], [577, 241, 426, 681], [281, 676, 141, 138, 291, 386, 533, 668]], ![[534, 625, 113, 569, 19, 629, 302, 470], [527, 291, 295, 676], [757, 638, 350, 171], [508, 453, 790, 342, 475, 531, 650, 77], [136, 241, 420, 549], [377, 637, 729, 457, 502, 204, 412, 240], [339, 300, 365, 575], [432, 775, 428, 289], [65, 56, 754, 675, 625, 312, 211, 597]], ![[638, 219, 123, 552, 571, 507, 457, 254], [638, 460, 768, 774], [753, 287, 22, 33], [147, 30, 347, 586, 365, 579, 498, 400], [315, 578, 759, 484], [314, 390, 349, 319, 718, 623, 666, 718], [515, 464, 83, 484], [683, 687, 592, 555], [271, 650, 362, 330, 568, 507, 134, 152]]]
 h' := ![![[623, 129, 321, 537, 282], [658, 308, 216, 66, 30], [727, 609, 473, 472, 655], [418, 766, 20, 552, 441], [558, 464, 176, 530, 759], [29, 117, 136, 143, 26], [536, 523, 30, 49, 791], [0, 349, 525, 100], [0, 0, 0, 1], [0, 1]], ![[660, 417, 650, 200, 201], [161, 114, 437, 727, 374], [262, 458, 124, 273, 20], [750, 585, 592, 606, 602], [657, 262, 275, 639, 148], [567, 577, 378, 102, 150], [15, 316, 321, 317, 544], [347, 693, 688, 788, 446], [53, 449, 92, 95, 520], [623, 129, 321, 537, 282]], ![[615, 522, 508, 107, 590], [556, 121, 367, 118, 566], [587, 451, 801, 203, 270], [69, 648, 37, 177, 532], [534, 236, 183, 337, 255], [161, 518, 540, 302, 211], [660, 766, 257, 603, 126], [362, 434, 735, 327, 194], [232, 464, 473, 582, 163], [660, 417, 650, 200, 201]], ![[529, 549, 139, 774, 545], [336, 752, 42, 621, 225], [333, 456, 369, 41, 783], [532, 676, 0, 499, 691], [466, 759, 383, 701, 103], [746, 676, 737, 77, 444], [297, 684, 303, 791, 48], [799, 387, 801, 15, 147], [683, 174, 653, 774, 17], [615, 522, 508, 107, 590]], ![[0, 1], [243, 323, 556, 86, 423], [333, 453, 660, 629, 699], [680, 561, 160, 593, 161], [372, 706, 601, 220, 353], [680, 539, 636, 185, 787], [724, 138, 707, 667, 109], [177, 564, 487, 388, 22], [141, 531, 400, 166, 109], [529, 549, 139, 774, 545]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [672, 364, 588, 642], [], [], []]
 b := ![[], [692, 741, 778, 365, 101], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A809 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 809 1 where
 D := ![[460, 284, 709, 0, 0, 1]]; D' := ![[460, 284, 709, 0, 0, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9]
 n := ![5]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P809P0

def C8090 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A809.D 0) 809 where
  n := 5
  w := ![![809, 0, 0, 0, 0], ![16180, 809, 809, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K809 : KummerData 809 ![I809N0] ![346531411903049] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A809
  C := by
    intro i
    match i with
    | 0 => exact C8090
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 809 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp811 : Fact (Nat.Prime 811) := {out := by norm_num}

def I811N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![811, 0, 0, 0, 0], ![134, 1, 0, 0, 0]] i)))

def I811N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![811, 0, 0, 0, 0], ![175, 1, 0, 0, 0]] i)))

def I811N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![811, 0, 0, 0, 0], ![792, 664, 502, 2, 0]] i)))

def P811P0 : CertificateIrreducibleZModOfList' 811 1 2 9 [134, 1] where
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
 g := ![![[], [696], [], [568], [], [746], [], [], [114, 677, 1]]]
 h' := ![![[0, 1], [1], [286], [122], [727], [600], [701], [658], [133], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P811P1 : CertificateIrreducibleZModOfList' 811 1 2 9 [175, 1] where
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
 g := ![![[], [621], [], [688], [], [125], [], [], [618, 636, 1]]]
 h' := ![![[0, 1], [810], [514], [439], [484], [22], [526], [458], [524], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P811P2 : CertificateIrreducibleZModOfList' 811 3 2 9 [792, 663, 502, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [457, 686, 650], [663, 124, 161], [0, 1]]
 g := ![![[707, 441, 436], [127, 434, 520], [656, 725], [655, 646, 271], [7, 306], [531, 203, 292], [62, 255], [81, 594], [1]], ![[176, 49, 495, 36], [703, 435, 148, 281], [598, 594], [245, 363, 742, 594], [162, 80], [238, 172, 254, 255], [278, 676], [95, 746], [352, 464, 779, 125]], ![[39, 783, 65, 186], [102, 427, 510, 615], [697, 502], [533, 83, 121, 33], [138, 448], [511, 623, 208, 446], [205, 185], [177, 673], [417, 108, 125, 686]]]
 h' := ![![[457, 686, 650], [791, 492, 227], [32, 564, 262], [280, 685, 748], [255, 129, 52], [357, 387, 210], [606, 801, 649], [278, 513, 607], [19, 148, 309], [0, 1]], ![[663, 124, 161], [464, 34, 29], [717, 786, 76], [428, 305, 309], [796, 704, 277], [462, 405, 228], [590, 694, 175], [668, 175, 785], [36, 793, 701], [457, 686, 650]], ![[0, 1], [769, 285, 555], [492, 272, 473], [15, 632, 565], [700, 789, 482], [177, 19, 373], [143, 127, 798], [364, 123, 230], [399, 681, 612], [663, 124, 161]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47, 538], []]
 b := ![[], [726, 724, 633], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A811 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 811 3 where
 D := ![[134, 1], [175, 1], [792, 663, 502, 1]]; D' := ![[134, 1], [175, 1], [792, 663, 502, 1]]
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
  w := ![![811, 0, 0, 0, 0], ![134, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C8111 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A811.D 1) 811 where
  n := 1
  w := ![![811, 0, 0, 0, 0], ![175, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C8112 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A811.D 2) 811 where
  n := 3
  w := ![![811, 0, 0, 0, 0], ![792, 664, 502, 2, 0]]
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

def I821N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![821, 0, 0, 0, 0], ![726, 1, 0, 0, 0]] i)))

def I821N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![821, 0, 0, 0, 0], ![233, 161, 1, 0, 0]] i)))

def I821N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![821, 0, 0, 0, 0], ![535, 755, 1, 0, 0]] i)))

def P821P0 : CertificateIrreducibleZModOfList' 821 1 2 9 [726, 1] where
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
 g := ![![[], [], [700], [], [35], [177], [], [], [815, 95, 1]]]
 h' := ![![[0, 1], [1], [820], [39], [41], [395], [680], [605], [251], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P821P1 : CertificateIrreducibleZModOfList' 821 2 2 9 [233, 161, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [660, 820], [0, 1]]
 g := ![![[420, 600], [449], [482, 690], [277], [137, 154], [607, 245], [37], [341], [660, 1]], ![[698, 221], [449], [227, 131], [277], [794, 667], [570, 576], [37], [341], [499, 820]]]
 h' := ![![[660, 820], [156, 532], [171, 513], [70, 492], [98, 695], [602, 616], [626, 512], [155, 50], [568, 237], [0, 1]], ![[0, 1], [709, 289], [499, 308], [495, 329], [680, 126], [767, 205], [294, 309], [315, 771], [177, 584], [660, 820]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [295]]
 b := ![[], [585, 558]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P821P2 : CertificateIrreducibleZModOfList' 821 2 2 9 [535, 755, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [66, 820], [0, 1]]
 g := ![![[316, 121], [193], [292, 163], [365], [71, 469], [402, 419], [222], [198], [66, 1]], ![[92, 700], [193], [377, 658], [365], [648, 352], [142, 402], [222], [198], [132, 820]]]
 h' := ![![[66, 820], [547, 11], [591, 622], [466, 135], [602, 274], [32, 223], [238, 336], [28, 624], [814, 537], [0, 1]], ![[0, 1], [452, 810], [593, 199], [345, 686], [624, 547], [793, 598], [247, 485], [162, 197], [132, 284], [66, 820]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [123]]
 b := ![[], [23, 472]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A821 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 821 3 where
 D := ![[726, 1], [233, 161, 1], [535, 755, 1]]; D' := ![[726, 1], [233, 161, 1], [535, 755, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9, 9]
 n := ![1, 2, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P821P0
  | 1 => exact P821P1
  | 2 => exact P821P2

def C8210 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A821.D 0) 821 where
  n := 1
  w := ![![821, 0, 0, 0, 0], ![726, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C8211 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A821.D 1) 821 where
  n := 2
  w := ![![821, 0, 0, 0, 0], ![233, 161, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C8212 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A821.D 2) 821 where
  n := 2
  w := ![![821, 0, 0, 0, 0], ![535, 755, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K821 : KummerData 821 ![I821N0, I821N1, I821N2] ![821, 674041, 674041] where
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

def I823N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![823, 0, 0, 0, 0], ![465, 1, 0, 0, 0]] i)))

def I823N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![823, 0, 0, 0, 0], ![710, 1, 0, 0, 0]] i)))

def I823N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![823, 0, 0, 0, 0], ![805, 1, 0, 0, 0]] i)))

def I823N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![823, 0, 0, 0, 0], ![76, 489, 1, 0, 0]] i)))

def P823P0 : CertificateIrreducibleZModOfList' 823 1 2 9 [465, 1] where
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
 g := ![![[], [200], [693], [], [25], [646], [], [], [599, 358, 1]]]
 h' := ![![[0, 1], [822], [371], [733], [720], [5], [69], [287], [462], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P823P1 : CertificateIrreducibleZModOfList' 823 1 2 9 [710, 1] where
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
 g := ![![[], [437], [512], [], [502], [468], [], [], [424, 113, 1]]]
 h' := ![![[0, 1], [1], [246], [429], [762], [212], [208], [410], [178], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P823P2 : CertificateIrreducibleZModOfList' 823 1 2 9 [805, 1] where
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
 g := ![![[], [503], [607], [], [181], [693], [], [], [324, 18, 1]]]
 h' := ![![[0, 1], [1], [227], [333], [789], [129], [733], [103], [71], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P823P3 : CertificateIrreducibleZModOfList' 823 2 2 9 [76, 489, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [334, 822], [0, 1]]
 g := ![![[667, 556], [153, 502], [172, 236], [731], [771, 379], [129, 262], [796], [715], [334, 1]], ![[373, 267], [752, 321], [811, 587], [731], [615, 444], [399, 561], [796], [715], [668, 822]]]
 h' := ![![[334, 822], [717, 768], [96, 212], [641, 406], [660, 162], [72, 778], [174, 404], [159, 599], [129, 375], [0, 1]], ![[0, 1], [453, 55], [126, 611], [450, 417], [450, 661], [679, 45], [138, 419], [236, 224], [283, 448], [334, 822]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [711]]
 b := ![[], [299, 767]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A823 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 823 4 where
 D := ![[465, 1], [710, 1], [805, 1], [76, 489, 1]]; D' := ![[465, 1], [710, 1], [805, 1], [76, 489, 1]]
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
  w := ![![823, 0, 0, 0, 0], ![465, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C8231 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A823.D 1) 823 where
  n := 1
  w := ![![823, 0, 0, 0, 0], ![710, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C8232 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A823.D 2) 823 where
  n := 1
  w := ![![823, 0, 0, 0, 0], ![805, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C8233 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A823.D 3) 823 where
  n := 2
  w := ![![823, 0, 0, 0, 0], ![76, 489, 1, 0, 0]]
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

def I827N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![827, 0, 0, 0, 0], ![334, 778, 1, 0, 0]] i)))

def I827N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![827, 0, 0, 0, 0], ![463, 414, 49, 2, 0]] i)))

def P827P0 : CertificateIrreducibleZModOfList' 827 2 2 9 [334, 778, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [49, 826], [0, 1]]
 g := ![![[760, 330], [747, 377], [371], [773, 772], [112, 616], [80, 286], [371], [207], [49, 1]], ![[390, 497], [199, 450], [371], [559, 55], [524, 211], [35, 541], [371], [207], [98, 826]]]
 h' := ![![[49, 826], [256, 574], [290, 651], [669, 45], [634, 81], [571, 511], [185, 615], [7, 45], [174, 413], [0, 1]], ![[0, 1], [264, 253], [763, 176], [393, 782], [468, 746], [800, 316], [548, 212], [558, 782], [563, 414], [49, 826]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [549]]
 b := ![[], [511, 688]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P827P1 : CertificateIrreducibleZModOfList' 827 3 2 9 [463, 413, 49, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [317, 294, 427], [461, 532, 400], [0, 1]]
 g := ![![[712, 666, 310], [381, 292, 258], [417, 452], [625, 22, 279], [818, 640, 439], [354, 437, 56], [82, 537], [563, 747], [1]], ![[714, 802, 168, 787], [634, 387, 363, 701], [39, 11], [177, 334, 280, 590], [6, 236, 631, 540], [804, 794, 754, 239], [796, 329], [428, 374], [103, 452, 180, 703]], ![[22, 234, 526, 327], [752, 107, 230, 795], [209, 782], [168, 352, 405, 408], [601, 419, 333, 416], [174, 337, 169, 729], [799, 259], [286, 107], [84, 90, 307, 124]]]
 h' := ![![[317, 294, 427], [575, 79, 383], [283, 487, 178], [75, 661, 79], [32, 508, 405], [671, 68, 473], [220, 51, 769], [12, 57, 587], [364, 414, 778], [0, 1]], ![[461, 532, 400], [248, 417, 140], [163, 590, 790], [652, 812, 91], [135, 304, 682], [55, 633, 319], [653, 90, 18], [456, 115, 34], [77, 474, 196], [317, 294, 427]], ![[0, 1], [681, 331, 304], [520, 577, 686], [564, 181, 657], [105, 15, 567], [284, 126, 35], [216, 686, 40], [22, 655, 206], [776, 766, 680], [461, 532, 400]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [496, 505], []]
 b := ![[], [173, 139, 177], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A827 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 827 2 where
 D := ![[334, 778, 1], [463, 413, 49, 1]]; D' := ![[334, 778, 1], [463, 413, 49, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P827P0
  | 1 => exact P827P1

def C8270 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A827.D 0) 827 where
  n := 2
  w := ![![827, 0, 0, 0, 0], ![334, 778, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C8271 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A827.D 1) 827 where
  n := 3
  w := ![![827, 0, 0, 0, 0], ![463, 414, 49, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K827 : KummerData 827 ![I827N0, I827N1] ![683929, 565609283] where
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


lemma PB18792I15_primes (p : ℕ) :
  p ∈ Set.range ![769, 773, 787, 797, 809, 811, 821, 823, 827] ↔ Nat.Prime p ∧ 761 < p ∧ p ≤ 827 := by
  rw [← List.mem_ofFn']
  convert primes_range 761 827 (by omega)
  decide

def PB18792I15 : PrimesBelowBoundCertificateInterval O 761 827 18792 where
  m := 9
  g := ![1, 2, 4, 4, 1, 3, 3, 4, 2]
  P := ![769, 773, 787, 797, 809, 811, 821, 823, 827]
  hP := PB18792I15_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I769N0]
    · exact ![I773N0, I773N1]
    · exact ![I787N0, I787N1, I787N2, I787N3]
    · exact ![I797N0, I797N1, I797N2, I797N3]
    · exact ![I809N0]
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
    · exact ![787, 787, 787, 619369]
    · exact ![797, 797, 797, 635209]
    · exact ![346531411903049]
    · exact ![811, 811, 533411731]
    · exact ![821, 674041, 674041]
    · exact ![823, 823, 823, 677329]
    · exact ![683929, 565609283]
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
  β := ![I787N0, I787N1, I787N2, I797N0, I797N1, I797N2, I811N0, I811N1, I821N0, I823N0, I823N1, I823N2]
  Il := ![[], [], [I787N0, I787N1, I787N2], [I797N0, I797N1, I797N2], [], [I811N0, I811N1], [I821N0], [I823N0, I823N1, I823N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
