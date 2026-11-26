
import IdealArithmetic.Examples.NF5_1_91125000000_1_K.RI5_1_91125000000_1_K
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 

instance hp709 : Fact (Nat.Prime 709) := {out := by norm_num}

def I709N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![709, 0, 0, 0, 0], ![536, 1, 0, 0, 0]] i)))

def I709N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![709, 0, 0, 0, 0], ![689, 1, 0, 0, 0]] i)))

def I709N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![709, 0, 0, 0, 0], ![602, 467, 193, 2, 0]] i)))

def P709P0 : CertificateIrreducibleZModOfList' 709 1 2 9 [536, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [603], [], [], [], [348], [113], [173, 1]]]
 h' := ![![[0, 1], [708], [96], [188], [489], [176], [648], [406], [151], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P709P1 : CertificateIrreducibleZModOfList' 709 1 2 9 [689, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [390], [], [], [], [681], [475], [20, 1]]]
 h' := ![![[0, 1], [1], [1], [604], [363], [222], [149], [283], [400], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P709P2 : CertificateIrreducibleZModOfList' 709 3 2 9 [602, 466, 193, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [158, 583, 681], [358, 125, 28], [0, 1]]
 g := ![![[134, 610, 481], [177, 412], [253, 453, 182], [87, 560], [140, 627], [331, 7], [556, 675, 74], [624, 516, 1], []], ![[267, 25, 449, 405], [340, 81], [112, 319, 81, 175], [624, 64], [187, 252], [12, 336], [10, 673, 81, 387], [621, 96, 33, 662], [380, 75]], ![[271, 392, 221, 500], [395, 507], [613, 655, 303, 136], [247, 414], [641, 568], [673, 373], [550, 340, 535, 560], [186, 615, 338, 694], [324, 75]]]
 h' := ![![[158, 583, 681], [130, 223, 227], [129, 70, 78], [501, 170, 40], [413, 157, 279], [518, 242, 451], [645, 300, 596], [122, 525, 100], [0, 0, 1], [0, 1]], ![[358, 125, 28], [472, 211, 152], [246, 570, 700], [661, 575, 240], [284, 607, 701], [396, 459, 678], [461, 299, 163], [15, 536, 636], [396, 284, 125], [158, 583, 681]], ![[0, 1], [414, 275, 330], [244, 69, 640], [84, 673, 429], [143, 654, 438], [377, 8, 289], [229, 110, 659], [493, 357, 682], [471, 425, 583], [358, 125, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23, 264], []]
 b := ![[], [222, 74, 212], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A709 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 709 3 where
 D := ![[536, 1], [689, 1], [602, 466, 193, 1]]; D' := ![[536, 1], [689, 1], [602, 466, 193, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9, 9]
 n := ![1, 1, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P709P0
  | 1 => exact P709P1
  | 2 => exact P709P2

def C7090 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A709.D 0) 709 where
  n := 1
  w := ![![709, 0, 0, 0, 0], ![536, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C7091 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A709.D 1) 709 where
  n := 1
  w := ![![709, 0, 0, 0, 0], ![689, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C7092 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A709.D 2) 709 where
  n := 3
  w := ![![709, 0, 0, 0, 0], ![602, 467, 193, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K709 : KummerData 709 ![I709N0, I709N1, I709N2] ![709, 709, 356400829] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A709
  C := by
    intro i
    match i with
    | 0 => exact C7090
    | 1 => exact C7091
    | 2 => exact C7092
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 709 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp719 : Fact (Nat.Prime 719) := {out := by norm_num}

def I719N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![719, 0, 0, 0, 0], ![161, 1, 0, 0, 0]] i)))

def I719N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![719, 0, 0, 0, 0], ![701, 608, 1, 0, 0]] i)))

def I719N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![719, 0, 0, 0, 0], ![257, 669, 1, 0, 0]] i)))

def P719P0 : CertificateIrreducibleZModOfList' 719 1 2 9 [161, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [326], [31], [111], [], [], [2], [650], [558, 1]]]
 h' := ![![[0, 1], [1], [42], [104], [334], [148], [397], [324], [37], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P719P1 : CertificateIrreducibleZModOfList' 719 2 2 9 [701, 608, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [111, 718], [0, 1]]
 g := ![![[126, 273], [431, 244], [141, 111], [502, 75], [50], [338], [108, 261], [494, 98], [1]], ![[231, 446], [193, 475], [239, 608], [199, 644], [50], [338], [319, 458], [587, 621], [1]]]
 h' := ![![[111, 718], [568, 388], [381, 49], [408, 334], [184, 137], [404, 537], [506, 102], [264, 121], [18, 111], [0, 1]], ![[0, 1], [496, 331], [68, 670], [94, 385], [292, 582], [334, 182], [324, 617], [34, 598], [116, 608], [111, 718]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [406]]
 b := ![[], [597, 203]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P719P2 : CertificateIrreducibleZModOfList' 719 2 2 9 [257, 669, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [50, 718], [0, 1]]
 g := ![![[246, 484], [379, 500], [490, 257], [322, 289], [288], [273], [55, 480], [78, 343], [1]], ![[0, 235], [214, 219], [398, 462], [392, 430], [288], [273], [328, 239], [691, 376], [1]]]
 h' := ![![[50, 718], [381, 697], [614, 600], [650, 621], [627, 702], [649, 293], [245, 388], [86, 492], [462, 50], [0, 1]], ![[0, 1], [0, 22], [416, 119], [64, 98], [496, 17], [200, 426], [232, 331], [240, 227], [86, 669], [50, 718]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [592]]
 b := ![[], [509, 296]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A719 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 719 3 where
 D := ![[161, 1], [701, 608, 1], [257, 669, 1]]; D' := ![[161, 1], [701, 608, 1], [257, 669, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9, 9]
 n := ![1, 2, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P719P0
  | 1 => exact P719P1
  | 2 => exact P719P2

def C7190 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A719.D 0) 719 where
  n := 1
  w := ![![719, 0, 0, 0, 0], ![161, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C7191 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A719.D 1) 719 where
  n := 2
  w := ![![719, 0, 0, 0, 0], ![701, 608, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C7192 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A719.D 2) 719 where
  n := 2
  w := ![![719, 0, 0, 0, 0], ![257, 669, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K719 : KummerData 719 ![I719N0, I719N1, I719N2] ![719, 516961, 516961] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A719
  C := by
    intro i
    match i with
    | 0 => exact C7190
    | 1 => exact C7191
    | 2 => exact C7192
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 719 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp727 : Fact (Nat.Prime 727) := {out := by norm_num}

def I727N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![727, 0, 0, 0, 0], ![342, 1, 0, 0, 0]] i)))

def I727N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![727, 0, 0, 0, 0], ![1227, 3147, 11539, -2268, 22728]] i)))

def P727P0 : CertificateIrreducibleZModOfList' 727 1 2 9 [342, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [372], [477], [], [197], [], [208], [346], [385, 1]]]
 h' := ![![[0, 1], [1], [441], [190], [237], [468], [110], [169], [644], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P727P1 : CertificateIrreducibleZModOfList' 727 4 2 9 [579, 660, 644, 385, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [318, 531, 615, 522], [22, 563, 58, 242], [2, 359, 54, 690], [0, 1]]
 g := ![![[346, 330, 307, 649], [688, 494, 711, 343], [376, 512, 500, 385], [565, 156, 687], [221, 414, 228, 111], [57, 675, 422], [504, 549], [342, 1], []], ![[244, 93, 643, 369, 317, 552], [416, 457, 114, 526, 54, 525], [268, 461, 164, 111, 717, 607], [479, 515, 571], [554, 562, 157, 369, 256, 520], [691, 287, 146], [16, 435, 558, 165, 433, 503], [147, 207, 183, 415, 579, 24], [561, 606, 586]], ![[403, 123, 682, 396, 713, 162], [178, 542, 490, 345, 203, 685], [285, 8, 206, 616, 630, 225], [263, 139, 686], [6, 599, 193, 702, 125, 322], [534, 391, 60], [425, 238, 472, 402, 383, 380], [482, 207, 416, 352, 481, 241], [185, 484, 404]], ![[576, 134, 425, 126, 390, 218], [216, 349, 20, 663, 326, 644], [521, 536, 519, 520, 351, 563], [648, 102, 353], [401, 8, 478, 64, 341, 101], [104, 367, 86], [443, 68, 571, 328, 692, 423], [61, 374, 628, 682, 39, 270], [469, 376, 642]]]
 h' := ![![[318, 531, 615, 522], [44, 491, 316, 244], [396, 376, 598, 528], [64, 630, 17, 333], [720, 725, 349, 651], [355, 142, 585, 609], [438, 349, 291, 379], [453, 525, 100], [0, 0, 1], [0, 1]], ![[22, 563, 58, 242], [368, 240, 598, 522], [570, 203, 359, 549], [636, 75, 121, 276], [560, 237, 25, 45], [511, 710, 277, 111], [101, 453, 666, 687], [483, 514, 352, 66], [221, 438, 39, 110], [318, 531, 615, 522]], ![[2, 359, 54, 690], [468, 717, 726, 594], [614, 570, 283, 641], [497, 568, 364, 279], [464, 623, 496, 443], [597, 513, 181, 381], [718, 287, 455, 327], [180, 31, 447, 352], [238, 476, 347, 725], [22, 563, 58, 242]], ![[0, 1], [509, 6, 541, 94], [53, 305, 214, 463], [228, 181, 225, 566], [403, 596, 584, 315], [140, 89, 411, 353], [200, 365, 42, 61], [253, 384, 555, 309], [351, 540, 340, 619], [2, 359, 54, 690]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [204, 448, 627], []]
 b := ![[], [], [348, 363, 127, 427], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A727 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 727 2 where
 D := ![[342, 1], [579, 660, 644, 385, 1]]; D' := ![[342, 1], [579, 660, 644, 385, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P727P0
  | 1 => exact P727P1

def C7270 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A727.D 0) 727 where
  n := 1
  w := ![![727, 0, 0, 0, 0], ![342, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C7271 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A727.D 1) 727 where
  n := 4
  w := ![![727, 0, 0, 0, 0], ![1227, 3147, 11539, -2268, 22728]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K727 : KummerData 727 ![I727N0, I727N1] ![727, 279342903841] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A727
  C := by
    intro i
    match i with
    | 0 => exact C7270
    | 1 => exact C7271
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 727 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp733 : Fact (Nat.Prime 733) := {out := by norm_num}

def I733N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![733, 0, 0, 0, 0], ![716, 1, 0, 0, 0]] i)))

def I733N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![733, 0, 0, 0, 0], ![1314, 2534, 11184, -3004, 22728]] i)))

def P733P0 : CertificateIrreducibleZModOfList' 733 1 2 9 [716, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [388], [588], [111], [], [563], [692], [17, 1]]]
 h' := ![![[0, 1], [1], [732], [467], [421], [298], [42], [36], [289], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P733P1 : CertificateIrreducibleZModOfList' 733 4 2 9 [666, 415, 289, 17, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [227, 545, 210, 71], [62, 615, 339, 697], [427, 305, 184, 698], [0, 1]]
 g := ![![[441, 156, 415, 260], [282, 312, 304], [236, 181, 370, 10], [730, 307, 28, 232], [119, 587, 640, 83], [145, 266, 492], [237, 471], [716, 1], []], ![[540, 204, 625, 671, 273, 21], [82, 344, 165], [243, 531, 673, 278, 418, 99], [353, 117, 219, 346, 126, 666], [52, 451, 303, 556, 603, 596], [649, 731, 49], [728, 711, 246, 314, 419, 603], [112, 445, 43, 707, 561, 523], [108, 564, 643]], ![[568, 576, 609, 37, 63, 454], [48, 62, 652], [37, 248, 100, 116, 423, 510], [669, 559, 223, 264, 650, 253], [662, 304, 409, 501, 437, 238], [634, 628, 459], [496, 311, 50, 558, 214, 466], [714, 281, 634, 653, 395, 490], [331, 472, 563]], ![[554, 135, 233, 718, 705, 702], [282, 693, 41], [714, 79, 375, 478, 312, 171], [20, 423, 628, 336, 670, 145], [157, 519, 668, 501, 446, 4], [283, 368, 204], [356, 538, 261, 361, 570, 64], [449, 75, 669, 631, 352, 492], [571, 13, 492]]]
 h' := ![![[227, 545, 210, 71], [210, 535, 713, 154], [419, 34, 387, 670], [532, 594, 197, 686], [643, 133, 377, 608], [356, 165, 536, 112], [486, 549, 228, 35], [327, 525, 100], [0, 0, 1], [0, 1]], ![[62, 615, 339, 697], [134, 420, 191, 444], [550, 81, 468, 178], [442, 349, 526, 166], [13, 154, 369, 469], [525, 333, 119, 301], [716, 257, 726, 726], [62, 587, 372, 303], [125, 707, 118, 246], [227, 545, 210, 71]], ![[427, 305, 184, 698], [229, 244, 319, 424], [573, 431, 70, 488], [194, 625, 30, 704], [728, 516, 543, 663], [661, 354, 272, 386], [652, 208, 661, 649], [575, 381, 658, 166], [366, 572, 52, 176], [62, 615, 339, 697]], ![[0, 1], [492, 267, 243, 444], [213, 187, 541, 130], [475, 631, 713, 643], [411, 663, 177, 459], [610, 614, 539, 667], [169, 452, 584, 56], [635, 706, 336, 264], [686, 187, 562, 311], [427, 305, 184, 698]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [697, 315, 399], []]
 b := ![[], [], [635, 145, 215, 683], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A733 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 733 2 where
 D := ![[716, 1], [666, 415, 289, 17, 1]]; D' := ![[716, 1], [666, 415, 289, 17, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P733P0
  | 1 => exact P733P1

def C7330 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A733.D 0) 733 where
  n := 1
  w := ![![733, 0, 0, 0, 0], ![716, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C7331 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A733.D 1) 733 where
  n := 4
  w := ![![733, 0, 0, 0, 0], ![1314, 2534, 11184, -3004, 22728]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K733 : KummerData 733 ![I733N0, I733N1] ![733, 288679469521] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A733
  C := by
    intro i
    match i with
    | 0 => exact C7330
    | 1 => exact C7331
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 733 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp739 : Fact (Nat.Prime 739) := {out := by norm_num}

def I739N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![739, 0, 0, 0, 0], ![64, 1, 0, 0, 0]] i)))

def I739N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![739, 0, 0, 0, 0], ![241, 312, 1, 0, 0]] i)))

def I739N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![739, 0, 0, 0, 0], ![710, 363, 1, 0, 0]] i)))

def P739P0 : CertificateIrreducibleZModOfList' 739 1 2 9 [64, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [612], [], [], [], [227], [283], [438], [675, 1]]]
 h' := ![![[0, 1], [738], [277], [283], [689], [252], [363], [50], [401], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P739P1 : CertificateIrreducibleZModOfList' 739 2 2 9 [241, 312, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [427, 738], [0, 1]]
 g := ![![[311, 46], [140, 351], [180], [610], [264], [353, 43], [427, 227], [461, 535], [1]], ![[0, 693], [0, 388], [180], [610], [264], [239, 696], [547, 512], [555, 204], [1]]]
 h' := ![![[427, 738], [254, 394], [170, 479], [156, 56], [284, 127], [651, 560], [553, 700], [488, 363], [498, 427], [0, 1]], ![[0, 1], [0, 345], [0, 260], [420, 683], [566, 612], [335, 179], [158, 39], [299, 376], [294, 312], [427, 738]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [205]]
 b := ![[], [471, 472]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P739P2 : CertificateIrreducibleZModOfList' 739 2 2 9 [710, 363, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [376, 738], [0, 1]]
 g := ![![[701, 688], [723, 173], [224], [624], [377], [97, 197], [87, 173], [5, 227], [1]], ![[0, 51], [0, 566], [224], [624], [377], [269, 542], [103, 566], [372, 512], [1]]]
 h' := ![![[376, 738], [275, 583], [122, 436], [456, 417], [344, 593], [596, 584], [306, 373], [145, 436], [29, 376], [0, 1]], ![[0, 1], [0, 156], [0, 303], [580, 322], [134, 146], [697, 155], [144, 366], [23, 303], [256, 363], [376, 738]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [530]]
 b := ![[], [432, 265]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A739 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 739 3 where
 D := ![[64, 1], [241, 312, 1], [710, 363, 1]]; D' := ![[64, 1], [241, 312, 1], [710, 363, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9, 9]
 n := ![1, 2, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P739P0
  | 1 => exact P739P1
  | 2 => exact P739P2

def C7390 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A739.D 0) 739 where
  n := 1
  w := ![![739, 0, 0, 0, 0], ![64, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C7391 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A739.D 1) 739 where
  n := 2
  w := ![![739, 0, 0, 0, 0], ![241, 312, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C7392 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A739.D 2) 739 where
  n := 2
  w := ![![739, 0, 0, 0, 0], ![710, 363, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K739 : KummerData 739 ![I739N0, I739N1, I739N2] ![739, 546121, 546121] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A739
  C := by
    intro i
    match i with
    | 0 => exact C7390
    | 1 => exact C7391
    | 2 => exact C7392
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 739 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp743 : Fact (Nat.Prime 743) := {out := by norm_num}

def I743N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![743, 0, 0, 0, 0], ![72, 1, 0, 0, 0]] i)))

def I743N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![743, 0, 0, 0, 0], ![145, 1, 0, 0, 0]] i)))

def I743N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![743, 0, 0, 0, 0], ![728, 1, 0, 0, 0]] i)))

def I743N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![743, 0, 0, 0, 0], ![184, 541, 1, 0, 0]] i)))

def P743P0 : CertificateIrreducibleZModOfList' 743 1 2 9 [72, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [258], [36], [], [], [106], [16], [289], [671, 1]]]
 h' := ![![[0, 1], [742], [380], [6], [682], [541], [334], [739], [726], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P743P1 : CertificateIrreducibleZModOfList' 743 1 2 9 [145, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [41], [338], [], [], [288], [340], [546], [598, 1]]]
 h' := ![![[0, 1], [742], [28], [583], [71], [591], [481], [331], [221], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P743P2 : CertificateIrreducibleZModOfList' 743 1 2 9 [728, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [99], [211], [], [], [256], [98], [101], [15, 1]]]
 h' := ![![[0, 1], [742], [193], [484], [22], [125], [727], [29], [225], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P743P3 : CertificateIrreducibleZModOfList' 743 2 2 9 [184, 541, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [202, 742], [0, 1]]
 g := ![![[540, 424], [365, 72], [274, 200], [164], [88], [226, 249], [484, 297], [273, 682], [1]], ![[0, 319], [49, 671], [552, 543], [164], [88], [0, 494], [295, 446], [582, 61], [1]]]
 h' := ![![[202, 742], [453, 75], [108, 612], [456, 466], [730, 56], [24, 250], [104, 588], [292, 664], [559, 202], [0, 1]], ![[0, 1], [0, 668], [394, 131], [227, 277], [154, 687], [0, 493], [0, 155], [680, 79], [498, 541], [202, 742]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [633]]
 b := ![[], [354, 688]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A743 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 743 4 where
 D := ![[72, 1], [145, 1], [728, 1], [184, 541, 1]]; D' := ![[72, 1], [145, 1], [728, 1], [184, 541, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9, 9, 9]
 n := ![1, 1, 1, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P743P0
  | 1 => exact P743P1
  | 2 => exact P743P2
  | 3 => exact P743P3

def C7430 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A743.D 0) 743 where
  n := 1
  w := ![![743, 0, 0, 0, 0], ![72, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C7431 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A743.D 1) 743 where
  n := 1
  w := ![![743, 0, 0, 0, 0], ![145, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C7432 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A743.D 2) 743 where
  n := 1
  w := ![![743, 0, 0, 0, 0], ![728, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C7433 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A743.D 3) 743 where
  n := 2
  w := ![![743, 0, 0, 0, 0], ![184, 541, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K743 : KummerData 743 ![I743N0, I743N1, I743N2, I743N3] ![743, 743, 743, 552049] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A743
  C := by
    intro i
    match i with
    | 0 => exact C7430
    | 1 => exact C7431
    | 2 => exact C7432
    | 3 => exact C7433
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 743 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp751 : Fact (Nat.Prime 751) := {out := by norm_num}

def I751N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![751, 0, 0, 0, 0], ![15771, 751, 751, 0, 0]] i)))

def P751P0 : CertificateIrreducibleZModOfList' 751 5 2 9 [51, 226, 651, 0, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [653, 654, 518, 646, 591], [669, 38, 115, 267, 30], [713, 264, 702, 32, 464], [218, 545, 167, 557, 417], [0, 1]]
 g := ![![[105, 152, 451, 663, 556], [344, 513, 65, 115, 23], [52, 172, 566, 441, 574], [691, 306, 183, 706, 601], [578, 313, 417, 208], [526, 668, 167, 711, 74], [237], [1], []], ![[470, 687, 348, 90, 630, 486, 688, 670], [164, 434, 443, 212, 278, 70, 77, 426], [94, 536, 673, 341, 748, 184, 275, 124], [731, 200, 336, 729, 259, 456, 413, 377], [375, 487, 468, 748], [70, 213, 109, 424, 42, 701, 259, 653], [618, 704, 32, 734, 534, 657, 647, 502], [294, 711, 411, 13, 575, 705, 741, 442], [205, 722, 556, 66]], ![[308, 310, 481, 530, 486, 305, 206, 521], [194, 632, 591, 630, 160, 548, 704, 108], [671, 653, 166, 290, 385, 89, 724, 562], [659, 516, 665, 319, 185, 222, 480, 619], [275, 269], [383, 42, 302, 9, 738, 384, 464, 564], [85, 606, 731, 130, 342, 458, 358, 675], [41, 354, 633, 62, 316, 460, 265, 497], [486, 85, 249, 149]], ![[44, 696, 79, 664, 504, 211, 386, 251], [207, 495, 730, 109, 704, 231, 187, 452], [570, 662, 481, 221, 457, 48, 23, 62], [400, 547, 439, 614, 301, 32, 441, 620], [255, 647, 203, 734], [416, 371, 347, 606, 435, 674, 471, 675], [363, 96, 741, 675, 74, 642, 485, 409], [420, 563, 651, 390, 328, 630, 447, 41], [717, 612, 407, 510]], ![[9, 460, 718, 518, 116, 337, 478, 314], [391, 73, 549, 700, 92, 363, 120, 646], [736, 430, 540, 491, 612, 311, 113, 202], [486, 551, 360, 318, 360, 559, 715, 702], [309, 298, 602, 437], [186, 308, 434, 172, 108, 132, 617, 626], [181, 104, 406, 565, 301, 700, 32, 455], [54, 72, 68, 577, 89, 94, 444, 306], [211, 429, 420, 408]]]
 h' := ![![[653, 654, 518, 646, 591], [480, 471, 158, 736, 53], [352, 636, 73, 704, 582], [56, 150, 693, 498, 152], [353, 310, 618, 85, 66], [210, 44, 334, 547, 380], [680, 107, 190, 322, 611], [700, 525, 100], [0, 0, 1], [0, 1]], ![[669, 38, 115, 267, 30], [225, 68, 335, 514, 434], [61, 332, 422, 223, 292], [88, 311, 174, 340, 339], [417, 140, 201, 521, 118], [747, 647, 632, 45, 606], [653, 83, 535, 449, 491], [81, 434, 428, 506, 378], [651, 446, 454, 699, 258], [653, 654, 518, 646, 591]], ![[713, 264, 702, 32, 464], [193, 346, 726, 0, 343], [703, 741, 668, 119, 595], [597, 310, 76, 206, 677], [738, 700, 57, 20, 280], [393, 278, 633, 613], [197, 562, 680, 530, 738], [412, 156, 642, 429, 390], [713, 508, 26, 450, 297], [669, 38, 115, 267, 30]], ![[218, 545, 167, 557, 417], [389, 543, 427, 581, 610], [541, 211, 351, 476, 362], [171, 93, 498, 362, 645], [700, 635, 137, 667, 227], [448, 127, 312, 643, 684], [438, 322, 697, 53, 110], [403, 20, 267, 259, 130], [174, 717, 320, 518, 344], [713, 264, 702, 32, 464]], ![[0, 1], [520, 74, 607, 422, 62], [595, 333, 739, 731, 422], [95, 638, 61, 96, 440], [690, 468, 489, 209, 60], [72, 406, 342, 405, 583], [43, 428, 151, 148, 303], [402, 367, 65, 308, 604], [715, 582, 701, 586, 603], [218, 545, 167, 557, 417]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [129, 79, 371, 587], [], [], []]
 b := ![[], [343, 601, 605, 250, 581], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A751 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 751 1 where
 D := ![[51, 226, 651, 0, 0, 1]]; D' := ![[51, 226, 651, 0, 0, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9]
 n := ![5]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P751P0

def C7510 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A751.D 0) 751 where
  n := 5
  w := ![![751, 0, 0, 0, 0], ![15771, 751, 751, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K751 : KummerData 751 ![I751N0] ![238890943128751] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A751
  C := by
    intro i
    match i with
    | 0 => exact C7510
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 751 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp757 : Fact (Nat.Prime 757) := {out := by norm_num}

def I757N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![757, 0, 0, 0, 0], ![203, 1, 0, 0, 0]] i)))

def I757N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![757, 0, 0, 0, 0], ![262, 1, 0, 0, 0]] i)))

def I757N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![757, 0, 0, 0, 0], ![322, 1, 0, 0, 0]] i)))

def I757N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![757, 0, 0, 0, 0], ![103, 727, 1, 0, 0]] i)))

def P757P0 : CertificateIrreducibleZModOfList' 757 1 2 9 [203, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [433], [], [322], [750], [524], [553], [554, 1]]]
 h' := ![![[0, 1], [756], [670], [52], [493], [664], [365], [534], [331], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P757P1 : CertificateIrreducibleZModOfList' 757 1 2 9 [262, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [9], [], [84], [754], [84], [3], [495, 1]]]
 h' := ![![[0, 1], [756], [670], [754], [702], [29], [702], [728], [514], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P757P2 : CertificateIrreducibleZModOfList' 757 1 2 9 [322, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [134], [], [326], [548], [432], [625], [435, 1]]]
 h' := ![![[0, 1], [1], [1], [170], [251], [682], [184], [112], [732], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P757P3 : CertificateIrreducibleZModOfList' 757 2 2 9 [103, 727, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 756], [0, 1]]
 g := ![![[132, 147], [367], [247, 507], [108], [119, 248], [39, 586], [665, 227], [381, 143], [1]], ![[0, 610], [367], [317, 250], [108], [746, 509], [208, 171], [662, 530], [129, 614], [1]]]
 h' := ![![[30, 756], [446, 187], [297, 424], [60, 626], [612, 56], [525, 608], [392, 612], [121, 497], [654, 30], [0, 1]], ![[0, 1], [0, 570], [148, 333], [672, 131], [21, 701], [597, 149], [584, 145], [648, 260], [40, 727], [30, 756]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [515]]
 b := ![[], [301, 636]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A757 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 757 4 where
 D := ![[203, 1], [262, 1], [322, 1], [103, 727, 1]]; D' := ![[203, 1], [262, 1], [322, 1], [103, 727, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9, 9, 9]
 n := ![1, 1, 1, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P757P0
  | 1 => exact P757P1
  | 2 => exact P757P2
  | 3 => exact P757P3

def C7570 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A757.D 0) 757 where
  n := 1
  w := ![![757, 0, 0, 0, 0], ![203, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C7571 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A757.D 1) 757 where
  n := 1
  w := ![![757, 0, 0, 0, 0], ![262, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C7572 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A757.D 2) 757 where
  n := 1
  w := ![![757, 0, 0, 0, 0], ![322, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C7573 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A757.D 3) 757 where
  n := 2
  w := ![![757, 0, 0, 0, 0], ![103, 727, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K757 : KummerData 757 ![I757N0, I757N1, I757N2, I757N3] ![757, 757, 757, 573049] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A757
  C := by
    intro i
    match i with
    | 0 => exact C7570
    | 1 => exact C7571
    | 2 => exact C7572
    | 3 => exact C7573
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 757 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp761 : Fact (Nat.Prime 761) := {out := by norm_num}

def I761N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![761, 0, 0, 0, 0], ![34, 1, 0, 0, 0]] i)))

def I761N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![761, 0, 0, 0, 0], ![705, 105, 1, 0, 0]] i)))

def I761N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![761, 0, 0, 0, 0], ![587, 622, 1, 0, 0]] i)))

def P761P0 : CertificateIrreducibleZModOfList' 761 1 2 9 [34, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [291], [401], [308], [473], [20], [727, 1]]]
 h' := ![![[0, 1], [1], [1], [760], [64], [182], [660], [81], [395], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P761P1 : CertificateIrreducibleZModOfList' 761 2 2 9 [705, 105, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [656, 760], [0, 1]]
 g := ![![[664, 341], [597], [671], [227, 125], [121, 328], [416, 561], [503, 636], [272, 371], [1]], ![[626, 420], [597], [671], [39, 636], [687, 433], [108, 200], [691, 125], [128, 390], [1]]]
 h' := ![![[656, 760], [246, 252], [686, 174], [536, 670], [688, 607], [466, 33], [11, 448], [12, 679], [56, 656], [0, 1]], ![[0, 1], [421, 509], [680, 587], [198, 91], [116, 154], [45, 728], [153, 313], [251, 82], [427, 105], [656, 760]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [651]]
 b := ![[], [537, 706]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P761P2 : CertificateIrreducibleZModOfList' 761 2 2 9 [587, 622, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [139, 760], [0, 1]]
 g := ![![[530, 139], [680], [230], [100, 162], [642, 291], [481, 654], [513, 395], [479, 296], [1]], ![[65, 622], [680], [230], [549, 599], [758, 470], [67, 107], [626, 366], [529, 465], [1]]]
 h' := ![![[139, 760], [681, 731], [403, 351], [658, 401], [602, 104], [745, 697], [225, 95], [397, 727], [174, 139], [0, 1]], ![[0, 1], [316, 30], [488, 410], [83, 360], [599, 657], [220, 64], [493, 666], [237, 34], [470, 622], [139, 760]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [224]]
 b := ![[], [587, 112]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A761 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 761 3 where
 D := ![[34, 1], [705, 105, 1], [587, 622, 1]]; D' := ![[34, 1], [705, 105, 1], [587, 622, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9, 9]
 n := ![1, 2, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P761P0
  | 1 => exact P761P1
  | 2 => exact P761P2

def C7610 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A761.D 0) 761 where
  n := 1
  w := ![![761, 0, 0, 0, 0], ![34, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C7611 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A761.D 1) 761 where
  n := 2
  w := ![![761, 0, 0, 0, 0], ![705, 105, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C7612 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A761.D 2) 761 where
  n := 2
  w := ![![761, 0, 0, 0, 0], ![587, 622, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K761 : KummerData 761 ![I761N0, I761N1, I761N2] ![761, 579121, 579121] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A761
  C := by
    intro i
    match i with
    | 0 => exact C7610
    | 1 => exact C7611
    | 2 => exact C7612
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 761 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


lemma PB18792I14_primes (p : ℕ) :
  p ∈ Set.range ![709, 719, 727, 733, 739, 743, 751, 757, 761] ↔ Nat.Prime p ∧ 701 < p ∧ p ≤ 761 := by
  rw [← List.mem_ofFn']
  convert primes_range 701 761 (by omega)
  decide

def PB18792I14 : PrimesBelowBoundCertificateInterval O 701 761 18792 where
  m := 9
  g := ![3, 3, 2, 2, 3, 4, 1, 4, 3]
  P := ![709, 719, 727, 733, 739, 743, 751, 757, 761]
  hP := PB18792I14_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I709N0, I709N1, I709N2]
    · exact ![I719N0, I719N1, I719N2]
    · exact ![I727N0, I727N1]
    · exact ![I733N0, I733N1]
    · exact ![I739N0, I739N1, I739N2]
    · exact ![I743N0, I743N1, I743N2, I743N3]
    · exact ![I751N0]
    · exact ![I757N0, I757N1, I757N2, I757N3]
    · exact ![I761N0, I761N1, I761N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · convert (containsPrimesAbove_of_KummerData K709) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K719) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K727) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K733) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K739) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K743) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K751) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K757) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K761) <;> rfl
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![709, 709, 356400829]
    · exact ![719, 516961, 516961]
    · exact ![727, 279342903841]
    · exact ![733, 288679469521]
    · exact ![739, 546121, 546121]
    · exact ![743, 743, 743, 552049]
    · exact ![238890943128751]
    · exact ![757, 757, 757, 573049]
    · exact ![761, 579121, 579121]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact (card_quot_of_KummerData K709)
    · exact (card_quot_of_KummerData K719)
    · exact (card_quot_of_KummerData K727)
    · exact (card_quot_of_KummerData K733)
    · exact (card_quot_of_KummerData K739)
    · exact (card_quot_of_KummerData K743)
    · exact (card_quot_of_KummerData K751)
    · exact (card_quot_of_KummerData K757)
    · exact (card_quot_of_KummerData K761)
  β := ![I709N0, I709N1, I719N0, I727N0, I733N0, I739N0, I743N0, I743N1, I743N2, I757N0, I757N1, I757N2, I761N0]
  Il := ![[I709N0, I709N1], [I719N0], [I727N0], [I733N0], [I739N0], [I743N0, I743N1, I743N2], [], [I757N0, I757N1, I757N2], [I761N0]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
