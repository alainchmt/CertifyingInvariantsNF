
import IdealArithmetic.Examples.NF5_1_281250000_1_K.RI5_1_281250000_1_K
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 

instance hp467 : Fact (Nat.Prime 467) := {out := by norm_num}

def I467N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![467, 0, 0, 0, 0], ![182, 1, 0, 0, 0]] i)))

def I467N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![467, 0, 0, 0, 0], ![296, 282, 414, 1425, 10]] i)))

def P467P0 : CertificateIrreducibleZModOfList' 467 1 2 8 [182, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [331], [], [], [430], [], [22], [434, 285, 1]]]
 h' := ![![[0, 1], [1], [407], [122], [196], [373], [199], [402], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P467P1 : CertificateIrreducibleZModOfList' 467 4 2 8 [296, 282, 409, 285, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [422, 172, 274, 338], [171, 204, 97, 145], [56, 90, 96, 451], [0, 1]]
 g := ![![[393, 380, 320, 435], [162, 114, 58, 434], [157, 359, 351], [403, 302, 256], [200, 248, 262, 331], [335, 188, 58], [347, 25, 182, 1], []], ![[340, 307, 305, 329, 303, 78], [8, 437, 442, 346, 227, 375], [330, 309, 155], [453, 16, 55], [438, 426, 0, 159, 203, 168], [337, 227, 276], [418, 182, 337, 317, 211, 261], [368, 396, 346, 411, 411, 110]], ![[73, 229, 221, 158, 458, 196], [310, 343, 395, 42, 63, 270], [356, 245, 432], [236, 265, 267], [315, 452, 247, 377, 122, 38], [342, 390, 64], [233, 414, 419, 118, 303, 222], [104, 179, 118, 42, 153, 49]], ![[82, 188, 181, 99, 207, 259], [40, 1, 223, 25, 167, 263], [38, 430, 159], [454, 106, 385], [399, 432, 329, 4, 225, 355], [459, 148, 229], [109, 368, 208, 33, 213, 142], [9, 230, 39, 410, 269, 107]]]
 h' := ![![[422, 172, 274, 338], [149, 91, 283, 430], [237, 206, 458, 182], [3, 373, 453, 384], [109, 254, 425, 451], [161, 39, 422, 407], [28, 288, 300, 375], [0, 0, 0, 1], [0, 1]], ![[171, 204, 97, 145], [298, 346, 237, 405], [353, 66, 349, 354], [94, 182, 260, 434], [401, 212, 189, 191], [338, 216, 155, 263], [95, 152, 236, 273], [290, 120, 233, 298], [422, 172, 274, 338]], ![[56, 90, 96, 451], [176, 429, 20, 177], [175, 458, 166, 356], [464, 59, 43, 343], [175, 277, 29, 141], [300, 115, 291, 317], [367, 334, 172, 8], [80, 399, 43, 304], [171, 204, 97, 145]], ![[0, 1], [259, 68, 394, 389], [190, 204, 428, 42], [70, 320, 178, 240], [357, 191, 291, 151], [242, 97, 66, 414], [441, 160, 226, 278], [162, 415, 191, 331], [56, 90, 96, 451]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [275, 265, 18], []]
 b := ![[], [], [204, 405, 263, 206], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A467 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 467 2 where
 D := ![[182, 1], [296, 282, 409, 285, 1]]; D' := ![[182, 1], [296, 282, 409, 285, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8, 8]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P467P0
  | 1 => exact P467P1

def C4670 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A467.D 0) 467 where
  n := 1
  w := ![![467, 0, 0, 0, 0], ![182, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C4671 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A467.D 1) 467 where
  n := 4
  w := ![![467, 0, 0, 0, 0], ![296, 282, 414, 1425, 10]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K467 : KummerData 467 ![I467N0, I467N1] ![467, 47562811921] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A467
  C := by
    intro i
    match i with
    | 0 => exact C4670
    | 1 => exact C4671
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 467 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp479 : Fact (Nat.Prime 479) := {out := by norm_num}

def I479N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![479, 0, 0, 0, 0], ![152, 1, 0, 0, 0]] i)))

def I479N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![479, 0, 0, 0, 0], ![160, 1, 0, 0, 0]] i)))

def I479N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![479, 0, 0, 0, 0], ![284, 191, 167, 5, 0]] i)))

def P479P0 : CertificateIrreducibleZModOfList' 479 1 2 8 [152, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [375], [180], [163], [151], [], [21], [112, 327, 1]]]
 h' := ![![[0, 1], [1], [422], [132], [40], [55], [161], [220], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P479P1 : CertificateIrreducibleZModOfList' 479 1 2 8 [160, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [3], [386], [11], [305], [], [251], [213, 319, 1]]]
 h' := ![![[0, 1], [478], [31], [156], [58], [28], [76], [408], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P479P2 : CertificateIrreducibleZModOfList' 479 3 2 8 [284, 191, 167, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [172, 433, 13], [140, 45, 466], [0, 1]]
 g := ![![[276, 97, 98], [258, 78, 167], [352, 389, 441], [202, 165, 436], [126, 252, 243], [463, 151], [45, 420, 107], [1]], ![[477, 53, 392, 476], [211, 223, 394, 94], [193, 203, 344, 177], [448, 306, 170, 68], [118, 202, 134, 439], [370, 288], [193, 152, 290, 473], [279, 54, 164, 281]], ![[375, 371, 434, 251], [374, 45, 223, 42], [49, 361, 217, 105], [93, 116, 204, 206], [377, 104, 320, 147], [8, 115], [427, 208, 106, 27], [5, 142, 287, 198]]]
 h' := ![![[172, 433, 13], [15, 272, 128], [143, 91, 330], [112, 62, 458], [141, 188, 389], [171, 429, 200], [153, 202, 424], [195, 288, 312], [0, 1]], ![[140, 45, 466], [252, 295, 195], [460, 354, 226], [147, 125, 340], [473, 347, 310], [421, 247, 207], [11, 170, 151], [309, 276, 61], [172, 433, 13]], ![[0, 1], [105, 391, 156], [217, 34, 402], [288, 292, 160], [348, 423, 259], [213, 282, 72], [367, 107, 383], [305, 394, 106], [140, 45, 466]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [208, 198], []]
 b := ![[], [350, 78, 169], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A479 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 479 3 where
 D := ![[152, 1], [160, 1], [284, 191, 167, 1]]; D' := ![[152, 1], [160, 1], [284, 191, 167, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8, 8, 8]
 n := ![1, 1, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P479P0
  | 1 => exact P479P1
  | 2 => exact P479P2

def C4790 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A479.D 0) 479 where
  n := 1
  w := ![![479, 0, 0, 0, 0], ![152, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C4791 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A479.D 1) 479 where
  n := 1
  w := ![![479, 0, 0, 0, 0], ![160, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C4792 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A479.D 2) 479 where
  n := 3
  w := ![![479, 0, 0, 0, 0], ![284, 191, 167, 5, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K479 : KummerData 479 ![I479N0, I479N1, I479N2] ![479, 479, 109902239] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A479
  C := by
    intro i
    match i with
    | 0 => exact C4790
    | 1 => exact C4791
    | 2 => exact C4792
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 479 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp487 : Fact (Nat.Prime 487) := {out := by norm_num}

def I487N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![487, 0, 0, 0, 0], ![268, 187, 1, 0, 0]] i)))

def I487N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![487, 0, 0, 0, 0], ![435, 99, 300, 5, 0]] i)))

def P487P0 : CertificateIrreducibleZModOfList' 487 2 2 8 [268, 187, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [300, 486], [0, 1]]
 g := ![![[435, 169], [298, 332], [51, 297], [137], [362], [141, 141], [464, 279], [300, 1]], ![[0, 318], [63, 155], [30, 190], [137], [362], [72, 346], [400, 208], [113, 486]]]
 h' := ![![[300, 486], [4, 474], [455, 258], [210, 28], [141, 293], [198, 259], [320, 221], [442, 124], [0, 1]], ![[0, 1], [0, 13], [422, 229], [331, 459], [381, 194], [465, 228], [388, 266], [143, 363], [300, 486]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [106]]
 b := ![[], [329, 53]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P487P1 : CertificateIrreducibleZModOfList' 487 3 2 8 [435, 99, 300, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [185, 360, 359], [2, 126, 128], [0, 1]]
 g := ![![[425, 28, 248], [270, 220, 49], [111, 74, 459], [105, 362], [34, 161], [430, 378, 62], [257, 240, 392], [1]], ![[384, 299, 472, 436], [263, 310, 199, 243], [213, 467, 87, 317], [369, 70], [410, 401], [413, 472, 70, 287], [389, 312, 300, 478], [252, 275, 102, 357]], ![[460, 64, 259, 334], [47, 304, 61, 297], [340, 55, 140, 313], [306, 424], [316, 322], [87, 113, 216, 419], [209, 34, 288, 394], [42, 460, 420, 130]]]
 h' := ![![[185, 360, 359], [404, 121, 380], [415, 370, 7], [135, 17, 414], [123, 239, 259], [445, 422, 310], [215, 455, 297], [52, 388, 187], [0, 1]], ![[2, 126, 128], [90, 76, 250], [445, 17, 274], [78, 330, 314], [394, 23, 94], [263, 207, 141], [44, 482, 123], [93, 253, 196], [185, 360, 359]], ![[0, 1], [152, 290, 344], [318, 100, 206], [410, 140, 246], [313, 225, 134], [399, 345, 36], [398, 37, 67], [244, 333, 104], [2, 126, 128]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [376, 22], []]
 b := ![[], [82, 275, 23], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A487 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 487 2 where
 D := ![[268, 187, 1], [435, 99, 300, 1]]; D' := ![[268, 187, 1], [435, 99, 300, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8, 8]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P487P0
  | 1 => exact P487P1

def C4870 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A487.D 0) 487 where
  n := 2
  w := ![![487, 0, 0, 0, 0], ![268, 187, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C4871 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A487.D 1) 487 where
  n := 3
  w := ![![487, 0, 0, 0, 0], ![435, 99, 300, 5, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K487 : KummerData 487 ![I487N0, I487N1] ![237169, 115501303] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A487
  C := by
    intro i
    match i with
    | 0 => exact C4870
    | 1 => exact C4871
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 487 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp491 : Fact (Nat.Prime 491) := {out := by norm_num}

def I491N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![491, 0, 0, 0, 0], ![44, 1, 0, 0, 0]] i)))

def I491N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![491, 0, 0, 0, 0], ![401, 1, 0, 0, 0]] i)))

def I491N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![491, 0, 0, 0, 0], ![439, 159, 46, 5, 0]] i)))

def P491P0 : CertificateIrreducibleZModOfList' 491 1 2 8 [44, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [279], [], [229], [], [425], [143], [463, 447, 1]]]
 h' := ![![[0, 1], [490], [233], [235], [291], [449], [91], [250], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P491P1 : CertificateIrreducibleZModOfList' 491 1 2 8 [401, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [60], [], [129], [], [355], [58], [244, 90, 1]]]
 h' := ![![[0, 1], [490], [325], [317], [243], [35], [310], [356], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P491P2 : CertificateIrreducibleZModOfList' 491 3 2 8 [439, 159, 46, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [265, 112, 397], [180, 378, 94], [0, 1]]
 g := ![![[430, 285, 117], [137, 290, 64], [289, 71], [305, 76, 123], [321, 17], [439, 312, 233], [66, 271, 152], [1]], ![[73, 34, 433, 247], [484, 393, 435, 423], [455, 147], [236, 326, 207, 73], [225, 152], [447, 136, 188, 137], [358, 7, 190, 317], [357, 266, 9, 188]], ![[446, 148, 174, 375], [347, 240, 101, 240], [7, 85], [184, 397, 217, 461], [87, 174], [84, 230, 45, 45], [21, 433, 5, 238], [402, 336, 488, 303]]]
 h' := ![![[265, 112, 397], [250, 327, 92], [107, 473, 483], [148, 151, 215], [133, 158, 245], [242, 458, 80], [486, 410, 235], [52, 332, 445], [0, 1]], ![[180, 378, 94], [4, 246, 110], [33, 208, 141], [374, 350, 300], [316, 159, 180], [20, 87, 445], [160, 230, 208], [140, 381, 13], [265, 112, 397]], ![[0, 1], [133, 409, 289], [373, 301, 358], [3, 481, 467], [130, 174, 66], [486, 437, 457], [389, 342, 48], [184, 269, 33], [180, 378, 94]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [224, 436], []]
 b := ![[], [333, 223, 130], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A491 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 491 3 where
 D := ![[44, 1], [401, 1], [439, 159, 46, 1]]; D' := ![[44, 1], [401, 1], [439, 159, 46, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8, 8, 8]
 n := ![1, 1, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P491P0
  | 1 => exact P491P1
  | 2 => exact P491P2

def C4910 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A491.D 0) 491 where
  n := 1
  w := ![![491, 0, 0, 0, 0], ![44, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C4911 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A491.D 1) 491 where
  n := 1
  w := ![![491, 0, 0, 0, 0], ![401, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C4912 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A491.D 2) 491 where
  n := 3
  w := ![![491, 0, 0, 0, 0], ![439, 159, 46, 5, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K491 : KummerData 491 ![I491N0, I491N1, I491N2] ![491, 491, 118370771] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A491
  C := by
    intro i
    match i with
    | 0 => exact C4910
    | 1 => exact C4911
    | 2 => exact C4912
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 491 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp499 : Fact (Nat.Prime 499) := {out := by norm_num}

def I499N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![499, 0, 0, 0, 0], ![89, 1, 0, 0, 0]] i)))

def I499N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![499, 0, 0, 0, 0], ![475, 1, 0, 0, 0]] i)))

def I499N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![499, 0, 0, 0, 0], ![216, 348, 434, 5, 0]] i)))

def P499P0 : CertificateIrreducibleZModOfList' 499 1 2 8 [89, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [342], [], [], [402], [57], [451], [436, 410, 1]]]
 h' := ![![[0, 1], [1], [29], [45], [150], [416], [280], [118], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P499P1 : CertificateIrreducibleZModOfList' 499 1 2 8 [475, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [104], [], [], [36], [125], [447], [77, 24, 1]]]
 h' := ![![[0, 1], [1], [64], [491], [365], [6], [249], [351], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P499P2 : CertificateIrreducibleZModOfList' 499 3 2 8 [216, 348, 434, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [283, 344, 466], [281, 154, 33], [0, 1]]
 g := ![![[1, 444, 482], [358, 108, 118], [70, 100], [411, 150], [441, 325, 328], [5, 202, 276], [368, 344, 233], [1]], ![[289, 245, 424, 62], [285, 241, 305, 398], [347, 287], [242, 439], [203, 225, 161, 392], [378, 287, 397, 112], [375, 251, 429, 232], [362, 222, 14, 490]], ![[122, 438], [460, 132, 284, 279], [404, 364], [394, 187], [166, 373, 275, 299], [272, 18, 372, 292], [144, 366, 369, 20], [275, 125, 212, 9]]]
 h' := ![![[283, 344, 466], [17, 60, 383], [209, 391, 169], [360, 72, 489], [53, 121, 347], [417, 189, 223], [352, 475, 224], [283, 151, 65], [0, 1]], ![[281, 154, 33], [388, 375, 116], [93, 85, 149], [368, 24, 76], [350, 444, 44], [328, 143, 161], [304, 403, 358], [259, 206, 37], [283, 344, 466]], ![[0, 1], [368, 64], [387, 23, 181], [181, 403, 433], [153, 433, 108], [360, 167, 115], [417, 120, 416], [486, 142, 397], [281, 154, 33]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [366, 77], []]
 b := ![[], [299, 423, 335], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A499 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 499 3 where
 D := ![[89, 1], [475, 1], [216, 348, 434, 1]]; D' := ![[89, 1], [475, 1], [216, 348, 434, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8, 8, 8]
 n := ![1, 1, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P499P0
  | 1 => exact P499P1
  | 2 => exact P499P2

def C4990 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A499.D 0) 499 where
  n := 1
  w := ![![499, 0, 0, 0, 0], ![89, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C4991 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A499.D 1) 499 where
  n := 1
  w := ![![499, 0, 0, 0, 0], ![475, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C4992 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A499.D 2) 499 where
  n := 3
  w := ![![499, 0, 0, 0, 0], ![216, 348, 434, 5, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K499 : KummerData 499 ![I499N0, I499N1, I499N2] ![499, 499, 124251499] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A499
  C := by
    intro i
    match i with
    | 0 => exact C4990
    | 1 => exact C4991
    | 2 => exact C4992
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 499 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp503 : Fact (Nat.Prime 503) := {out := by norm_num}

def I503N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![503, 0, 0, 0, 0], ![15, 1, 0, 0, 0]] i)))

def I503N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![503, 0, 0, 0, 0], ![358, 1, 0, 0, 0]] i)))

def I503N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![503, 0, 0, 0, 0], ![478, 1, 0, 0, 0]] i)))

def I503N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![503, 0, 0, 0, 0], ![290, 155, 1, 0, 0]] i)))

def P503P0 : CertificateIrreducibleZModOfList' 503 1 2 8 [15, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [67], [112], [], [394], [56], [190], [225, 488, 1]]]
 h' := ![![[0, 1], [1], [332], [283], [126], [166], [168], [146], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P503P1 : CertificateIrreducibleZModOfList' 503 1 2 8 [358, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [392], [23], [], [378], [301], [346], [402, 145, 1]]]
 h' := ![![[0, 1], [1], [317], [289], [486], [387], [373], [445], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P503P2 : CertificateIrreducibleZModOfList' 503 1 2 8 [478, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [161], [169], [], [300], [294], [18], [122, 25, 1]]]
 h' := ![![[0, 1], [1], [201], [13], [458], [308], [450], [32], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P503P3 : CertificateIrreducibleZModOfList' 503 2 2 8 [290, 155, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [348, 502], [0, 1]]
 g := ![![[200, 196], [218, 300], [88, 78], [493], [232, 438], [189, 462], [289, 285], [348, 1]], ![[0, 307], [497, 203], [70, 425], [493], [247, 65], [5, 41], [378, 218], [193, 502]]]
 h' := ![![[348, 502], [158, 14], [133, 308], [179, 197], [122, 281], [17, 465], [191, 105], [183, 94], [0, 1]], ![[0, 1], [0, 489], [178, 195], [327, 306], [328, 222], [374, 38], [12, 398], [200, 409], [348, 502]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [433]]
 b := ![[], [54, 468]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A503 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 503 4 where
 D := ![[15, 1], [358, 1], [478, 1], [290, 155, 1]]; D' := ![[15, 1], [358, 1], [478, 1], [290, 155, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8, 8, 8, 8]
 n := ![1, 1, 1, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P503P0
  | 1 => exact P503P1
  | 2 => exact P503P2
  | 3 => exact P503P3

def C5030 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A503.D 0) 503 where
  n := 1
  w := ![![503, 0, 0, 0, 0], ![15, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C5031 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A503.D 1) 503 where
  n := 1
  w := ![![503, 0, 0, 0, 0], ![358, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C5032 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A503.D 2) 503 where
  n := 1
  w := ![![503, 0, 0, 0, 0], ![478, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C5033 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A503.D 3) 503 where
  n := 2
  w := ![![503, 0, 0, 0, 0], ![290, 155, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K503 : KummerData 503 ![I503N0, I503N1, I503N2, I503N3] ![503, 503, 503, 253009] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A503
  C := by
    intro i
    match i with
    | 0 => exact C5030
    | 1 => exact C5031
    | 2 => exact C5032
    | 3 => exact C5033
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 503 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp509 : Fact (Nat.Prime 509) := {out := by norm_num}

def I509N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![509, 0, 0, 0, 0], ![509, 0, 0, 2545, 0]] i)))

def P509P0 : CertificateIrreducibleZModOfList' 509 5 2 8 [209, 250, 0, 484, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [436, 411, 381, 129, 363], [1, 60, 285, 496, 340], [222, 206, 501, 101, 384], [359, 340, 360, 292, 440], [0, 1]]
 g := ![![[334, 320, 128, 195, 37], [497, 284, 262, 107], [126, 425, 486, 204, 388], [97, 452, 63, 212, 355], [100, 74, 381, 102, 500], [259, 22, 141], [25, 0, 1], []], ![[317, 479, 474, 462, 397, 285, 321, 267], [53, 437, 272, 455], [304, 264, 74, 320, 385, 265, 418, 323], [243, 247, 295, 68, 483, 4, 435, 163], [202, 117, 473, 478, 132, 186, 92, 339], [57, 477, 10, 59, 117, 275, 56, 47], [211, 131, 307, 461, 73, 149, 248, 117], [126, 473, 467, 109, 151, 311, 438, 399]], ![[393, 360, 259, 242, 273, 53, 353, 23], [25, 241, 211, 442], [106, 421, 441, 411, 319, 168, 144, 389], [313, 345, 361, 412, 476, 293, 130, 324], [492, 102, 119, 146, 225, 215, 498, 328], [59, 13, 347, 468, 328, 471, 119, 383], [211, 46, 501, 152, 152, 449, 197, 141], [329, 341, 136, 256, 275, 141, 322, 38]], ![[475, 105, 342, 364, 491, 210, 142, 417], [127, 171, 373, 335], [65, 184, 153, 406, 5, 72, 281, 20], [316, 395, 413, 219, 448, 241, 117, 492], [245, 125, 411, 17, 145, 432, 226, 57], [370, 255, 476, 3, 184, 448, 332, 85], [412, 222, 416, 212, 72, 439, 430, 97], [182, 461, 310, 77, 464, 138, 166, 417]], ![[147, 279, 360, 41, 170, 13, 181, 296], [137, 361, 85, 85], [288, 2, 62, 459, 287, 83, 337, 451], [97, 158, 37, 500, 14, 262, 178, 433], [393, 213, 328, 330, 474, 492, 428, 77], [273, 276, 283, 339, 44, 123, 374, 15], [232, 482, 200, 326, 297, 130, 346, 277], [462, 108, 78, 447, 346, 388, 399, 305]]]
 h' := ![![[436, 411, 381, 129, 363], [104, 356, 254, 447, 60], [134, 242, 434, 166, 427], [87, 331, 42, 61, 252], [478, 25, 155, 66, 125], [332, 286, 317, 482, 394], [374, 367, 300, 375], [0, 0, 0, 1], [0, 1]], ![[1, 60, 285, 496, 340], [273, 356, 144, 277, 496], [212, 508, 194, 125, 392], [180, 208, 287, 337, 476], [23, 375, 247, 212, 472], [408, 406, 107, 73, 68], [170, 273, 97, 37, 289], [502, 432, 228, 218, 433], [436, 411, 381, 129, 363]], ![[222, 206, 501, 101, 384], [135, 375, 415, 346, 17], [86, 503, 455, 66, 98], [129, 190, 187, 406, 100], [251, 122, 228, 38, 288], [292, 224, 457, 347, 265], [173, 85, 322, 221, 417], [464, 379, 290, 52, 401], [1, 60, 285, 496, 340]], ![[359, 340, 360, 292, 440], [507, 456, 477, 306, 384], [40, 54, 384, 494, 276], [342, 118, 420, 145, 324], [51, 316, 126, 396, 7], [410, 110, 121, 318, 452], [65, 460, 36, 263, 456], [230, 132, 397, 473, 425], [222, 206, 501, 101, 384]], ![[0, 1], [224, 493, 237, 151, 61], [380, 220, 60, 167, 334], [154, 171, 82, 69, 375], [376, 180, 262, 306, 126], [43, 501, 16, 307, 348], [309, 342, 263, 122, 365], [331, 75, 103, 274, 268], [359, 340, 360, 292, 440]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [72, 386, 116, 352], [], [], []]
 b := ![[], [492, 294, 44, 308, 107], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A509 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 509 1 where
 D := ![[209, 250, 0, 484, 0, 1]]; D' := ![[209, 250, 0, 484, 0, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8]
 n := ![5]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P509P0

def C5090 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A509.D 0) 509 where
  n := 5
  w := ![![509, 0, 0, 0, 0], ![509, 0, 0, 2545, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K509 : KummerData 509 ![I509N0] ![34165588961549] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A509
  C := by
    intro i
    match i with
    | 0 => exact C5090
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 509 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp521 : Fact (Nat.Prime 521) := {out := by norm_num}

def I521N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![521, 0, 0, 0, 0], ![22, 1, 0, 0, 0]] i)))

def I521N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![521, 0, 0, 0, 0], ![106, 82, 1, 0, 0]] i)))

def I521N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![521, 0, 0, 0, 0], ![24, 417, 1, 0, 0]] i)))

def P521P0 : CertificateIrreducibleZModOfList' 521 1 2 9 [22, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [450], [], [], [], [], [499, 1]]]
 h' := ![![[0, 1], [1], [1], [520], [433], [267], [124], [327], [484], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P521P1 : CertificateIrreducibleZModOfList' 521 2 2 9 [106, 82, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [439, 520], [0, 1]]
 g := ![![[335, 290], [263], [236], [414, 377], [142], [69], [118], [472], [1]], ![[0, 231], [263], [236], [239, 144], [142], [69], [118], [472], [1]]]
 h' := ![![[439, 520], [118, 281], [325, 28], [401, 310], [58, 306], [1, 244], [208, 177], [279, 41], [415, 439], [0, 1]], ![[0, 1], [0, 240], [113, 493], [510, 211], [495, 215], [312, 277], [282, 344], [43, 480], [366, 82], [439, 520]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [217]]
 b := ![[], [20, 369]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P521P2 : CertificateIrreducibleZModOfList' 521 2 2 9 [24, 417, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [104, 520], [0, 1]]
 g := ![![[343, 284], [438], [402], [368, 266], [489], [517], [176], [396], [1]], ![[182, 237], [438], [402], [419, 255], [489], [517], [176], [396], [1]]]
 h' := ![![[104, 520], [372, 320], [355, 312], [25, 483], [238, 74], [184, 131], [296, 470], [450, 243], [497, 104], [0, 1]], ![[0, 1], [308, 201], [501, 209], [241, 38], [119, 447], [262, 390], [202, 51], [193, 278], [372, 417], [104, 520]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [389]]
 b := ![[], [306, 455]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A521 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 521 3 where
 D := ![[22, 1], [106, 82, 1], [24, 417, 1]]; D' := ![[22, 1], [106, 82, 1], [24, 417, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9, 9]
 n := ![1, 2, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P521P0
  | 1 => exact P521P1
  | 2 => exact P521P2

def C5210 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A521.D 0) 521 where
  n := 1
  w := ![![521, 0, 0, 0, 0], ![22, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C5211 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A521.D 1) 521 where
  n := 2
  w := ![![521, 0, 0, 0, 0], ![106, 82, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C5212 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A521.D 2) 521 where
  n := 2
  w := ![![521, 0, 0, 0, 0], ![24, 417, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K521 : KummerData 521 ![I521N0, I521N1, I521N2] ![521, 271441, 271441] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A521
  C := by
    intro i
    match i with
    | 0 => exact C5210
    | 1 => exact C5211
    | 2 => exact C5212
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 521 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp523 : Fact (Nat.Prime 523) := {out := by norm_num}

def I523N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![523, 0, 0, 0, 0], ![312, 1, 0, 0, 0]] i)))

def I523N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![523, 0, 0, 0, 0], ![341, 283, 46, 1055, 10]] i)))

def P523P0 : CertificateIrreducibleZModOfList' 523 1 2 9 [312, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [290], [], [168], [], [], [], [], [211, 1]]]
 h' := ![![[0, 1], [522], [381], [407], [313], [275], [296], [172], [66], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P523P1 : CertificateIrreducibleZModOfList' 523 4 2 9 [341, 283, 41, 211, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [265, 408, 51, 356], [510, 18, 399, 156], [60, 96, 73, 11], [0, 1]]
 g := ![![[171, 298, 202, 461], [451, 24, 107, 436], [481, 359, 435], [203, 386, 212, 160], [152, 238, 290], [118, 4, 461], [193, 238, 66], [1], []], ![[336, 404, 281, 182, 413, 16], [186, 84, 419, 491, 189, 290], [351, 198, 60], [5, 456, 365, 34, 114, 158], [112, 220, 158], [7, 79, 280], [93, 262, 60], [32, 76, 280], [401, 442, 170]], ![[53, 431, 22, 451, 125, 363], [103, 364, 299, 351, 201, 452], [317, 44, 324], [149, 365, 177, 412, 125, 504], [458, 138, 335], [463, 65, 130], [394, 283, 318], [492, 168, 201], [407, 455, 278]], ![[235, 194, 241, 33, 215, 303], [404, 53, 495, 337, 295, 137], [489, 302, 466], [353, 264, 100, 423, 218, 203], [141, 377, 201], [425, 370, 100], [206, 112, 122], [452, 279, 296], [44, 133, 121]]]
 h' := ![![[265, 408, 51, 356], [494, 68, 324, 148], [129, 265, 371, 91], [336, 182, 393, 64], [305, 233, 478, 285], [166, 140, 150, 142], [260, 222, 341, 148], [182, 240, 482, 312], [0, 0, 1], [0, 1]], ![[510, 18, 399, 156], [116, 362, 155, 342], [437, 163, 382, 112], [19, 101, 234, 61], [347, 491, 408, 343], [166, 126, 295, 415], [375, 386, 98, 43], [205, 144, 117, 462], [428, 151, 273, 480], [265, 408, 51, 356]], ![[60, 96, 73, 11], [160, 497, 35, 362], [273, 133, 142, 259], [307, 474, 308, 505], [200, 189, 16, 207], [1, 305, 304, 181], [148, 432, 318, 322], [117, 294, 272, 494], [500, 110, 217, 215], [510, 18, 399, 156]], ![[0, 1], [74, 119, 9, 194], [26, 485, 151, 61], [375, 289, 111, 416], [178, 133, 144, 211], [265, 475, 297, 308], [354, 6, 289, 10], [97, 368, 175, 301], [102, 262, 32, 351], [60, 96, 73, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [75, 91, 190], []]
 b := ![[], [], [358, 505, 263, 153], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A523 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 523 2 where
 D := ![[312, 1], [341, 283, 41, 211, 1]]; D' := ![[312, 1], [341, 283, 41, 211, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P523P0
  | 1 => exact P523P1

def C5230 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A523.D 0) 523 where
  n := 1
  w := ![![523, 0, 0, 0, 0], ![312, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C5231 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A523.D 1) 523 where
  n := 4
  w := ![![523, 0, 0, 0, 0], ![341, 283, 46, 1055, 10]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K523 : KummerData 523 ![I523N0, I523N1] ![523, 74818113841] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A523
  C := by
    intro i
    match i with
    | 0 => exact C5230
    | 1 => exact C5231
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 523 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


lemma PB1045I10_primes (p : ℕ) :
  p ∈ Set.range ![467, 479, 487, 491, 499, 503, 509, 521, 523] ↔ Nat.Prime p ∧ 463 < p ∧ p ≤ 523 := by
  rw [← List.mem_ofFn']
  convert primes_range 463 523 (by omega)
  decide

def PB1045I10 : PrimesBelowBoundCertificateInterval O 463 523 1045 where
  m := 9
  g := ![2, 3, 2, 3, 3, 4, 1, 3, 2]
  P := ![467, 479, 487, 491, 499, 503, 509, 521, 523]
  hP := PB1045I10_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I467N0, I467N1]
    · exact ![I479N0, I479N1, I479N2]
    · exact ![I487N0, I487N1]
    · exact ![I491N0, I491N1, I491N2]
    · exact ![I499N0, I499N1, I499N2]
    · exact ![I503N0, I503N1, I503N2, I503N3]
    · exact ![I509N0]
    · exact ![I521N0, I521N1, I521N2]
    · exact ![I523N0, I523N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · convert (containsPrimesAbove_of_KummerData K467) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K479) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K487) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K491) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K499) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K503) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K509) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K521) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K523) <;> rfl
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![467, 47562811921]
    · exact ![479, 479, 109902239]
    · exact ![237169, 115501303]
    · exact ![491, 491, 118370771]
    · exact ![499, 499, 124251499]
    · exact ![503, 503, 503, 253009]
    · exact ![34165588961549]
    · exact ![521, 271441, 271441]
    · exact ![523, 74818113841]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact (card_quot_of_KummerData K467)
    · exact (card_quot_of_KummerData K479)
    · exact (card_quot_of_KummerData K487)
    · exact (card_quot_of_KummerData K491)
    · exact (card_quot_of_KummerData K499)
    · exact (card_quot_of_KummerData K503)
    · exact (card_quot_of_KummerData K509)
    · exact (card_quot_of_KummerData K521)
    · exact (card_quot_of_KummerData K523)
  β := ![I467N0, I479N0, I479N1, I491N0, I491N1, I499N0, I499N1, I503N0, I503N1, I503N2, I521N0, I523N0]
  Il := ![[I467N0], [I479N0, I479N1], [], [I491N0, I491N1], [I499N0, I499N1], [I503N0, I503N1, I503N2], [], [I521N0], [I523N0]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
