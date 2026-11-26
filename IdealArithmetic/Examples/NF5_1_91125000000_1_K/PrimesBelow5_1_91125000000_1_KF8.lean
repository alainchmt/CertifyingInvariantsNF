
import IdealArithmetic.Examples.NF5_1_91125000000_1_K.RI5_1_91125000000_1_K
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 

instance hp367 : Fact (Nat.Prime 367) := {out := by norm_num}

def I367N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![367, 0, 0, 0, 0], ![98, 1, 0, 0, 0]] i)))

def I367N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![367, 0, 0, 0, 0], ![922, 2434, 10957, -2500, 22728]] i)))

def P367P0 : CertificateIrreducibleZModOfList' 367 1 2 8 [98, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [191], [364], [32], [], [274], [174], [269, 1]]]
 h' := ![![[0, 1], [366], [294], [167], [51], [306], [197], [62], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P367P1 : CertificateIrreducibleZModOfList' 367 4 2 8 [274, 63, 62, 269, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [85, 218, 41, 335], [121, 286, 118, 213], [259, 229, 208, 186], [0, 1]]
 g := ![![[68, 230, 34, 174], [205, 192, 287, 91], [71, 224, 96, 14], [311, 271, 234, 204], [289, 224, 362], [148, 91], [98, 1], []], ![[119, 331, 251, 125, 155, 334], [341, 149, 54, 195, 321, 103], [295, 163, 123, 159], [40, 206, 112, 316, 157, 363], [128, 356, 208], [72, 252, 183, 115, 251, 136], [58, 132, 174, 70, 356, 68], [322, 106, 290]], ![[286, 133, 246, 295, 365, 327], [234, 121, 151, 17, 104, 332], [74, 228, 175, 189, 222, 244], [52, 357, 8, 53, 256, 114], [359, 330, 299], [217, 178, 3, 236, 220, 50], [34, 250, 355, 170, 116, 329], [360, 313, 228]], ![[319, 290, 271, 238, 148, 305], [359, 158, 91, 199, 229, 254], [94, 172, 332, 248, 307, 21], [0, 103, 316, 315, 123, 76], [116, 53, 9], [25, 332, 261, 58, 251, 11], [7, 203, 79, 112, 300, 344], [263, 1, 98]]]
 h' := ![![[85, 218, 41, 335], [348, 179, 212, 62], [364, 340, 56, 267], [297, 209, 190, 43], [180, 195, 277, 122], [185, 291, 313, 340], [306, 158, 100], [0, 0, 1], [0, 1]], ![[121, 286, 118, 213], [93, 187, 185, 14], [27, 38, 253, 357], [164, 212, 322], [162, 4, 78, 295], [79, 176, 283, 93], [281, 194, 193, 76], [104, 208, 139, 66], [85, 218, 41, 335]], ![[259, 229, 208, 186], [273, 12, 121, 113], [116, 221, 190, 345], [292, 156, 235, 155], [164, 71, 83, 335], [305, 177, 61, 304], [336, 277, 130, 241], [44, 39, 336, 176], [121, 286, 118, 213]], ![[0, 1], [358, 356, 216, 178], [215, 135, 235, 132], [348, 157, 354, 169], [147, 97, 296, 349], [79, 90, 77, 364], [43, 105, 311, 50], [157, 120, 258, 125], [259, 229, 208, 186]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [277, 135, 243], []]
 b := ![[], [], [313, 20, 338, 309], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A367 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 367 2 where
 D := ![[98, 1], [274, 63, 62, 269, 1]]; D' := ![[98, 1], [274, 63, 62, 269, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8, 8]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P367P0
  | 1 => exact P367P1

def C3670 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A367.D 0) 367 where
  n := 1
  w := ![![367, 0, 0, 0, 0], ![98, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C3671 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A367.D 1) 367 where
  n := 4
  w := ![![367, 0, 0, 0, 0], ![922, 2434, 10957, -2500, 22728]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K367 : KummerData 367 ![I367N0, I367N1] ![367, 18141126721] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A367
  C := by
    intro i
    match i with
    | 0 => exact C3670
    | 1 => exact C3671
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 367 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp373 : Fact (Nat.Prime 373) := {out := by norm_num}

def I373N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![373, 0, 0, 0, 0], ![123, 14, 1, 0, 0]] i)))

def I373N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![373, 0, 0, 0, 0], ![227, 74, 359, 2, 0]] i)))

def P373P0 : CertificateIrreducibleZModOfList' 373 2 2 8 [123, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [359, 372], [0, 1]]
 g := ![![[176, 279], [13], [369, 9], [332], [208, 17], [309, 229], [327, 196], [1]], ![[0, 94], [13], [243, 364], [332], [343, 356], [87, 144], [194, 177], [1]]]
 h' := ![![[359, 372], [253, 98], [119, 67], [104, 370], [153, 248], [39, 197], [63, 244], [250, 359], [0, 1]], ![[0, 1], [0, 275], [300, 306], [146, 3], [38, 125], [265, 176], [4, 129], [73, 14], [359, 372]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [247]]
 b := ![[], [305, 310]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P373P1 : CertificateIrreducibleZModOfList' 373 3 2 8 [227, 73, 359, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [210, 302, 112], [177, 70, 261], [0, 1]]
 g := ![![[354, 41, 165], [185, 364], [33, 353, 152], [242, 7], [132, 296, 253], [187, 312, 302], [123, 14, 1], []], ![[28, 169, 224, 71], [302, 290], [262, 294, 80, 7], [239, 36], [281, 304, 349, 337], [17, 144, 216, 147], [228, 275, 333, 117], [68, 235]], ![[359, 369, 73, 225], [318, 283], [224, 244, 262, 348], [364, 366], [364, 169, 2, 261], [105, 338, 332, 289], [110, 138, 133, 130], [292, 235]]]
 h' := ![![[210, 302, 112], [369, 212, 270], [342, 293, 61], [353, 219, 317], [249, 117, 58], [73, 128, 66], [54, 152, 100], [0, 0, 1], [0, 1]], ![[177, 70, 261], [32, 200, 122], [207, 265, 159], [299, 178, 93], [252, 9, 6], [65, 285, 306], [164, 369, 152], [316, 272, 70], [210, 302, 112]], ![[0, 1], [16, 334, 354], [169, 188, 153], [300, 349, 336], [308, 247, 309], [324, 333, 1], [358, 225, 121], [107, 101, 302], [177, 70, 261]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36, 7], []]
 b := ![[], [311, 202, 303], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A373 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 373 2 where
 D := ![[123, 14, 1], [227, 73, 359, 1]]; D' := ![[123, 14, 1], [227, 73, 359, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8, 8]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P373P0
  | 1 => exact P373P1

def C3730 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A373.D 0) 373 where
  n := 2
  w := ![![373, 0, 0, 0, 0], ![123, 14, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C3731 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A373.D 1) 373 where
  n := 3
  w := ![![373, 0, 0, 0, 0], ![227, 74, 359, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K373 : KummerData 373 ![I373N0, I373N1] ![139129, 51895117] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A373
  C := by
    intro i
    match i with
    | 0 => exact C3730
    | 1 => exact C3731
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 373 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp379 : Fact (Nat.Prime 379) := {out := by norm_num}

def I379N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![379, 0, 0, 0, 0], ![46, 1, 0, 0, 0]] i)))

def I379N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![379, 0, 0, 0, 0], ![164, 1, 0, 0, 0]] i)))

def I379N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![379, 0, 0, 0, 0], ![184, 173, 169, 2, 0]] i)))

def P379P0 : CertificateIrreducibleZModOfList' 379 1 2 8 [46, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [173], [], [348], [324], [297], [329], [333, 1]]]
 h' := ![![[0, 1], [1], [141], [289], [256], [361], [26], [221], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P379P1 : CertificateIrreducibleZModOfList' 379 1 2 8 [164, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [104], [], [62], [289], [127], [169], [215, 1]]]
 h' := ![![[0, 1], [378], [56], [65], [358], [17], [330], [366], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P379P2 : CertificateIrreducibleZModOfList' 379 3 2 8 [184, 172, 169, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [311, 35, 252], [278, 343, 127], [0, 1]]
 g := ![![[91, 21, 126], [306, 196, 6], [243, 120], [28, 110, 205], [257, 236, 180], [117, 357, 146], [343, 210, 1], []], ![[277, 294, 334, 209], [149, 139, 218, 72], [332, 304], [366, 211, 121, 27], [280, 299, 287, 155], [358, 248, 120, 241], [81, 194, 192, 273], [173, 211]], ![[297, 222, 243, 19], [200, 90, 215, 159], [80, 84], [11, 252, 136, 216], [363, 50, 216, 19], [363, 135, 112, 126], [337, 92, 93, 185], [298, 211]]]
 h' := ![![[311, 35, 252], [167, 51, 287], [228, 148, 232], [154, 326, 96], [87, 240, 179], [75, 9, 145], [181, 146, 100], [0, 0, 1], [0, 1]], ![[278, 343, 127], [330, 212, 246], [7, 199, 140], [68, 83, 243], [361, 4, 218], [72, 376, 80], [148, 212, 219], [80, 186, 343], [311, 35, 252]], ![[0, 1], [288, 116, 225], [328, 32, 7], [220, 349, 40], [95, 135, 361], [233, 373, 154], [220, 21, 60], [91, 193, 35], [278, 343, 127]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [336, 162], []]
 b := ![[], [101, 146, 243], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A379 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 379 3 where
 D := ![[46, 1], [164, 1], [184, 172, 169, 1]]; D' := ![[46, 1], [164, 1], [184, 172, 169, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8, 8, 8]
 n := ![1, 1, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P379P0
  | 1 => exact P379P1
  | 2 => exact P379P2

def C3790 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A379.D 0) 379 where
  n := 1
  w := ![![379, 0, 0, 0, 0], ![46, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C3791 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A379.D 1) 379 where
  n := 1
  w := ![![379, 0, 0, 0, 0], ![164, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C3792 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A379.D 2) 379 where
  n := 3
  w := ![![379, 0, 0, 0, 0], ![184, 173, 169, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K379 : KummerData 379 ![I379N0, I379N1, I379N2] ![379, 379, 54439939] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A379
  C := by
    intro i
    match i with
    | 0 => exact C3790
    | 1 => exact C3791
    | 2 => exact C3792
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 379 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp383 : Fact (Nat.Prime 383) := {out := by norm_num}

def I383N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![383, 0, 0, 0, 0], ![217, 1, 0, 0, 0]] i)))

def I383N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![383, 0, 0, 0, 0], ![775, 2295, 11258, -2706, 22728]] i)))

def P383P0 : CertificateIrreducibleZModOfList' 383 1 2 8 [217, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [353], [24], [184], [12], [348], [17], [166, 1]]]
 h' := ![![[0, 1], [382], [154], [287], [77], [318], [141], [363], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P383P1 : CertificateIrreducibleZModOfList' 383 4 2 8 [127, 27, 363, 166, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [150, 105, 10, 228], [100, 183, 267, 292], [350, 94, 106, 246], [0, 1]]
 g := ![![[225, 161, 218, 343], [243, 69, 249, 55], [313, 247, 80, 251], [39, 243, 130, 258], [320, 73, 44, 73], [363, 42], [217, 1], []], ![[38, 299, 13, 287, 12, 288], [255, 310, 337, 32, 57, 63], [110, 202, 138, 20, 153, 295], [7, 150, 61, 284, 274, 168], [20, 361, 281, 355, 25, 238], [32, 45, 244, 198, 170, 278], [178, 378, 86, 99, 36, 213], [336, 376, 279]], ![[8, 50, 197, 159, 191, 147], [371, 315, 316, 299, 183, 50], [1, 167, 22, 131, 353, 42], [99, 163, 201, 166, 90, 152], [211, 214, 132, 200, 126, 251], [270, 291, 4, 130, 363, 213], [269, 329, 278, 53, 373, 373], [307, 371, 238]], ![[208, 319, 325, 142, 175, 163], [257, 208, 152, 67, 220, 326], [171, 167, 113, 236, 161, 40], [349, 123, 66, 328, 343, 191], [331, 296, 198, 83, 258, 22], [10, 181, 144, 21, 192, 234], [348, 161, 186, 117, 279, 79], [134, 115, 2]]]
 h' := ![![[150, 105, 10, 228], [162, 46, 102, 145], [81, 305, 357, 210], [26, 107, 282, 146], [341, 55, 372, 32], [242, 91, 230, 148], [17, 142, 100], [0, 0, 1], [0, 1]], ![[100, 183, 267, 292], [341, 164, 40, 93], [299, 215, 362, 242], [79, 14, 141, 353], [303, 201, 67, 299], [172, 346, 49, 92], [313, 352, 26, 201], [127, 337, 55, 157], [150, 105, 10, 228]], ![[350, 94, 106, 246], [48, 8, 197, 357], [294, 158, 242, 250], [239, 301, 360, 285], [319, 279, 300, 165], [327, 127, 282, 148], [73, 255, 91, 272], [119, 344, 315, 63], [100, 183, 267, 292]], ![[0, 1], [53, 165, 44, 171], [150, 88, 188, 64], [257, 344, 366, 365], [34, 231, 27, 270], [5, 202, 205, 378], [307, 17, 166, 293], [157, 85, 12, 163], [350, 94, 106, 246]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [60, 111, 281], []]
 b := ![[], [], [280, 172, 311, 344], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A383 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 383 2 where
 D := ![[217, 1], [127, 27, 363, 166, 1]]; D' := ![[217, 1], [127, 27, 363, 166, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8, 8]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P383P0
  | 1 => exact P383P1

def C3830 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A383.D 0) 383 where
  n := 1
  w := ![![383, 0, 0, 0, 0], ![217, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C3831 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A383.D 1) 383 where
  n := 4
  w := ![![383, 0, 0, 0, 0], ![775, 2295, 11258, -2706, 22728]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K383 : KummerData 383 ![I383N0, I383N1] ![383, 21517662721] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A383
  C := by
    intro i
    match i with
    | 0 => exact C3830
    | 1 => exact C3831
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 383 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp389 : Fact (Nat.Prime 389) := {out := by norm_num}

def I389N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![389, 0, 0, 0, 0], ![15949, 778, 389, 0, 0]] i)))

def P389P0 : CertificateIrreducibleZModOfList' 389 5 2 8 [229, 253, 289, 0, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [169, 116, 76, 172, 13], [102, 5, 315, 83, 338], [261, 161, 176, 323, 295], [246, 106, 211, 200, 132], [0, 1]]
 g := ![![[339, 30, 210, 260, 187], [201, 205, 79, 120], [218, 176, 338, 82, 127], [74, 110, 243, 221], [362, 362, 209, 30], [359, 275], [0, 1], []], ![[253, 309, 114, 196, 192, 104, 152, 13], [47, 272, 216, 308], [74, 234, 234, 186, 206, 198, 376, 183], [272, 263, 124, 19], [132, 179, 101, 209], [21, 237, 310, 345], [0, 10, 38, 96], [191, 308, 95, 122, 363, 23, 68, 252]], ![[29, 258, 169, 345, 185, 258, 230, 319], [335, 11, 219, 35], [235, 232, 119, 129, 375, 85, 101, 118], [222, 3, 331, 36], [60, 17, 248, 44], [381, 356, 182, 373], [142, 278, 111, 320], [69, 287, 312, 122, 65, 27, 353, 387]], ![[137, 243, 229, 206, 43, 51, 209, 269], [97, 141, 333, 262], [81, 205, 283, 244, 59, 54, 54, 354], [77, 370, 349, 78], [275, 122, 90, 112], [367, 278, 55, 111], [71, 298, 162, 264], [281, 340, 368, 218, 32, 201, 194, 320]], ![[346, 197, 279, 106, 375, 166, 115, 118], [114, 133, 226, 202], [357, 75, 285, 1, 82, 108, 50, 233], [67, 174, 239, 178], [109, 46, 144, 178], [178, 285, 235, 216], [259, 276, 345, 236], [30, 258, 198, 305, 201, 384, 25, 200]]]
 h' := ![![[169, 116, 76, 172, 13], [46, 153, 208, 362, 24], [259, 310, 201, 256, 241], [272, 311, 80, 60, 72], [267, 85, 132, 296, 143], [257, 242, 94, 222, 315], [0, 160, 136, 100], [0, 0, 0, 1], [0, 1]], ![[102, 5, 315, 83, 338], [262, 361, 65, 300, 388], [284, 386, 22, 176, 257], [346, 40, 54, 363, 349], [86, 219, 61, 182, 244], [370, 125, 144, 14, 212], [30, 94, 116, 381, 321], [315, 68, 291, 87, 112], [169, 116, 76, 172, 13]], ![[261, 161, 176, 323, 295], [150, 208, 249, 264, 386], [319, 92, 6, 111, 206], [156, 169, 356, 53, 14], [183, 7, 8, 329, 383], [132, 143, 90, 42, 40], [213, 197, 307, 185, 318], [164, 137, 222, 343, 299], [102, 5, 315, 83, 338]], ![[246, 106, 211, 200, 132], [171, 357, 352, 40, 204], [109, 25, 341, 196, 111], [374, 91, 125, 238, 63], [180, 119, 319, 225, 95], [57, 17, 272, 85, 298], [99, 99, 205, 225, 307], [172, 79, 31, 379, 342], [261, 161, 176, 323, 295]], ![[0, 1], [278, 88, 293, 201, 165], [113, 354, 208, 39, 352], [197, 167, 163, 64, 280], [330, 348, 258, 135, 302], [361, 251, 178, 26, 302], [94, 228, 14, 276, 221], [38, 105, 234, 357, 25], [246, 106, 211, 200, 132]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 124, 369, 109], [], [], []]
 b := ![[], [153, 2, 226, 147, 231], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A389 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 389 1 where
 D := ![[229, 253, 289, 0, 0, 1]]; D' := ![[229, 253, 289, 0, 0, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8]
 n := ![5]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P389P0

def C3890 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A389.D 0) 389 where
  n := 5
  w := ![![389, 0, 0, 0, 0], ![15949, 778, 389, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K389 : KummerData 389 ![I389N0] ![8907339520949] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A389
  C := by
    intro i
    match i with
    | 0 => exact C3890
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 389 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp397 : Fact (Nat.Prime 397) := {out := by norm_num}

def I397N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![397, 0, 0, 0, 0], ![306, 1, 0, 0, 0]] i)))

def I397N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![397, 0, 0, 0, 0], ![908, 2555, 11236, -2856, 22728]] i)))

def P397P0 : CertificateIrreducibleZModOfList' 397 1 2 8 [306, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [349], [147], [], [], [], [341, 91, 1]]]
 h' := ![![[0, 1], [1], [396], [276], [140], [314], [255], [65], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P397P1 : CertificateIrreducibleZModOfList' 397 4 2 8 [260, 362, 341, 91, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [223, 323, 57, 109], [381, 20, 234, 185], [99, 53, 106, 103], [0, 1]]
 g := ![![[303, 290, 365, 195], [325, 130, 129], [321, 201, 165, 307], [387, 350, 110, 314], [158, 138, 209], [260, 116, 75], [0, 306, 1], []], ![[64, 25, 79, 128, 133, 8], [309, 306, 278], [95, 313, 137, 55, 131, 384], [312, 149, 388, 266, 299, 248], [289, 184, 364], [377, 72, 121], [196, 188, 64], [376, 345, 176, 17, 28, 15]], ![[284, 32, 26, 21, 56, 187], [10, 19, 23], [128, 62, 219, 319, 272, 181], [360, 343, 246, 9, 250, 114], [35, 15, 78], [304, 229, 275], [287, 350, 319], [227, 230, 66, 366, 42, 269]], ![[362, 58, 367, 390, 295, 184], [138, 261, 341], [352, 167, 191, 265, 373, 263], [164, 221, 40, 169, 53, 323], [301, 124, 97], [54, 285, 147], [368, 330, 246], [56, 335, 334, 171, 374, 183]]]
 h' := ![![[223, 323, 57, 109], [221, 343, 300, 275], [307, 147, 43, 78], [218, 358, 225, 313], [1, 32, 296, 255], [287, 378, 106, 81], [0, 237, 128, 100], [0, 0, 0, 1], [0, 1]], ![[381, 20, 234, 185], [307, 216, 169, 188], [222, 158, 220, 300], [333, 392, 322, 46], [387, 394, 352, 306], [104, 147, 391, 268], [113, 264, 197, 11], [68, 19, 319, 389], [223, 323, 57, 109]], ![[99, 53, 106, 103], [50, 228, 221, 237], [247, 373, 250, 325], [19, 220, 374, 393], [312, 340, 106, 73], [218, 230, 90, 152], [65, 42, 372, 146], [7, 29, 153, 349], [381, 20, 234, 185]], ![[0, 1], [99, 7, 104, 94], [270, 116, 281, 91], [284, 221, 270, 42], [242, 28, 40, 160], [243, 39, 207, 293], [189, 251, 97, 140], [160, 349, 322, 55], [99, 53, 106, 103]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [336, 292, 169], []]
 b := ![[], [], [26, 319, 177, 336], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A397 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 397 2 where
 D := ![[306, 1], [260, 362, 341, 91, 1]]; D' := ![[306, 1], [260, 362, 341, 91, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8, 8]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P397P0
  | 1 => exact P397P1

def C3970 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A397.D 0) 397 where
  n := 1
  w := ![![397, 0, 0, 0, 0], ![306, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C3971 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A397.D 1) 397 where
  n := 4
  w := ![![397, 0, 0, 0, 0], ![908, 2555, 11236, -2856, 22728]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K397 : KummerData 397 ![I397N0, I397N1] ![397, 24840596881] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A397
  C := by
    intro i
    match i with
    | 0 => exact C3970
    | 1 => exact C3971
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 397 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp401 : Fact (Nat.Prime 401) := {out := by norm_num}

def I401N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![401, 0, 0, 0, 0], ![115, 1, 0, 0, 0]] i)))

def I401N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![401, 0, 0, 0, 0], ![358, 1, 0, 0, 0]] i)))

def I401N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![401, 0, 0, 0, 0], ![79, 105, 329, 2, 0]] i)))

def P401P0 : CertificateIrreducibleZModOfList' 401 1 2 8 [115, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [], [70], [], [], [393, 286, 1]]]
 h' := ![![[0, 1], [400], [381], [98], [371], [291], [290], [118], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P401P1 : CertificateIrreducibleZModOfList' 401 1 2 8 [358, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [], [63], [], [], [245, 43, 1]]]
 h' := ![![[0, 1], [1], [400], [381], [303], [146], [252], [109], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P401P2 : CertificateIrreducibleZModOfList' 401 3 2 8 [79, 104, 329, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [249, 107, 279], [224, 293, 122], [0, 1]]
 g := ![![[7, 35, 229], [347, 10], [109, 1], [369, 35], [145, 28, 291], [2, 8], [179, 372], [1]], ![[94, 321, 41, 334], [2, 397], [98, 77], [133, 285], [13, 83, 263, 355], [197, 77], [288, 376], [286, 213, 31, 281]], ![[296, 243, 205, 139], [277, 44], [62, 160], [392, 146], [203, 138, 56, 327], [349, 215], [88, 311], [87, 282, 229, 120]]]
 h' := ![![[249, 107, 279], [60, 226, 330], [280, 135, 211], [323, 219, 1], [174, 294, 293], [207, 379, 111], [120, 107, 106], [322, 297, 72], [0, 1]], ![[224, 293, 122], [37, 39, 146], [350, 154, 40], [83, 227, 41], [114, 178, 257], [323, 210, 320], [249, 119, 360], [12, 235, 100], [249, 107, 279]], ![[0, 1], [300, 136, 326], [23, 112, 150], [54, 356, 359], [81, 330, 252], [270, 213, 371], [217, 175, 336], [140, 270, 229], [224, 293, 122]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [239, 184], []]
 b := ![[], [82, 348, 179], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A401 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 401 3 where
 D := ![[115, 1], [358, 1], [79, 104, 329, 1]]; D' := ![[115, 1], [358, 1], [79, 104, 329, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8, 8, 8]
 n := ![1, 1, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P401P0
  | 1 => exact P401P1
  | 2 => exact P401P2

def C4010 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A401.D 0) 401 where
  n := 1
  w := ![![401, 0, 0, 0, 0], ![115, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C4011 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A401.D 1) 401 where
  n := 1
  w := ![![401, 0, 0, 0, 0], ![358, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C4012 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A401.D 2) 401 where
  n := 3
  w := ![![401, 0, 0, 0, 0], ![79, 105, 329, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K401 : KummerData 401 ![I401N0, I401N1, I401N2] ![401, 401, 64481201] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A401
  C := by
    intro i
    match i with
    | 0 => exact C4010
    | 1 => exact C4011
    | 2 => exact C4012
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 401 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp409 : Fact (Nat.Prime 409) := {out := by norm_num}

def I409N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![409, 0, 0, 0, 0], ![15951, 818, 409, 0, 0]] i)))

def P409P0 : CertificateIrreducibleZModOfList' 409 5 2 8 [231, 293, 309, 0, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [173, 395, 188, 53, 67], [7, 291, 306, 117, 142], [270, 158, 186, 183, 353], [368, 382, 138, 56, 256], [0, 1]]
 g := ![![[279, 279, 289, 140, 160], [181, 288, 318, 243], [355, 76, 91, 9], [289, 176, 197, 24, 231], [150, 222, 253, 46, 167], [296, 184], [0, 1], []], ![[128, 391, 80, 36, 198, 250, 312, 210], [316, 316, 364, 162], [31, 55, 114, 289], [77, 35, 1, 284, 312, 109, 158, 132], [61, 229, 327, 5, 134, 329, 72, 194], [311, 13, 89, 311], [22, 258, 251, 20], [371, 53, 183, 128, 279, 275, 46, 148]], ![[84, 360, 18, 361, 351, 100, 37, 217], [202, 189, 126, 184], [113, 91, 358, 318], [368, 71, 311, 95, 249, 227, 132, 265], [248, 356, 65, 281, 354, 52, 155, 391], [118, 285, 3, 273], [47, 402, 132, 120], [204, 364, 77, 393, 35, 22, 228, 288]], ![[96, 120, 106, 239, 341, 187, 195, 226], [390, 53, 318, 142], [154, 78, 171, 167], [370, 294, 55, 324, 167, 83, 84, 199], [106, 274, 12, 408, 322, 58, 18, 47], [173, 366, 350, 159], [173, 315, 245, 34], [388, 68, 78, 286, 330, 238, 183, 254]], ![[207, 290, 139, 273, 124, 296, 273, 143], [293, 358, 91, 125], [112, 328, 94, 204], [401, 210, 163, 160, 291, 247, 47, 92], [393, 351, 378, 53, 267, 326, 365, 50], [13, 286, 403, 338], [75, 119, 305, 71], [152, 319, 245, 212, 279, 327, 177, 36]]]
 h' := ![![[173, 395, 188, 53, 67], [13, 84, 75, 100, 287], [79, 268, 143, 374, 124], [317, 367, 251, 53, 406], [115, 77, 189, 342, 244], [336, 12, 10, 391, 385], [0, 178, 116, 100], [0, 0, 0, 1], [0, 1]], ![[7, 291, 306, 117, 142], [213, 106, 24, 70, 135], [35, 322, 19, 19, 354], [285, 211, 283, 268, 17], [36, 358, 35, 100, 307], [45, 164, 216, 350, 3], [164, 275, 85, 400, 245], [375, 366, 157, 42, 300], [173, 395, 188, 53, 67]], ![[270, 158, 186, 183, 353], [64, 407, 176, 156, 200], [399, 318, 95, 28, 309], [288, 15, 77, 101, 184], [388, 32, 361, 172, 31], [1, 32, 239, 147, 36], [80, 298, 60, 252, 56], [254, 353, 217, 335, 386], [7, 291, 306, 117, 142]], ![[368, 382, 138, 56, 256], [344, 140, 40, 31, 373], [41, 133, 135, 261, 372], [21, 75, 179, 387, 24], [155, 256, 138, 133, 79], [27, 194, 353, 259, 92], [114, 298, 223, 30, 74], [227, 87, 207, 370, 86], [270, 158, 186, 183, 353]], ![[0, 1], [226, 81, 94, 52, 232], [251, 186, 17, 136, 68], [49, 150, 28, 9, 187], [154, 95, 95, 71, 157], [277, 7, 0, 80, 302], [194, 178, 334, 36, 34], [262, 12, 237, 70, 46], [368, 382, 138, 56, 256]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [387, 74, 328, 291], [], [], []]
 b := ![[], [358, 213, 44, 369, 191], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A409 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 409 1 where
 D := ![[231, 293, 309, 0, 0, 1]]; D' := ![[231, 293, 309, 0, 0, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8]
 n := ![5]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P409P0

def C4090 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A409.D 0) 409 where
  n := 5
  w := ![![409, 0, 0, 0, 0], ![15951, 818, 409, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K409 : KummerData 409 ![I409N0] ![11445019581049] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A409
  C := by
    intro i
    match i with
    | 0 => exact C4090
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 409 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp419 : Fact (Nat.Prime 419) := {out := by norm_num}

def I419N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![419, 0, 0, 0, 0], ![18, 1, 0, 0, 0]] i)))

def I419N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![419, 0, 0, 0, 0], ![406, 1, 0, 0, 0]] i)))

def I419N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![419, 0, 0, 0, 0], ![368, 260, 414, 2, 0]] i)))

def P419P0 : CertificateIrreducibleZModOfList' 419 1 2 8 [18, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [256], [], [], [], [145], [], [324, 401, 1]]]
 h' := ![![[0, 1], [1], [16], [4], [417], [323], [318], [34], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P419P1 : CertificateIrreducibleZModOfList' 419 1 2 8 [406, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [129], [], [], [], [13], [], [169, 13, 1]]]
 h' := ![![[0, 1], [1], [59], [152], [69], [169], [348], [102], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P419P2 : CertificateIrreducibleZModOfList' 419 3 2 8 [368, 259, 414, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [114, 364, 216], [310, 54, 203], [0, 1]]
 g := ![![[298, 86, 264], [332, 126, 187], [322, 324], [186, 411], [245, 341], [136, 255, 192], [49, 25], [1]], ![[1, 182, 17, 213], [349, 161, 19, 279], [189, 393], [191, 333], [87, 13], [304, 185, 116, 398], [11, 295], [189, 87, 6, 327]], ![[366, 180, 413, 7], [156, 211, 306, 191], [252, 37], [130, 92], [18, 38], [257, 400, 240, 306], [416, 12], [1, 153, 391, 92]]]
 h' := ![![[114, 364, 216], [172, 285, 39], [221, 369, 381], [130, 199, 401], [117, 221, 192], [232, 144, 315], [72, 295, 187], [51, 160, 5], [0, 1]], ![[310, 54, 203], [228, 19, 397], [328, 297, 137], [140, 22, 112], [6, 195, 282], [344, 230, 348], [329, 312, 74], [381, 2, 53], [114, 364, 216]], ![[0, 1], [331, 115, 402], [162, 172, 320], [352, 198, 325], [114, 3, 364], [156, 45, 175], [22, 231, 158], [151, 257, 361], [310, 54, 203]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33, 365], []]
 b := ![[], [250, 20, 105], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A419 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 419 3 where
 D := ![[18, 1], [406, 1], [368, 259, 414, 1]]; D' := ![[18, 1], [406, 1], [368, 259, 414, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8, 8, 8]
 n := ![1, 1, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P419P0
  | 1 => exact P419P1
  | 2 => exact P419P2

def C4190 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A419.D 0) 419 where
  n := 1
  w := ![![419, 0, 0, 0, 0], ![18, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C4191 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A419.D 1) 419 where
  n := 1
  w := ![![419, 0, 0, 0, 0], ![406, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C4192 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A419.D 2) 419 where
  n := 3
  w := ![![419, 0, 0, 0, 0], ![368, 260, 414, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K419 : KummerData 419 ![I419N0, I419N1, I419N2] ![419, 419, 73560059] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A419
  C := by
    intro i
    match i with
    | 0 => exact C4190
    | 1 => exact C4191
    | 2 => exact C4192
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 419 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


lemma PB18792I8_primes (p : ℕ) :
  p ∈ Set.range ![367, 373, 379, 383, 389, 397, 401, 409, 419] ↔ Nat.Prime p ∧ 359 < p ∧ p ≤ 419 := by
  rw [← List.mem_ofFn']
  convert primes_range 359 419 (by omega)
  decide

def PB18792I8 : PrimesBelowBoundCertificateInterval O 359 419 18792 where
  m := 9
  g := ![2, 2, 3, 2, 1, 2, 3, 1, 3]
  P := ![367, 373, 379, 383, 389, 397, 401, 409, 419]
  hP := PB18792I8_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I367N0, I367N1]
    · exact ![I373N0, I373N1]
    · exact ![I379N0, I379N1, I379N2]
    · exact ![I383N0, I383N1]
    · exact ![I389N0]
    · exact ![I397N0, I397N1]
    · exact ![I401N0, I401N1, I401N2]
    · exact ![I409N0]
    · exact ![I419N0, I419N1, I419N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · convert (containsPrimesAbove_of_KummerData K367) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K373) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K379) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K383) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K389) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K397) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K401) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K409) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K419) <;> rfl
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![367, 18141126721]
    · exact ![139129, 51895117]
    · exact ![379, 379, 54439939]
    · exact ![383, 21517662721]
    · exact ![8907339520949]
    · exact ![397, 24840596881]
    · exact ![401, 401, 64481201]
    · exact ![11445019581049]
    · exact ![419, 419, 73560059]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact (card_quot_of_KummerData K367)
    · exact (card_quot_of_KummerData K373)
    · exact (card_quot_of_KummerData K379)
    · exact (card_quot_of_KummerData K383)
    · exact (card_quot_of_KummerData K389)
    · exact (card_quot_of_KummerData K397)
    · exact (card_quot_of_KummerData K401)
    · exact (card_quot_of_KummerData K409)
    · exact (card_quot_of_KummerData K419)
  β := ![I367N0, I379N0, I379N1, I383N0, I397N0, I401N0, I401N1, I419N0, I419N1]
  Il := ![[I367N0], [], [I379N0, I379N1], [I383N0], [], [I397N0], [I401N0, I401N1], [], [I419N0, I419N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
