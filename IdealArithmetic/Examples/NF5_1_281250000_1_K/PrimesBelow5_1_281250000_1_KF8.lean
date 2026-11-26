
import IdealArithmetic.Examples.NF5_1_281250000_1_K.RI5_1_281250000_1_K
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 

instance hp367 : Fact (Nat.Prime 367) := {out := by norm_num}

def I367N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![367, 0, 0, 0, 0], ![24, 1, 0, 0, 0]] i)))

def I367N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![367, 0, 0, 0, 0], ![171, 355, 189, 1715, 10]] i)))

def P367P0 : CertificateIrreducibleZModOfList' 367 1 2 8 [24, 1] where
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
 g := ![![[], [107], [200], [120], [], [164], [8], [343, 1]]]
 h' := ![![[0, 1], [1], [338], [56], [292], [101], [175], [209], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P367P1 : CertificateIrreducibleZModOfList' 367 4 2 8 [171, 355, 184, 343, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [340, 190, 152, 133], [194, 183, 299, 209], [224, 360, 283, 25], [0, 1]]
 g := ![![[174, 169, 268, 271], [141, 322, 207, 270], [254, 89, 88, 95], [19, 327, 257, 14], [125, 58, 126], [85, 189, 320, 258], [24, 1], []], ![[16, 320, 22, 189, 271, 29], [239, 108, 85, 90, 103, 140], [304, 210, 84, 303, 121, 180], [349, 355, 355, 115, 203, 186], [86, 214, 162], [229, 290, 114, 185, 152, 86], [294, 326, 195, 201, 140, 171], [254, 346, 73]], ![[87, 52, 323, 158, 282, 26], [36, 285, 47, 295, 1, 95], [297, 223, 275, 84, 225, 178], [232, 85, 139, 246, 79, 302], [115, 100, 106], [349, 241, 45, 343, 224, 333], [349, 324, 190, 327, 166, 7], [288, 27, 8]], ![[11, 99, 165, 319, 299, 355], [36, 335, 178, 314, 232, 283], [311, 356, 105, 348, 285, 62], [300, 360, 356, 104, 363, 207], [67, 219, 53], [162, 51, 176, 344, 356, 83], [55, 122, 6, 5, 55, 161], [69, 157, 258]]]
 h' := ![![[340, 190, 152, 133], [111, 81, 70, 291], [239, 287, 207, 296], [54, 17, 32, 241], [17, 18, 82, 324], [145, 348, 273, 129], [300, 117, 0, 25], [0, 0, 1], [0, 1]], ![[194, 183, 299, 209], [271, 294, 235, 84], [356, 187, 299, 64], [72, 334, 322, 293], [257, 95, 45, 308], [284, 234, 32, 344], [236, 152, 171, 201], [234, 49, 350, 125], [340, 190, 152, 133]], ![[224, 360, 283, 25], [250, 254, 245, 279], [310, 282, 213, 97], [209, 123, 12, 293], [37, 339, 177, 267], [148, 177, 259, 222], [328, 78, 271, 11], [132, 113, 45, 258], [194, 183, 299, 209]], ![[0, 1], [265, 105, 184, 80], [304, 345, 15, 277], [297, 260, 1, 274], [104, 282, 63, 202], [223, 342, 170, 39], [94, 20, 292, 130], [209, 205, 338, 351], [224, 360, 283, 25]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [226, 174, 70], []]
 b := ![[], [], [7, 47, 306, 98], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A367 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 367 2 where
 D := ![[24, 1], [171, 355, 184, 343, 1]]; D' := ![[24, 1], [171, 355, 184, 343, 1]]
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
  w := ![![367, 0, 0, 0, 0], ![24, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C3671 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A367.D 1) 367 where
  n := 4
  w := ![![367, 0, 0, 0, 0], ![171, 355, 189, 1715, 10]]
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

def I373N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![373, 0, 0, 0, 0], ![348, 1, 0, 0, 0]] i)))

def I373N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![373, 0, 0, 0, 0], ![12, 80, 232, 125, 10]] i)))

def P373P0 : CertificateIrreducibleZModOfList' 373 1 2 8 [348, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [179], [], [70], [235], [94], [25, 1]]]
 h' := ![![[0, 1], [1], [372], [170], [258], [280], [112], [252], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P373P1 : CertificateIrreducibleZModOfList' 373 4 2 8 [12, 80, 227, 25, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [253, 71, 20, 253], [161, 177, 88, 43], [307, 124, 265, 77], [0, 1]]
 g := ![![[10, 42, 210, 119], [35, 300, 22], [355, 307, 5, 333], [364, 334, 91], [197, 211, 0, 257], [285, 141, 41, 252], [348, 1], []], ![[362, 138, 73, 333, 48, 88], [175, 361, 152], [252, 355, 185, 329, 237, 137], [19, 269, 356], [336, 324, 18, 14, 317, 264], [38, 182, 344, 352, 320, 254], [252, 357, 243, 66, 0, 89], [94, 367, 226]], ![[5, 0, 357, 41, 252, 228], [157, 365, 324], [332, 140, 361, 243, 168, 96], [336, 145, 27], [264, 91, 69, 333, 70, 178], [336, 75, 171, 19, 82, 230], [115, 84, 41, 46, 152, 233], [97, 135, 357]], ![[70, 185, 26, 254, 355, 214], [144, 108, 322], [338, 288, 163, 110, 216, 145], [370, 197, 179], [361, 268, 24, 97, 311, 201], [319, 331, 269, 317, 52, 212], [147, 369, 113, 207, 52, 260], [223, 9, 334]]]
 h' := ![![[253, 71, 20, 253], [357, 141, 111, 137], [216, 35, 173, 231], [318, 317, 103, 102], [247, 224, 55, 217], [310, 233, 317, 279], [300, 123, 0, 25], [0, 0, 1], [0, 1]], ![[161, 177, 88, 43], [221, 213, 25, 7], [249, 29, 166, 317], [28, 167, 121, 173], [16, 72, 293, 346], [4, 283, 62, 202], [230, 217, 151, 78], [217, 130, 170, 263], [253, 71, 20, 253]], ![[307, 124, 265, 77], [89, 233, 120, 209], [333, 163, 59, 18], [252, 227, 233, 130], [76, 45, 166, 353], [318, 135, 20, 229], [346, 276, 38, 19], [139, 243, 182, 153], [161, 177, 88, 43]], ![[0, 1], [200, 159, 117, 20], [199, 146, 348, 180], [370, 35, 289, 341], [296, 32, 232, 203], [3, 95, 347, 36], [139, 130, 184, 251], [188, 0, 20, 330], [307, 124, 265, 77]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [1, 76, 48], []]
 b := ![[], [], [37, 148, 88, 129], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A373 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 373 2 where
 D := ![[348, 1], [12, 80, 227, 25, 1]]; D' := ![[348, 1], [12, 80, 227, 25, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8, 8]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P373P0
  | 1 => exact P373P1

def C3730 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A373.D 0) 373 where
  n := 1
  w := ![![373, 0, 0, 0, 0], ![348, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C3731 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A373.D 1) 373 where
  n := 4
  w := ![![373, 0, 0, 0, 0], ![12, 80, 232, 125, 10]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K373 : KummerData 373 ![I373N0, I373N1] ![373, 19356878641] where
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

def I379N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![379, 0, 0, 0, 0], ![379, 0, 0, 1895, 0]] i)))

def P379P0 : CertificateIrreducibleZModOfList' 379 5 2 8 [79, 250, 0, 354, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [290, 81, 139, 216, 118], [83, 327, 335, 187, 136], [367, 30, 144, 309, 214], [18, 319, 140, 46, 290], [0, 1]]
 g := ![![[241, 221, 285, 176, 30], [367, 169, 277, 51, 106], [235, 367, 35, 26], [90, 107, 152, 280, 332], [193, 377, 341, 232, 207], [93, 0, 246], [1], []], ![[106, 159, 319, 327, 240, 75, 250, 218], [93, 151, 197, 255, 262, 179, 200, 361], [31, 216, 331, 267], [175, 125, 218, 215, 166, 205, 233, 104], [270, 184, 156, 85, 243, 284, 254, 324], [31, 135, 367, 229, 352, 90, 59, 9], [131, 297, 204, 14, 21, 342, 294, 104], [155, 48, 190, 280]], ![[281, 366, 145, 35, 120, 200, 61, 22], [84, 27, 73, 58, 292, 251, 67, 187], [349, 50, 86, 137], [75, 89, 39, 327, 141, 250, 165, 127], [0, 111, 174, 72, 26, 260, 219, 79], [235, 244, 43, 167, 29, 115, 260, 103], [18, 202, 236, 120, 202, 226, 68, 93], [154, 281, 78, 304]], ![[41, 5, 338, 240, 294, 16, 43, 373], [264, 332, 293, 331, 95, 88, 173, 363], [197, 338, 301, 376], [273, 274, 165, 87, 171, 138, 96, 175], [177, 209, 216, 140, 303, 196, 259, 354], [321, 33, 309, 261, 114, 365, 373, 209], [320, 129, 129, 255, 51, 249, 299, 168], [164, 148, 360, 316]], ![[265, 316, 139, 289, 170, 36, 202, 171], [300, 193, 116, 60, 287, 281, 346, 262], [33, 21, 275, 327], [307, 177, 136, 59, 223, 38, 117, 221], [218, 95, 49, 245, 151, 26, 221, 114], [35, 167, 181, 314, 331, 137, 328, 333], [241, 125, 361, 19, 269, 214, 99, 100], [22, 123, 150, 341]]]
 h' := ![![[290, 81, 139, 216, 118], [190, 209, 38, 65, 48], [328, 88, 320, 360, 248], [91, 114, 256, 331, 351], [292, 133, 303, 76, 321], [233, 46, 358, 293, 219], [300, 129, 0, 25], [0, 0, 1], [0, 1]], ![[83, 327, 335, 187, 136], [13, 125, 238, 121, 292], [245, 173, 228, 17, 215], [44, 4, 349, 7, 159], [119, 352, 61, 82, 244], [119, 378, 59, 331, 84], [356, 250, 216, 246, 365], [224, 269, 289, 189, 135], [290, 81, 139, 216, 118]], ![[367, 30, 144, 309, 214], [216, 361, 16, 287, 158], [67, 208, 323, 42, 336], [352, 104, 209, 269, 196], [120, 152, 44, 190, 164], [245, 156, 34, 297, 41], [161, 334, 15, 373, 68], [29, 26, 94, 121, 140], [83, 327, 335, 187, 136]], ![[18, 319, 140, 46, 290], [68, 278, 80, 124, 133], [374, 373, 209, 149, 148], [34, 370, 251, 202, 103], [165, 314, 202, 55, 321], [253, 25, 102, 158, 194], [347, 365, 63, 150, 85], [74, 27, 224, 270, 151], [367, 30, 144, 309, 214]], ![[0, 1], [340, 164, 7, 161, 127], [173, 295, 57, 190, 190], [49, 166, 72, 328, 328], [277, 186, 148, 355, 87], [197, 153, 205, 58, 220], [336, 59, 85, 343, 240], [102, 57, 150, 178, 332], [18, 319, 140, 46, 290]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [210, 305, 54, 377], [], [], []]
 b := ![[], [114, 286, 305, 241, 212], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A379 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 379 1 where
 D := ![[79, 250, 0, 354, 0, 1]]; D' := ![[79, 250, 0, 354, 0, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8]
 n := ![5]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P379P0

def C3790 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A379.D 0) 379 where
  n := 5
  w := ![![379, 0, 0, 0, 0], ![379, 0, 0, 1895, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K379 : KummerData 379 ![I379N0] ![7819807277899] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A379
  C := by
    intro i
    match i with
    | 0 => exact C3790
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 379 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp383 : Fact (Nat.Prime 383) := {out := by norm_num}

def I383N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![383, 0, 0, 0, 0], ![247, 1, 0, 0, 0]] i)))

def I383N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![383, 0, 0, 0, 0], ![36, 342, 92, 680, 10]] i)))

def P383P0 : CertificateIrreducibleZModOfList' 383 1 2 8 [247, 1] where
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
 g := ![![[], [138], [252], [193], [248], [63], [288], [136, 1]]]
 h' := ![![[0, 1], [1], [185], [204], [24], [142], [102], [112], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P383P1 : CertificateIrreducibleZModOfList' 383 4 2 8 [36, 342, 87, 136, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 166, 292, 286], [372, 249, 186, 97], [244, 350, 288], [0, 1]]
 g := ![![[106, 139, 377, 353], [224, 312, 21, 192], [280, 6, 160, 19], [59, 75, 62, 284], [55, 154, 260, 266], [193, 61, 26, 242], [247, 1], []], ![[66, 166, 319, 140, 223, 370], [98, 129, 10, 210, 250, 152], [235, 216, 280, 13, 228, 204], [363, 148, 194, 108, 104, 324], [330, 374, 356, 281, 231, 232], [380, 266, 264, 348, 188, 18], [58, 345, 292, 360, 187, 336], [352, 15, 217]], ![[193, 290, 109, 243, 28, 155], [57, 109, 96, 214, 52, 194], [365, 24, 353, 151, 339, 371], [56, 260, 152, 15, 372, 371], [75, 238, 26, 379, 222, 111], [253, 312, 367, 259, 335, 291], [374, 320, 116, 114, 3, 66], [192, 61, 217]], ![[333, 134, 111, 163, 295], [254, 312, 71, 70, 34], [348, 70, 8, 55, 343], [314, 224, 234, 367, 248], [276, 133, 121, 193, 363], [310, 215, 233, 92, 67], [204, 9, 213, 136, 34], [216]]]
 h' := ![![[14, 166, 292, 286], [362, 197, 160, 229], [261, 176, 223, 123], [174, 114, 155, 209], [318, 10, 329, 117], [329, 350, 230, 319], [300, 133, 0, 25], [0, 0, 1], [0, 1]], ![[372, 249, 186, 97], [146, 201, 367, 121], [323, 298, 200, 249], [97, 305, 118, 264], [36, 111, 82, 138], [313, 31, 266, 61], [283, 112, 269, 296], [163, 156, 209, 328], [14, 166, 292, 286]], ![[244, 350, 288], [36, 266, 114, 231], [180, 119, 165, 137], [36, 281, 1, 243], [279, 369, 2, 243], [347, 276, 248, 25], [57, 282, 33, 159], [103, 198, 275, 181], [372, 249, 186, 97]], ![[0, 1], [47, 102, 125, 185], [152, 173, 178, 257], [178, 66, 109, 50], [284, 276, 353, 268], [243, 109, 22, 361], [375, 239, 81, 286], [55, 29, 281, 257], [244, 350, 288]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [324, 290, 232], []]
 b := ![[], [], [155, 172, 244, 274], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A383 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 383 2 where
 D := ![[247, 1], [36, 342, 87, 136, 1]]; D' := ![[247, 1], [36, 342, 87, 136, 1]]
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
  w := ![![383, 0, 0, 0, 0], ![247, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C3831 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A383.D 1) 383 where
  n := 4
  w := ![![383, 0, 0, 0, 0], ![36, 342, 92, 680, 10]]
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

def I389N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![389, 0, 0, 0, 0], ![10, 1, 0, 0, 0]] i)))

def I389N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![389, 0, 0, 0, 0], ![14, 1, 0, 0, 0]] i)))

def I389N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![389, 0, 0, 0, 0], ![109, 22, 365, 5, 0]] i)))

def P389P0 : CertificateIrreducibleZModOfList' 389 1 2 8 [10, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [206], [], [], [], [], [100, 379, 1]]]
 h' := ![![[0, 1], [388], [274], [325], [142], [157], [270], [167], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P389P1 : CertificateIrreducibleZModOfList' 389 1 2 8 [14, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [36], [], [], [], [], [196, 375, 1]]]
 h' := ![![[0, 1], [388], [274], [6], [361], [370], [52], [368], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P389P2 : CertificateIrreducibleZModOfList' 389 3 2 8 [109, 22, 365, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [170, 222, 128], [243, 166, 261], [0, 1]]
 g := ![![[209, 326, 293], [192, 295], [40, 293, 168], [46, 384], [273, 7], [348, 225], [320, 187], [1]], ![[5, 115, 347, 231], [358, 80], [302, 300, 211, 250], [328, 137], [183, 97], [248, 111], [331, 1], [184, 178, 10, 53]], ![[41, 273, 16, 170], [287, 97], [42, 150, 66, 75], [357, 270], [179, 308], [153, 210], [180, 236], [232, 102, 241, 336]]]
 h' := ![![[170, 222, 128], [26, 112, 43], [308, 267, 92], [145, 297, 107], [122, 373, 165], [160, 122, 120], [341, 324, 374], [280, 367, 24], [0, 1]], ![[243, 166, 261], [325, 6, 79], [354, 363, 45], [29, 179, 151], [204, 131, 57], [199, 340, 137], [388, 194, 82], [102, 348, 1], [170, 222, 128]], ![[0, 1], [6, 271, 267], [376, 148, 252], [128, 302, 131], [300, 274, 167], [370, 316, 132], [90, 260, 322], [250, 63, 364], [243, 166, 261]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [120, 271], []]
 b := ![[], [383, 132, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A389 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 389 3 where
 D := ![[10, 1], [14, 1], [109, 22, 365, 1]]; D' := ![[10, 1], [14, 1], [109, 22, 365, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8, 8, 8]
 n := ![1, 1, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P389P0
  | 1 => exact P389P1
  | 2 => exact P389P2

def C3890 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A389.D 0) 389 where
  n := 1
  w := ![![389, 0, 0, 0, 0], ![10, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C3891 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A389.D 1) 389 where
  n := 1
  w := ![![389, 0, 0, 0, 0], ![14, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C3892 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A389.D 2) 389 where
  n := 3
  w := ![![389, 0, 0, 0, 0], ![109, 22, 365, 5, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K389 : KummerData 389 ![I389N0, I389N1, I389N2] ![389, 389, 58863869] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A389
  C := by
    intro i
    match i with
    | 0 => exact C3890
    | 1 => exact C3891
    | 2 => exact C3892
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 389 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp397 : Fact (Nat.Prime 397) := {out := by norm_num}

def I397N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![397, 0, 0, 0, 0], ![31, 1, 0, 0, 0]] i)))

def I397N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![397, 0, 0, 0, 0], ![144, 362, 147, 1830, 10]] i)))

def P397P0 : CertificateIrreducibleZModOfList' 397 1 2 8 [31, 1] where
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
 g := ![![[], [], [333], [99], [], [], [], [167, 366, 1]]]
 h' := ![![[0, 1], [1], [396], [107], [167], [31], [256], [381], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P397P1 : CertificateIrreducibleZModOfList' 397 4 2 8 [144, 362, 142, 366, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [104, 167, 62, 205], [230, 343, 314, 385], [94, 283, 21, 204], [0, 1]]
 g := ![![[286, 228, 29, 202], [235, 306, 340], [309, 153, 366, 154], [315, 26, 239, 388], [276, 177, 324], [249, 364, 361], [25, 31, 1], []], ![[308, 85, 97, 139, 29, 360], [354, 333, 387], [229, 222, 318, 273, 54, 116], [233, 344, 312, 64, 18, 298], [175, 50, 206], [107, 269, 127], [124, 212, 292], [383, 185, 207, 73, 343, 225]], ![[281, 158, 133, 355, 293, 367], [28, 103, 192], [254, 101, 67, 98, 40, 44], [284, 75, 288, 130, 156, 188], [242, 344, 142], [273, 242, 48], [336, 223, 387], [31, 274, 311, 353, 298, 257]], ![[334, 340, 17, 315, 47, 117], [49, 249, 168], [174, 246, 356, 33, 344, 15], [341, 87, 84, 286, 40, 392], [238, 107, 372], [152, 167, 383], [282, 76, 31], [217, 384, 236, 172, 364, 216]]]
 h' := ![![[104, 167, 62, 205], [135, 313, 348, 254], [365, 378, 190, 205], [295, 161, 295, 224], [310, 240, 119, 189], [206, 39, 241, 379], [370, 381, 170, 378], [0, 0, 0, 1], [0, 1]], ![[230, 343, 314, 385], [237, 168, 154, 257], [0, 3, 132, 28], [381, 155, 139, 314], [265, 163, 278, 73], [211, 383, 240, 225], [327, 150, 75, 92], [194, 29, 192, 283], [104, 167, 62, 205]], ![[94, 283, 21, 204], [298, 205, 231, 88], [262, 317, 22, 237], [70, 125, 63, 43], [152, 100, 376, 270], [389, 355, 391, 272], [1, 120, 285, 80], [44, 377, 111, 369], [230, 343, 314, 385]], ![[0, 1], [314, 108, 61, 195], [350, 96, 53, 324], [299, 353, 297, 213], [230, 291, 21, 262], [135, 17, 319, 315], [339, 143, 264, 244], [175, 388, 94, 141], [94, 283, 21, 204]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [270, 36, 191], []]
 b := ![[], [], [171, 37, 97, 49], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A397 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 397 2 where
 D := ![[31, 1], [144, 362, 142, 366, 1]]; D' := ![[31, 1], [144, 362, 142, 366, 1]]
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
  w := ![![397, 0, 0, 0, 0], ![31, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C3971 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A397.D 1) 397 where
  n := 4
  w := ![![397, 0, 0, 0, 0], ![144, 362, 147, 1830, 10]]
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

def I401N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![401, 0, 0, 0, 0], ![144, 1, 0, 0, 0]] i)))

def I401N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![401, 0, 0, 0, 0], ![321, 1, 0, 0, 0]] i)))

def I401N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![401, 0, 0, 0, 0], ![23, 353, 337, 5, 0]] i)))

def P401P0 : CertificateIrreducibleZModOfList' 401 1 2 8 [144, 1] where
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
 g := ![![[], [], [], [], [125], [], [], [285, 257, 1]]]
 h' := ![![[0, 1], [1], [400], [20], [45], [313], [197], [263], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P401P1 : CertificateIrreducibleZModOfList' 401 1 2 8 [321, 1] where
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
 g := ![![[], [], [], [], [5], [], [], [385, 80, 1]]]
 h' := ![![[0, 1], [1], [1], [1], [400], [178], [315], [324], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P401P2 : CertificateIrreducibleZModOfList' 401 3 2 8 [23, 353, 337, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [185, 37, 57], [280, 363, 344], [0, 1]]
 g := ![![[114, 122, 98], [320, 57], [185, 369], [121, 183], [94, 145, 70], [55, 35], [19, 86], [1]], ![[156, 231, 398, 51], [342, 63], [85, 332], [231, 41], [364, 151, 159, 94], [191, 273], [73, 186], [330, 329, 135, 332]], ![[309, 183, 278, 176], [331, 176], [107, 89], [318, 111], [143, 132, 270, 102], [8, 220], [224, 287], [178, 79, 143, 69]]]
 h' := ![![[185, 37, 57], [315, 98, 30], [188, 141, 247], [212, 268, 171], [244, 335, 103], [382, 117, 110], [92, 335, 293], [378, 48, 64], [0, 1]], ![[280, 363, 344], [182, 184, 35], [231, 323, 255], [269, 81, 357], [171, 123, 344], [242, 263, 83], [376, 245, 342], [265, 154, 304], [185, 37, 57]], ![[0, 1], [150, 119, 336], [389, 338, 300], [309, 52, 274], [2, 344, 355], [361, 21, 208], [389, 222, 167], [374, 199, 33], [280, 363, 344]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [98, 18], []]
 b := ![[], [16, 239, 63], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A401 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 401 3 where
 D := ![[144, 1], [321, 1], [23, 353, 337, 1]]; D' := ![[144, 1], [321, 1], [23, 353, 337, 1]]
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
  w := ![![401, 0, 0, 0, 0], ![144, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C4011 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A401.D 1) 401 where
  n := 1
  w := ![![401, 0, 0, 0, 0], ![321, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C4012 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A401.D 2) 401 where
  n := 3
  w := ![![401, 0, 0, 0, 0], ![23, 353, 337, 5, 0]]
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

def I409N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![409, 0, 0, 0, 0], ![409, 0, 0, 2045, 0]] i)))

def P409P0 : CertificateIrreducibleZModOfList' 409 5 2 8 [109, 250, 0, 384, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [56, 245, 60, 166, 265], [219, 357, 15, 41, 328], [79, 359, 237, 372, 41], [55, 265, 97, 239, 184], [0, 1]]
 g := ![![[22, 43, 314, 219, 311], [242, 76, 26, 400], [254, 349, 326, 239], [172, 265, 372, 274, 137], [375, 255, 173, 189, 345], [276, 262, 0, 216], [0, 1], []], ![[270, 253, 392, 165, 388, 315, 14, 45], [200, 189, 408, 182], [262, 275, 353, 368], [204, 377, 402, 211, 155, 317, 27, 246], [92, 399, 146, 219, 211, 274, 86, 227], [73, 387, 234, 12], [241, 219, 34, 92], [313, 209, 324, 182, 299, 370, 96, 125]], ![[396, 182, 18, 345, 155, 116, 328, 64], [223, 11, 141, 179], [274, 29, 153, 48], [115, 162, 293, 283, 328, 221, 272, 25], [99, 375, 256, 343, 74, 111, 144, 327], [51, 60, 111, 229], [372, 259, 35, 23], [210, 186, 77, 323, 23, 395, 46, 259]], ![[120, 50, 199, 133, 165, 150, 95, 144], [331, 260, 132, 3], [233, 184, 184, 72], [238, 276, 207, 187, 247, 36, 193, 327], [406, 36, 63, 2, 402, 305, 31, 102], [298, 386, 199, 212], [45, 21, 154, 403], [155, 51, 299, 186, 28, 289, 322, 209]], ![[65, 75, 406, 74, 395, 25, 151, 225], [12, 91, 72, 48], [66, 329, 316, 103], [284, 143, 185, 359, 311, 272, 384, 54], [148, 159, 155, 312, 164, 286, 398, 225], [203, 138, 202, 166], [407, 275, 377, 399], [138, 108, 333, 179, 321, 75, 193, 25]]]
 h' := ![![[56, 245, 60, 166, 265], [87, 146, 151, 376, 164], [392, 162, 17, 347, 389], [66, 315, 191, 87, 110], [25, 332, 324, 115, 115], [182, 193, 369, 228, 326], [0, 300, 159, 0, 25], [0, 0, 0, 1], [0, 1]], ![[219, 357, 15, 41, 328], [271, 74, 357, 325, 250], [99, 107, 180, 234, 305], [314, 203, 151, 240, 293], [160, 7, 178, 310, 346], [60, 307, 364, 125, 264], [132, 385, 233, 405, 73], [394, 237, 325, 233, 58], [56, 245, 60, 166, 265]], ![[79, 359, 237, 372, 41], [313, 270, 22, 136, 218], [191, 153, 286, 127, 102], [257, 310, 184, 253, 263], [403, 346, 364, 54, 34], [197, 269, 310, 297, 133], [216, 228, 283, 195, 274], [353, 358, 106, 191, 29], [219, 357, 15, 41, 328]], ![[55, 265, 97, 239, 184], [197, 260, 336, 157, 43], [317, 404, 107, 15, 168], [360, 115, 186, 347, 236], [272, 235, 354, 392, 374], [262, 395, 392, 235, 238], [128, 123, 75, 285, 301], [68, 323, 27, 204, 255], [79, 359, 237, 372, 41]], ![[0, 1], [264, 68, 361, 233, 143], [83, 401, 228, 95, 263], [391, 284, 106, 300, 325], [43, 307, 7, 356, 358], [363, 63, 201, 342, 266], [227, 191, 68, 342, 145], [3, 309, 360, 189, 67], [55, 265, 97, 239, 184]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [263, 43, 390, 343], [], [], []]
 b := ![[], [87, 357, 234, 241, 187], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A409 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 409 1 where
 D := ![[109, 250, 0, 384, 0, 1]]; D' := ![[109, 250, 0, 384, 0, 1]]
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
  w := ![![409, 0, 0, 0, 0], ![409, 0, 0, 2045, 0]]
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

def I419N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![419, 0, 0, 0, 0], ![269, 1, 0, 0, 0]] i)))

def I419N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![419, 0, 0, 0, 0], ![365, 26, 1, 0, 0]] i)))

def I419N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![419, 0, 0, 0, 0], ![31, 124, 1, 0, 0]] i)))

def P419P0 : CertificateIrreducibleZModOfList' 419 1 2 8 [269, 1] where
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
 g := ![![[], [81], [], [], [], [291], [], [293, 150, 1]]]
 h' := ![![[0, 1], [418], [9], [3], [29], [74], [349], [374], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P419P1 : CertificateIrreducibleZModOfList' 419 2 2 8 [365, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [393, 418], [0, 1]]
 g := ![![[403, 225], [240, 69], [190], [413], [236], [], [351], [393, 1]], ![[0, 194], [122, 350], [190], [413], [236], [], [351], [367, 418]]]
 h' := ![![[393, 418], [390, 15], [351, 250], [203, 52], [174, 149], [0, 115], [339], [272, 311], [0, 1]], ![[0, 1], [0, 404], [136, 169], [108, 367], [71, 270], [362, 304], [339], [147, 108], [393, 418]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62]]
 b := ![[], [403, 31]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P419P2 : CertificateIrreducibleZModOfList' 419 2 2 8 [31, 124, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [295, 418], [0, 1]]
 g := ![![[4, 402], [107, 202], [189], [1], [189], [93, 169], [243], [295, 1]], ![[17, 17], [199, 217], [189], [1], [189], [87, 250], [243], [171, 418]]]
 h' := ![![[295, 418], [35, 365], [331, 88], [18, 281], [412, 1], [50, 138], [310, 13], [73, 261], [0, 1]], ![[0, 1], [27, 54], [313, 331], [370, 138], [288, 418], [117, 281], [374, 406], [391, 158], [295, 418]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [409]]
 b := ![[], [109, 414]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A419 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 419 3 where
 D := ![[269, 1], [365, 26, 1], [31, 124, 1]]; D' := ![[269, 1], [365, 26, 1], [31, 124, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8, 8, 8]
 n := ![1, 2, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P419P0
  | 1 => exact P419P1
  | 2 => exact P419P2

def C4190 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A419.D 0) 419 where
  n := 1
  w := ![![419, 0, 0, 0, 0], ![269, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C4191 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A419.D 1) 419 where
  n := 2
  w := ![![419, 0, 0, 0, 0], ![365, 26, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C4192 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A419.D 2) 419 where
  n := 2
  w := ![![419, 0, 0, 0, 0], ![31, 124, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K419 : KummerData 419 ![I419N0, I419N1, I419N2] ![419, 175561, 175561] where
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


lemma PB1045I8_primes (p : ℕ) :
  p ∈ Set.range ![367, 373, 379, 383, 389, 397, 401, 409, 419] ↔ Nat.Prime p ∧ 359 < p ∧ p ≤ 419 := by
  rw [← List.mem_ofFn']
  convert primes_range 359 419 (by omega)
  decide

def PB1045I8 : PrimesBelowBoundCertificateInterval O 359 419 1045 where
  m := 9
  g := ![2, 2, 1, 2, 3, 2, 3, 1, 3]
  P := ![367, 373, 379, 383, 389, 397, 401, 409, 419]
  hP := PB1045I8_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I367N0, I367N1]
    · exact ![I373N0, I373N1]
    · exact ![I379N0]
    · exact ![I383N0, I383N1]
    · exact ![I389N0, I389N1, I389N2]
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
    · exact ![373, 19356878641]
    · exact ![7819807277899]
    · exact ![383, 21517662721]
    · exact ![389, 389, 58863869]
    · exact ![397, 24840596881]
    · exact ![401, 401, 64481201]
    · exact ![11445019581049]
    · exact ![419, 175561, 175561]
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
  β := ![I367N0, I373N0, I383N0, I389N0, I389N1, I397N0, I401N0, I401N1, I419N0]
  Il := ![[I367N0], [I373N0], [], [I383N0], [I389N0, I389N1], [I397N0], [I401N0, I401N1], [], [I419N0]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
