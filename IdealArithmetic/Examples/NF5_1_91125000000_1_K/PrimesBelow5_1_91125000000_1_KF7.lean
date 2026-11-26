
import IdealArithmetic.Examples.NF5_1_91125000000_1_K.RI5_1_91125000000_1_K
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 

instance hp311 : Fact (Nat.Prime 311) := {out := by norm_num}

def I311N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![311, 0, 0, 0, 0], ![15861, 622, 311, 0, 0]] i)))

def P311P0 : CertificateIrreducibleZModOfList' 311 5 2 8 [141, 97, 211, 0, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [194, 53, 281, 223, 215], [4, 287, 223, 97, 152], [67, 201, 56, 305, 191], [46, 80, 62, 308, 64], [0, 1]]
 g := ![![[67, 88, 296, 40, 160], [221, 17, 92, 156, 14], [63, 117, 209, 276, 112], [270, 58, 185, 63], [266, 235, 126, 148, 288], [214, 100, 0, 0, 1], [], []], ![[270, 174, 122, 159, 104, 293, 149, 297], [253, 215, 4, 222, 135, 73, 284, 51], [273, 270, 196, 255, 202, 276, 250, 293], [287, 224, 18, 13], [101, 137, 57, 114, 35, 130, 295, 58], [21, 22, 271, 77, 188, 153, 200, 167], [94, 138, 54, 98], [187, 131, 102, 197]], ![[23, 17, 307, 274, 241, 6, 96, 85], [17, 207, 52, 285, 130, 59, 255, 174], [177, 306, 99, 6, 200, 193, 82, 293], [121, 152, 83, 6], [158, 237, 245, 222, 146, 237, 60, 153], [269, 121, 147, 52, 266, 264, 55, 177], [163, 202, 189, 109], [182, 73, 254, 90]], ![[78, 62, 79, 105, 116, 116, 218, 51], [63, 79, 126, 24, 259, 299, 240, 222], [218, 306, 206, 54, 50, 122, 241, 255], [142, 222, 225, 6], [7, 102, 286, 45, 120, 253, 297, 151], [197, 179, 264, 134, 49, 191, 269, 116], [67, 34, 17, 141], [296, 280, 196, 94]], ![[95, 120, 156, 165, 43, 42, 105, 187], [277, 130, 38, 144, 202, 59, 253, 107], [290, 110, 48, 304, 107, 18, 134, 75], [290, 192, 279, 36], [275, 184, 11, 284, 106, 186, 178, 10], [138, 108, 211, 89, 236, 91, 78, 78], [122, 240, 302, 21], [240, 170, 238, 53]]]
 h' := ![![[194, 53, 281, 223, 215], [250, 260, 274, 129, 99], [136, 105, 200, 146, 90], [258, 271, 308, 243, 62], [125, 202, 87, 202, 109], [304, 285, 193, 48, 170], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[4, 287, 223, 97, 152], [68, 128, 179, 161, 123], [303, 98, 133, 105, 34], [284, 221, 197, 259, 227], [53, 193, 125, 156, 18], [264, 126, 233, 101, 281], [161, 83, 237, 31, 108], [73, 126, 196, 305, 151], [194, 53, 281, 223, 215]], ![[67, 201, 56, 305, 191], [292, 212, 238, 80, 137], [217, 216, 242, 70, 94], [134, 211, 81, 47, 191], [159, 148, 176, 61, 95], [20, 247, 256, 186, 148], [241, 174, 100, 7, 52], [167, 162, 57, 163, 137], [4, 287, 223, 97, 152]], ![[46, 80, 62, 308, 64], [85, 74, 13, 307, 285], [130, 93, 201, 1, 284], [45, 232, 289, 208, 243], [196, 233, 307, 304, 95], [156, 231, 84, 253, 224], [236, 305, 155, 299, 14], [73, 105, 6, 26, 102], [67, 201, 56, 305, 191]], ![[0, 1], [221, 259, 229, 256, 289], [66, 110, 157, 300, 120], [275, 309, 58, 176, 210], [51, 157, 238, 210, 305], [220, 44, 167, 34, 110], [218, 60, 130, 285, 136], [309, 229, 51, 128, 232], [46, 80, 62, 308, 64]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [181, 8, 244, 108], [], [], []]
 b := ![[], [48, 88, 210, 238, 40], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A311 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 311 1 where
 D := ![[141, 97, 211, 0, 0, 1]]; D' := ![[141, 97, 211, 0, 0, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8]
 n := ![5]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P311P0

def C3110 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A311.D 0) 311 where
  n := 5
  w := ![![311, 0, 0, 0, 0], ![15861, 622, 311, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K311 : KummerData 311 ![I311N0] ![2909390022551] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A311
  C := by
    intro i
    match i with
    | 0 => exact C3110
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 311 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp313 : Fact (Nat.Prime 313) := {out := by norm_num}

def I313N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![313, 0, 0, 0, 0], ![33, 1, 0, 0, 0]] i)))

def I313N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![313, 0, 0, 0, 0], ![48, 1, 0, 0, 0]] i)))

def I313N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![313, 0, 0, 0, 0], ![220, 1, 0, 0, 0]] i)))

def I313N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![313, 0, 0, 0, 0], ![146, 12, 1, 0, 0]] i)))

def P313P0 : CertificateIrreducibleZModOfList' 313 1 2 8 [33, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [294], [249], [44], [], [280, 1]]]
 h' := ![![[0, 1], [1], [1], [1], [234], [113], [277], [150], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P313P1 : CertificateIrreducibleZModOfList' 313 1 2 8 [48, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [150], [58], [27], [], [265, 1]]]
 h' := ![![[0, 1], [1], [1], [312], [33], [269], [249], [113], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P313P2 : CertificateIrreducibleZModOfList' 313 1 2 8 [220, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [35], [114], [294], [], [93, 1]]]
 h' := ![![[0, 1], [312], [288], [125], [273], [111], [79], [198], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P313P3 : CertificateIrreducibleZModOfList' 313 2 2 8 [146, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [301, 312], [0, 1]]
 g := ![![[133, 261], [27], [230], [140, 249], [227, 214], [254, 75], [144], [1]], ![[131, 52], [27], [230], [282, 64], [163, 99], [293, 238], [144], [1]]]
 h' := ![![[301, 312], [289, 95], [172, 64], [218, 196], [36, 113], [163, 215], [292, 211], [167, 301], [0, 1]], ![[0, 1], [88, 218], [30, 249], [57, 117], [245, 200], [87, 98], [264, 102], [311, 12], [301, 312]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37]]
 b := ![[], [111, 175]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A313 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 313 4 where
 D := ![[33, 1], [48, 1], [220, 1], [146, 12, 1]]; D' := ![[33, 1], [48, 1], [220, 1], [146, 12, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8, 8, 8, 8]
 n := ![1, 1, 1, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P313P0
  | 1 => exact P313P1
  | 2 => exact P313P2
  | 3 => exact P313P3

def C3130 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A313.D 0) 313 where
  n := 1
  w := ![![313, 0, 0, 0, 0], ![33, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C3131 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A313.D 1) 313 where
  n := 1
  w := ![![313, 0, 0, 0, 0], ![48, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C3132 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A313.D 2) 313 where
  n := 1
  w := ![![313, 0, 0, 0, 0], ![220, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C3133 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A313.D 3) 313 where
  n := 2
  w := ![![313, 0, 0, 0, 0], ![146, 12, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K313 : KummerData 313 ![I313N0, I313N1, I313N2, I313N3] ![313, 313, 313, 97969] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A313
  C := by
    intro i
    match i with
    | 0 => exact C3130
    | 1 => exact C3131
    | 2 => exact C3132
    | 3 => exact C3133
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 313 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp317 : Fact (Nat.Prime 317) := {out := by norm_num}

def I317N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![317, 0, 0, 0, 0], ![303, 1, 0, 0, 0]] i)))

def I317N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![317, 0, 0, 0, 0], ![684, 2224, 11091, -3010, 22728]] i)))

def P317P0 : CertificateIrreducibleZModOfList' 317 1 2 8 [303, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [144], [135], [82], [311], [], [14, 1]]]
 h' := ![![[0, 1], [316], [114], [305], [197], [233], [59], [196], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P317P1 : CertificateIrreducibleZModOfList' 317 4 2 8 [36, 108, 196, 14, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 55, 267, 286], [37, 213, 287, 77], [229, 48, 80, 271], [0, 1]]
 g := ![![[43, 110, 269, 83], [139, 22, 253], [212, 66, 144, 82], [31, 19, 70, 89], [307, 179, 27, 39], [128, 112, 208, 196], [1], []], ![[208, 50, 117, 292, 32, 43], [280, 121, 258], [177, 105, 73, 314, 101, 95], [192, 56, 106, 162, 69, 148], [138, 128, 194, 230, 307, 79], [183, 224, 314, 50, 139, 94], [246, 48, 223], [70, 107, 10]], ![[167, 162, 146, 145, 32, 169], [195, 285, 216], [311, 71, 158, 147, 160, 37], [300, 52, 47, 229, 132, 85], [163, 242, 272, 275, 98, 250], [257, 183, 82, 46, 138, 79], [204, 246, 99], [112, 183, 223]], ![[78, 226, 194, 236, 166, 197], [102, 12, 23], [126, 235, 51, 103, 37, 88], [198, 263, 115, 138, 205, 98], [101, 189, 288, 247, 87, 132], [29, 246, 46, 268, 22, 2], [40, 107, 54], [97, 105, 214]]]
 h' := ![![[37, 55, 267, 286], [10, 134, 305, 297], [293, 51, 192, 39], [152, 36, 181, 233], [43, 78, 205, 113], [147, 241, 193, 91], [281, 209, 121, 303], [0, 0, 1], [0, 1]], ![[37, 213, 287, 77], [125, 146, 270, 109], [78, 178, 184, 154], [102, 287, 212, 112], [205, 5, 307, 195], [107, 265, 141, 151], [78, 29, 135, 204], [117, 266, 0, 240], [37, 55, 267, 286]], ![[229, 48, 80, 271], [20, 4, 203, 280], [180, 6, 197, 220], [196, 100, 191, 207], [20, 155, 106, 156], [116, 166, 221, 51], [226, 269, 49, 106], [190, 248, 62, 187], [37, 213, 287, 77]], ![[0, 1], [106, 33, 173, 265], [99, 82, 61, 221], [196, 211, 50, 82], [94, 79, 16, 170], [39, 279, 79, 24], [188, 127, 12, 21], [131, 120, 254, 207], [229, 48, 80, 271]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [79, 137, 149], []]
 b := ![[], [], [283, 285, 152, 31], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A317 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 317 2 where
 D := ![[303, 1], [36, 108, 196, 14, 1]]; D' := ![[303, 1], [36, 108, 196, 14, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8, 8]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P317P0
  | 1 => exact P317P1

def C3170 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A317.D 0) 317 where
  n := 1
  w := ![![317, 0, 0, 0, 0], ![303, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C3171 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A317.D 1) 317 where
  n := 4
  w := ![![317, 0, 0, 0, 0], ![684, 2224, 11091, -3010, 22728]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K317 : KummerData 317 ![I317N0, I317N1] ![317, 10098039121] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A317
  C := by
    intro i
    match i with
    | 0 => exact C3170
    | 1 => exact C3171
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 317 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp331 : Fact (Nat.Prime 331) := {out := by norm_num}

def I331N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![331, 0, 0, 0, 0], ![15888, 662, 331, 0, 0]] i)))

def P331P0 : CertificateIrreducibleZModOfList' 331 5 2 8 [168, 137, 231, 0, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [299, 219, 167, 276, 30], [11, 200, 34, 120, 157], [217, 158, 124, 17, 239], [135, 84, 6, 249, 236], [0, 1]]
 g := ![![[79, 185, 278, 78, 216], [198, 152, 111, 66, 84], [130, 133, 29, 194], [255, 200, 38, 197, 313], [106, 56, 290, 266], [], [1], []], ![[320, 74, 329, 17, 19, 154, 192, 77], [292, 230, 222, 28, 175, 195, 222, 241], [285, 248, 230, 126], [300, 49, 320, 22, 84, 292, 5, 56], [161, 250, 30, 191], [197, 47, 291, 241], [287, 297, 293, 144, 242, 185, 193, 241], [34, 136, 10, 238]], ![[317, 201, 101, 123, 244, 304, 304, 96], [41, 328, 213, 61, 41, 72, 46, 297], [147, 238, 293, 230], [25, 154, 129, 107, 213, 258, 274, 125], [47, 175, 132, 46], [84, 166, 256, 24], [200, 180, 304, 266, 198, 327, 46, 172], [69, 251, 277, 155]], ![[103, 193, 274, 186, 323, 29, 200, 329], [73, 210, 149, 141, 244, 328, 72, 123], [301, 41, 264, 126], [283, 273, 91, 12, 63, 109, 208, 304], [28, 176, 330, 203], [17, 306, 43, 316], [163, 38, 169, 140, 280, 83, 59, 191], [2, 312, 182, 189]], ![[279, 146, 191, 44, 159, 330, 100, 159], [10, 48, 55, 60, 63, 118, 112, 35], [167, 128, 289, 233], [156, 67, 76, 65, 161, 262, 133, 13], [168, 276, 251, 113], [46, 126, 77, 233], [36, 141, 132, 101, 223, 110, 131, 35], [131, 288, 23, 88]]]
 h' := ![![[299, 219, 167, 276, 30], [167, 34, 232, 260, 116], [27, 246, 101, 102, 49], [190, 176, 69, 42, 288], [43, 24, 222, 10, 225], [89, 23, 64, 73, 70], [163, 194, 100], [0, 0, 1], [0, 1]], ![[11, 200, 34, 120, 157], [216, 15, 297, 121, 198], [23, 135, 177, 202, 268], [153, 63, 95, 150, 78], [92, 190, 243, 88, 276], [75, 126, 57, 284, 218], [140, 313, 79, 266, 204], [277, 184, 170, 255, 63], [299, 219, 167, 276, 30]], ![[217, 158, 124, 17, 239], [211, 157, 88, 201, 159], [43, 150, 109, 188, 2], [307, 89, 102, 215, 237], [13, 179, 311, 283, 257], [109, 147, 97, 65, 276], [126, 19, 19, 243, 149], [114, 112, 156, 190, 157], [11, 200, 34, 120, 157]], ![[135, 84, 6, 249, 236], [153, 288, 77, 44, 325], [111, 315, 262, 48, 170], [325, 156, 47, 202, 253], [24, 135, 181, 97, 174], [147, 176, 234, 323, 269], [149, 262, 214, 111, 115], [82, 325, 33, 223, 269], [217, 158, 124, 17, 239]], ![[0, 1], [287, 168, 299, 36, 195], [38, 147, 13, 122, 173], [60, 178, 18, 53, 137], [227, 134, 36, 184, 61], [115, 190, 210, 248, 160], [237, 205, 250, 42, 194], [189, 41, 302, 325, 173], [135, 84, 6, 249, 236]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13, 306, 99, 123], [], [], []]
 b := ![[], [182, 223, 100, 94, 29], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A331 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 331 1 where
 D := ![[168, 137, 231, 0, 0, 1]]; D' := ![[168, 137, 231, 0, 0, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8]
 n := ![5]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P331P0

def C3310 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A331.D 0) 331 where
  n := 5
  w := ![![331, 0, 0, 0, 0], ![15888, 662, 331, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K331 : KummerData 331 ![I331N0] ![3973195810651] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A331
  C := by
    intro i
    match i with
    | 0 => exact C3310
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 331 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp337 : Fact (Nat.Prime 337) := {out := by norm_num}

def I337N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![337, 0, 0, 0, 0], ![315, 33, 1, 0, 0]] i)))

def I337N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![337, 0, 0, 0, 0], ![255, 101, 304, 2, 0]] i)))

def P337P0 : CertificateIrreducibleZModOfList' 337 2 2 8 [315, 33, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [304, 336], [0, 1]]
 g := ![![[167, 222], [311], [165], [78], [239, 243], [175], [18, 78], [1]], ![[255, 115], [311], [165], [78], [308, 94], [175], [140, 259], [1]]]
 h' := ![![[304, 336], [17, 151], [297, 131], [126, 204], [203, 304], [254, 68], [59, 258], [22, 304], [0, 1]], ![[0, 1], [89, 186], [18, 206], [134, 133], [281, 33], [32, 269], [307, 79], [100, 33], [304, 336]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [69]]
 b := ![[], [148, 203]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P337P1 : CertificateIrreducibleZModOfList' 337 3 2 8 [255, 100, 304, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [150, 98, 215], [220, 238, 122], [0, 1]]
 g := ![![[158, 133, 165], [61, 79], [289, 287], [289, 41], [263, 57, 300], [270, 227], [315, 33, 1], []], ![[124, 177, 256, 17], [307, 164], [80, 196], [85, 95], [169, 301, 21, 59], [2, 41], [202, 232, 172, 291], [178, 56]], ![[108, 295, 102, 90], [213, 1], [66, 289], [268, 169], [206, 173, 203, 69], [183, 187], [58, 9, 130, 276], [271, 56]]]
 h' := ![![[150, 98, 215], [73, 165, 133], [183, 74, 42], [112, 265, 31], [335, 205, 147], [242, 116, 113], [218, 188, 100], [0, 0, 1], [0, 1]], ![[220, 238, 122], [310, 100, 66], [243, 173, 294], [228, 180, 323], [196, 200, 203], [23, 33, 273], [14, 141, 190], [26, 16, 238], [150, 98, 215]], ![[0, 1], [176, 72, 138], [137, 90, 1], [241, 229, 320], [89, 269, 324], [276, 188, 288], [155, 8, 47], [189, 321, 98], [220, 238, 122]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [238, 190], []]
 b := ![[], [38, 6, 101], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A337 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 337 2 where
 D := ![[315, 33, 1], [255, 100, 304, 1]]; D' := ![[315, 33, 1], [255, 100, 304, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8, 8]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P337P0
  | 1 => exact P337P1

def C3370 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A337.D 0) 337 where
  n := 2
  w := ![![337, 0, 0, 0, 0], ![315, 33, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C3371 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A337.D 1) 337 where
  n := 3
  w := ![![337, 0, 0, 0, 0], ![255, 101, 304, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K337 : KummerData 337 ![I337N0, I337N1] ![113569, 38272753] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A337
  C := by
    intro i
    match i with
    | 0 => exact C3370
    | 1 => exact C3371
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 337 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp347 : Fact (Nat.Prime 347) := {out := by norm_num}

def I347N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![347, 0, 0, 0, 0], ![319, 1, 0, 0, 0]] i)))

def I347N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![347, 0, 0, 0, 0], ![912, 2468, 10985, -2982, 22728]] i)))

def P347P0 : CertificateIrreducibleZModOfList' 347 1 2 8 [319, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [285], [], [108], [293], [], [119], [28, 1]]]
 h' := ![![[0, 1], [346], [85], [248], [223], [306], [209], [90], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P347P1 : CertificateIrreducibleZModOfList' 347 4 2 8 [264, 338, 90, 28, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [69, 265, 234, 173], [218, 184, 317, 205], [32, 244, 143, 316], [0, 1]]
 g := ![![[51, 62, 143, 185], [242, 140, 159, 201], [44, 250, 59], [326, 278, 287, 202], [248, 10, 126, 52], [284], [319, 1], []], ![[284, 21, 292, 271, 60, 48], [322, 67, 266, 67, 228, 277], [136, 4, 85], [179, 216, 85, 33, 278, 219], [202, 7, 250, 264, 262, 39], [266, 257, 34], [40, 342, 36, 179, 72, 67], [318, 106, 87]], ![[333, 23, 276, 91, 188, 319], [192, 129, 192, 189, 193, 259], [320, 166, 279], [134, 42, 181, 337, 12, 110], [195, 77, 12, 47, 249, 285], [334, 174, 332], [87, 37, 100, 224, 304, 75], [176, 169, 38]], ![[64, 186, 8, 93, 132, 50], [231, 307, 26, 0, 21, 171], [274, 194, 250], [110, 96, 118, 263, 293, 318], [69, 336, 283, 11, 186, 254], [225, 61, 89], [156, 212, 207, 187, 272, 265], [259, 314, 267]]]
 h' := ![![[69, 265, 234, 173], [307, 56, 23, 78], [246, 211, 188, 44], [339, 159, 206, 104], [111, 138, 233, 152], [244, 31, 58, 235], [105, 178, 100], [0, 0, 1], [0, 1]], ![[218, 184, 317, 205], [172, 50, 232, 286], [223, 15, 9, 54], [115, 28, 16, 248], [272, 324, 170, 331], [17, 191, 90, 160], [29, 25, 315, 301], [272, 344, 180, 108], [69, 265, 234, 173]], ![[32, 244, 143, 316], [92, 217, 336, 187], [23, 136, 159, 303], [23, 18, 328, 64], [148, 205, 49, 3], [340, 289, 284, 204], [210, 188, 122, 218], [19, 63, 242, 248], [218, 184, 317, 205]], ![[0, 1], [135, 24, 103, 143], [46, 332, 338, 293], [317, 142, 144, 278], [254, 27, 242, 208], [27, 183, 262, 95], [319, 303, 157, 175], [313, 287, 271, 338], [32, 244, 143, 316]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [218, 111, 233], []]
 b := ![[], [], [161, 53, 320, 268], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A347 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 347 2 where
 D := ![[319, 1], [264, 338, 90, 28, 1]]; D' := ![[319, 1], [264, 338, 90, 28, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8, 8]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P347P0
  | 1 => exact P347P1

def C3470 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A347.D 0) 347 where
  n := 1
  w := ![![347, 0, 0, 0, 0], ![319, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C3471 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A347.D 1) 347 where
  n := 4
  w := ![![347, 0, 0, 0, 0], ![912, 2468, 10985, -2982, 22728]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K347 : KummerData 347 ![I347N0, I347N1] ![347, 14498327281] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A347
  C := by
    intro i
    match i with
    | 0 => exact C3470
    | 1 => exact C3471
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 347 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp349 : Fact (Nat.Prime 349) := {out := by norm_num}

def I349N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![349, 0, 0, 0, 0], ![298, 1, 0, 0, 0]] i)))

def I349N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![349, 0, 0, 0, 0], ![324, 1, 0, 0, 0]] i)))

def I349N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![349, 0, 0, 0, 0], ![78, 314, 76, 2, 0]] i)))

def P349P0 : CertificateIrreducibleZModOfList' 349 1 2 8 [298, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [219], [168], [145], [], [185], [51, 1]]]
 h' := ![![[0, 1], [1], [1], [192], [66], [144], [12], [158], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P349P1 : CertificateIrreducibleZModOfList' 349 1 2 8 [324, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [14], [67], [192], [], [94], [25, 1]]]
 h' := ![![[0, 1], [1], [1], [279], [263], [273], [256], [276], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P349P2 : CertificateIrreducibleZModOfList' 349 3 2 8 [78, 313, 76, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [50, 83, 105], [223, 265, 244], [0, 1]]
 g := ![![[62, 125, 78], [249, 73], [191, 293, 27], [14, 112, 180], [112, 253, 81], [73, 228], [228, 273, 1], []], ![[35, 184, 254, 8], [209, 293], [261, 28, 161, 218], [345, 203, 24, 342], [75, 169, 345, 101], [274, 285], [227, 319, 328, 302], [29, 206]], ![[283, 173, 160, 50], [222, 346], [181, 315, 86, 278], [21, 275, 123, 8], [96, 51, 26, 166], [52, 340], [255, 24, 170, 132], [239, 206]]]
 h' := ![![[50, 83, 105], [137, 259, 232], [109, 7, 90], [304, 265, 146], [338, 315, 23], [115, 245, 340], [15, 176, 100], [0, 0, 1], [0, 1]], ![[223, 265, 244], [248, 270, 29], [241, 238, 155], [140, 41, 205], [273, 274, 82], [102, 232, 306], [158, 73, 308], [238, 256, 265], [50, 83, 105]], ![[0, 1], [59, 169, 88], [171, 104, 104], [26, 43, 347], [334, 109, 244], [72, 221, 52], [332, 100, 290], [26, 93, 83], [223, 265, 244]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [339, 303], []]
 b := ![[], [232, 61, 37], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A349 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 349 3 where
 D := ![[298, 1], [324, 1], [78, 313, 76, 1]]; D' := ![[298, 1], [324, 1], [78, 313, 76, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8, 8, 8]
 n := ![1, 1, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P349P0
  | 1 => exact P349P1
  | 2 => exact P349P2

def C3490 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A349.D 0) 349 where
  n := 1
  w := ![![349, 0, 0, 0, 0], ![298, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C3491 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A349.D 1) 349 where
  n := 1
  w := ![![349, 0, 0, 0, 0], ![324, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C3492 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A349.D 2) 349 where
  n := 3
  w := ![![349, 0, 0, 0, 0], ![78, 314, 76, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K349 : KummerData 349 ![I349N0, I349N1, I349N2] ![349, 349, 42508549] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A349
  C := by
    intro i
    match i with
    | 0 => exact C3490
    | 1 => exact C3491
    | 2 => exact C3492
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 349 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp353 : Fact (Nat.Prime 353) := {out := by norm_num}

def I353N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![353, 0, 0, 0, 0], ![61, 1, 0, 0, 0]] i)))

def I353N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![353, 0, 0, 0, 0], ![697, 2645, 11086, -2454, 22728]] i)))

def P353P0 : CertificateIrreducibleZModOfList' 353 1 2 8 [61, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [], [], [135], [122], [292, 1]]]
 h' := ![![[0, 1], [1], [1], [352], [42], [237], [324], [191], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P353P1 : CertificateIrreducibleZModOfList' 353 4 2 8 [49, 251, 191, 292, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [232, 250, 228, 92], [290, 216, 147, 27], [245, 239, 331, 234], [0, 1]]
 g := ![![[233, 9, 87, 43], [214, 48, 25], [165, 155, 41], [119, 340, 289], [286, 310, 99], [175, 116], [61, 1], []], ![[90, 346, 168, 146, 102, 23], [125, 192, 159], [252, 24, 283], [13, 274, 237], [307, 313, 128], [43, 138, 129, 126, 4, 324], [162, 147, 140, 252, 22, 191], [25, 163, 345]], ![[15, 17, 136, 29, 117, 104], [294, 291, 25], [196, 345, 155], [70, 347, 267], [23, 26, 121], [332, 346, 352, 207, 282, 96], [193, 247, 271, 279, 142, 95], [346, 163, 23]], ![[195, 168, 202, 143, 109, 71], [150, 26, 122], [26, 264, 8], [150, 216, 218], [249, 30, 256], [264, 45, 285, 328, 265, 10], [119, 263, 279, 121, 52, 251], [13, 324, 41]]]
 h' := ![![[232, 250, 228, 92], [329, 28, 173, 211], [15, 246, 170, 5], [263, 299, 262, 234], [125, 80, 21, 17], [250, 208, 13, 282], [188, 172, 100], [0, 0, 1], [0, 1]], ![[290, 216, 147, 27], [186, 179, 85, 177], [37, 191, 158, 152], [33, 11, 15, 49], [101, 205, 45, 317], [32, 261, 97, 76], [50, 274, 54, 235], [2, 74, 152, 243], [232, 250, 228, 92]], ![[245, 239, 331, 234], [139, 338, 18, 33], [57, 122, 159, 5], [51, 9, 163, 89], [294, 36, 217, 178], [350, 55, 131, 11], [129, 162, 1, 105], [76, 89, 139, 177], [290, 216, 147, 27]], ![[0, 1], [220, 161, 77, 285], [235, 147, 219, 191], [34, 34, 266, 334], [335, 32, 70, 194], [74, 182, 112, 337], [249, 98, 198, 13], [84, 190, 61, 286], [245, 239, 331, 234]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [162, 24, 321], []]
 b := ![[], [], [154, 41, 131, 145], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A353 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 353 2 where
 D := ![[61, 1], [49, 251, 191, 292, 1]]; D' := ![[61, 1], [49, 251, 191, 292, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8, 8]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P353P0
  | 1 => exact P353P1

def C3530 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A353.D 0) 353 where
  n := 1
  w := ![![353, 0, 0, 0, 0], ![61, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C3531 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A353.D 1) 353 where
  n := 4
  w := ![![353, 0, 0, 0, 0], ![697, 2645, 11086, -2454, 22728]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K353 : KummerData 353 ![I353N0, I353N1] ![353, 15527402881] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A353
  C := by
    intro i
    match i with
    | 0 => exact C3530
    | 1 => exact C3531
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 353 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp359 : Fact (Nat.Prime 359) := {out := by norm_num}

def I359N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![359, 0, 0, 0, 0], ![15796, 718, 359, 0, 0]] i)))

def P359P0 : CertificateIrreducibleZModOfList' 359 5 2 8 [76, 193, 259, 0, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [269, 189, 35, 358, 26], [9, 124, 325, 105, 285], [357, 285, 154, 130, 137], [83, 119, 204, 125, 270], [0, 1]]
 g := ![![[124, 296, 129, 163, 203], [76, 324, 10, 104, 4], [1, 208, 136, 69, 24], [239, 58, 46, 303], [129, 74, 263, 146], [307], [1], []], ![[338, 72, 358, 107, 233, 344, 154, 71], [235, 134, 34, 37, 31, 185, 220, 343], [82, 279, 329, 89, 280, 187, 337, 197], [300, 102, 326, 303], [35, 265, 22, 320], [248, 350, 205, 95, 241, 83, 354, 314], [258, 52, 236, 232, 319, 264, 331, 189], [173, 26, 307, 317]], ![[309, 252, 349, 322, 6, 86, 308, 299], [303, 188, 65, 18, 234, 56, 232, 267], [83, 344, 122, 226, 251, 116, 230, 332], [8, 24, 296, 340], [330, 154, 242, 302], [216, 231, 219, 124, 230, 155, 114, 223], [245, 158, 302, 102, 142, 86, 348, 277], [122, 261, 256, 91]], ![[139, 21, 114, 105, 337, 36, 141, 355], [307, 186, 264, 82, 304, 268, 312, 332], [214, 276, 193, 321, 258, 23, 322, 269], [166, 319, 145, 102], [83, 69, 194, 100], [173, 174, 294, 47, 45, 210, 28, 31], [307, 208, 88, 193, 281, 318, 139, 190], [67, 220, 79, 101]], ![[281, 356, 21, 212, 330, 336, 72, 48], [117, 44, 338, 115, 268, 95, 43, 41], [343, 69, 251, 334, 26, 198, 266, 6], [313, 84, 181, 270], [316, 63, 215, 250], [47, 30, 34, 311, 49, 99, 347, 288], [57, 16, 7, 222, 166, 193, 339, 247], [167, 135, 8, 23]]]
 h' := ![![[269, 189, 35, 358, 26], [327, 230, 168, 289, 145], [283, 171, 13, 26, 2], [138, 33, 57, 243, 91], [257, 90, 206, 79, 73], [3, 16, 83, 150, 172], [283, 166, 100], [0, 0, 1], [0, 1]], ![[9, 124, 325, 105, 285], [318, 347, 60, 96, 129], [122, 60, 65, 96, 130], [198, 218, 310, 210, 352], [154, 67, 270, 283, 286], [115, 214, 299, 292, 107], [16, 34, 163, 297, 289], [337, 261, 62, 159, 150], [269, 189, 35, 358, 26]], ![[357, 285, 154, 130, 137], [141, 119, 108, 303, 46], [292, 160, 43, 243, 271], [146, 185, 65, 249, 32], [353, 33, 165, 186, 78], [286, 194, 131, 49, 149], [281, 338, 60, 117, 344], [143, 135, 215, 211, 155], [9, 124, 325, 105, 285]], ![[83, 119, 204, 125, 270], [96, 141, 331, 207, 47], [58, 207, 106, 158, 176], [182, 257, 87, 85, 281], [70, 350, 23, 72, 183], [224, 142, 28, 98, 349], [213, 324, 195, 149, 90], [297, 83, 73, 177, 233], [357, 285, 154, 130, 137]], ![[0, 1], [284, 240, 51, 182, 351], [95, 120, 132, 195, 139], [161, 25, 199, 290, 321], [105, 178, 54, 98, 98], [276, 152, 177, 129, 300], [263, 215, 200, 155, 354], [300, 239, 8, 171, 180], [83, 119, 204, 125, 270]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [283, 82, 207, 231], [], [], []]
 b := ![[], [227, 181, 347, 108, 143], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A359 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 359 1 where
 D := ![[76, 193, 259, 0, 0, 1]]; D' := ![[76, 193, 259, 0, 0, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8]
 n := ![5]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P359P0

def C3590 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A359.D 0) 359 where
  n := 5
  w := ![![359, 0, 0, 0, 0], ![15796, 718, 359, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K359 : KummerData 359 ![I359N0] ![5963102065799] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A359
  C := by
    intro i
    match i with
    | 0 => exact C3590
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 359 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


lemma PB18792I7_primes (p : ℕ) :
  p ∈ Set.range ![311, 313, 317, 331, 337, 347, 349, 353, 359] ↔ Nat.Prime p ∧ 307 < p ∧ p ≤ 359 := by
  rw [← List.mem_ofFn']
  convert primes_range 307 359 (by omega)
  decide

def PB18792I7 : PrimesBelowBoundCertificateInterval O 307 359 18792 where
  m := 9
  g := ![1, 4, 2, 1, 2, 2, 3, 2, 1]
  P := ![311, 313, 317, 331, 337, 347, 349, 353, 359]
  hP := PB18792I7_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I311N0]
    · exact ![I313N0, I313N1, I313N2, I313N3]
    · exact ![I317N0, I317N1]
    · exact ![I331N0]
    · exact ![I337N0, I337N1]
    · exact ![I347N0, I347N1]
    · exact ![I349N0, I349N1, I349N2]
    · exact ![I353N0, I353N1]
    · exact ![I359N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · convert (containsPrimesAbove_of_KummerData K311) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K313) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K317) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K331) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K337) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K347) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K349) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K353) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K359) <;> rfl
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2909390022551]
    · exact ![313, 313, 313, 97969]
    · exact ![317, 10098039121]
    · exact ![3973195810651]
    · exact ![113569, 38272753]
    · exact ![347, 14498327281]
    · exact ![349, 349, 42508549]
    · exact ![353, 15527402881]
    · exact ![5963102065799]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact (card_quot_of_KummerData K311)
    · exact (card_quot_of_KummerData K313)
    · exact (card_quot_of_KummerData K317)
    · exact (card_quot_of_KummerData K331)
    · exact (card_quot_of_KummerData K337)
    · exact (card_quot_of_KummerData K347)
    · exact (card_quot_of_KummerData K349)
    · exact (card_quot_of_KummerData K353)
    · exact (card_quot_of_KummerData K359)
  β := ![I313N0, I313N1, I313N2, I317N0, I347N0, I349N0, I349N1, I353N0]
  Il := ![[], [I313N0, I313N1, I313N2], [I317N0], [], [], [I347N0], [I349N0, I349N1], [I353N0], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
