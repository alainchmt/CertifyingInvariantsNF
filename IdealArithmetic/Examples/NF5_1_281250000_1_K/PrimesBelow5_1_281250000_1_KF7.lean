
import IdealArithmetic.Examples.NF5_1_281250000_1_K.RI5_1_281250000_1_K
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 

instance hp311 : Fact (Nat.Prime 311) := {out := by norm_num}

def I311N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![311, 0, 0, 0, 0], ![45, 1, 0, 0, 0]] i)))

def I311N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![311, 0, 0, 0, 0], ![110, 79, 1, 0, 0]] i)))

def I311N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![311, 0, 0, 0, 0], ![179, 187, 1, 0, 0]] i)))

def P311P0 : CertificateIrreducibleZModOfList' 311 1 2 8 [45, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [235], [278], [], [64], [14], [], [266, 1]]]
 h' := ![![[0, 1], [310], [241], [30], [230], [303], [90], [159], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P311P1 : CertificateIrreducibleZModOfList' 311 2 2 8 [110, 79, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [232, 310], [0, 1]]
 g := ![![[258, 105], [288, 278], [277, 89], [109], [95, 130], [23, 7], [21], [1]], ![[49, 206], [96, 33], [88, 222], [109], [88, 181], [92, 304], [21], [1]]]
 h' := ![![[232, 310], [42, 224], [8, 30], [276, 20], [124, 174], [269, 21], [149, 171], [201, 232], [0, 1]], ![[0, 1], [73, 87], [126, 281], [251, 291], [62, 137], [165, 290], [13, 140], [222, 79], [232, 310]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [288]]
 b := ![[], [90, 144]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P311P2 : CertificateIrreducibleZModOfList' 311 2 2 8 [179, 187, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [124, 310], [0, 1]]
 g := ![![[180, 139], [308, 175], [34, 193], [274], [108, 127], [72, 52], [137], [1]], ![[0, 172], [238, 136], [19, 118], [274], [306, 184], [300, 259], [137], [1]]]
 h' := ![![[124, 310], [226, 254], [134, 78], [104, 229], [261, 98], [174, 48], [54, 275], [132, 124], [0, 1]], ![[0, 1], [0, 57], [165, 233], [199, 82], [284, 213], [217, 263], [255, 36], [269, 187], [124, 310]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65]]
 b := ![[], [162, 188]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A311 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 311 3 where
 D := ![[45, 1], [110, 79, 1], [179, 187, 1]]; D' := ![[45, 1], [110, 79, 1], [179, 187, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8, 8, 8]
 n := ![1, 2, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P311P0
  | 1 => exact P311P1
  | 2 => exact P311P2

def C3110 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A311.D 0) 311 where
  n := 1
  w := ![![311, 0, 0, 0, 0], ![45, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C3111 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A311.D 1) 311 where
  n := 2
  w := ![![311, 0, 0, 0, 0], ![110, 79, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C3112 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A311.D 2) 311 where
  n := 2
  w := ![![311, 0, 0, 0, 0], ![179, 187, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K311 : KummerData 311 ![I311N0, I311N1, I311N2] ![311, 96721, 96721] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A311
  C := by
    intro i
    match i with
    | 0 => exact C3110
    | 1 => exact C3111
    | 2 => exact C3112
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 311 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp313 : Fact (Nat.Prime 313) := {out := by norm_num}

def I313N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![313, 0, 0, 0, 0], ![54, 1, 0, 0, 0]] i)))

def I313N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![313, 0, 0, 0, 0], ![125, 1, 0, 0, 0]] i)))

def I313N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![313, 0, 0, 0, 0], ![279, 1, 0, 0, 0]] i)))

def I313N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![313, 0, 0, 0, 0], ![304, 168, 1, 0, 0]] i)))

def P313P0 : CertificateIrreducibleZModOfList' 313 1 2 8 [54, 1] where
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
 g := ![![[], [], [], [99], [312], [214], [], [259, 1]]]
 h' := ![![[0, 1], [1], [312], [288], [54], [25], [98], [99], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P313P1 : CertificateIrreducibleZModOfList' 313 1 2 8 [125, 1] where
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
 g := ![![[], [], [], [25], [288], [1], [], [188, 1]]]
 h' := ![![[0, 1], [312], [25], [5], [308], [188], [312], [288], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P313P2 : CertificateIrreducibleZModOfList' 313 1 2 8 [279, 1] where
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
 g := ![![[], [], [], [116], [8], [228], [], [34, 1]]]
 h' := ![![[0, 1], [312], [288], [188], [272], [240], [139], [217], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P313P3 : CertificateIrreducibleZModOfList' 313 2 2 8 [304, 168, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [145, 312], [0, 1]]
 g := ![![[190, 139], [99], [24], [301, 256], [255, 261], [302, 114], [54], [1]], ![[0, 174], [99], [24], [174, 57], [227, 52], [243, 199], [54], [1]]]
 h' := ![![[145, 312], [148, 217], [299, 259], [205, 112], [104, 297], [214, 95], [254, 111], [9, 145], [0, 1]], ![[0, 1], [0, 96], [294, 54], [169, 201], [288, 16], [217, 218], [73, 202], [63, 168], [145, 312]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [306]]
 b := ![[], [19, 153]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A313 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 313 4 where
 D := ![[54, 1], [125, 1], [279, 1], [304, 168, 1]]; D' := ![[54, 1], [125, 1], [279, 1], [304, 168, 1]]
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
  w := ![![313, 0, 0, 0, 0], ![54, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C3131 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A313.D 1) 313 where
  n := 1
  w := ![![313, 0, 0, 0, 0], ![125, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C3132 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A313.D 2) 313 where
  n := 1
  w := ![![313, 0, 0, 0, 0], ![279, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C3133 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A313.D 3) 313 where
  n := 2
  w := ![![313, 0, 0, 0, 0], ![304, 168, 1, 0, 0]]
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

def I317N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![317, 0, 0, 0, 0], ![116, 1, 0, 0, 0]] i)))

def I317N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![317, 0, 0, 0, 0], ![63, 59, 122, 1005, 10]] i)))

def P317P0 : CertificateIrreducibleZModOfList' 317 1 2 8 [116, 1] where
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
 g := ![![[], [], [236], [95], [161], [160], [], [201, 1]]]
 h' := ![![[0, 1], [316], [203], [75], [27], [143], [193], [142], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P317P1 : CertificateIrreducibleZModOfList' 317 4 2 8 [63, 59, 117, 201, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [187, 31, 292, 227], [80, 179, 315, 72], [166, 106, 27, 18], [0, 1]]
 g := ![![[309, 61, 269, 66], [296, 145, 95], [90, 305, 223, 142], [257, 125, 257, 1], [218, 188, 212, 228], [54, 121, 106, 142], [1], []], ![[126, 159, 81, 75, 227, 138], [41, 46, 24], [257, 157, 132, 220, 34, 223], [137, 134, 270, 264, 64, 175], [102, 77, 98, 294, 212, 232], [122, 205, 59, 155, 83, 113], [139, 225, 204], [272, 74, 175]], ![[224, 11, 24, 172, 103, 271], [122, 270, 61], [9, 4, 80, 135, 19, 111], [98, 291, 240, 89, 257, 41], [227, 6, 240, 202, 91, 209], [145, 278, 72, 245, 296, 303], [298, 129, 141], [244, 24, 112]], ![[32, 87, 10, 292, 298, 255], [55, 233, 278], [59, 142, 178, 66, 125, 62], [66, 230, 113, 162, 147, 198], [112, 23, 87, 227, 274, 166], [81, 195, 66, 126, 246, 162], [122, 45, 223], [182, 199, 7]]]
 h' := ![![[187, 31, 292, 227], [83, 181, 42, 180], [36, 143, 219, 290], [293, 251, 221, 116], [214, 271, 88, 316], [85, 134, 296, 202], [254, 258, 200, 116], [0, 0, 1], [0, 1]], ![[80, 179, 315, 72], [76, 219, 33, 297], [272, 178, 26, 179], [137, 57, 20, 258], [60, 259, 112, 176], [258, 35, 206, 204], [23, 242, 18, 223], [81, 77, 188, 183], [187, 31, 292, 227]], ![[166, 106, 27, 18], [45, 74, 8, 239], [45, 143, 123, 78], [268, 284, 2, 98], [229, 26, 194, 310], [201, 218, 3, 129], [269, 128, 0, 292], [221, 52, 90, 211], [80, 179, 315, 72]], ![[0, 1], [201, 160, 234, 235], [42, 170, 266, 87], [258, 42, 74, 162], [247, 78, 240, 149], [266, 247, 129, 99], [145, 6, 99, 3], [240, 188, 38, 240], [166, 106, 27, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [190, 63, 313], []]
 b := ![[], [], [314, 233, 250, 229], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A317 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 317 2 where
 D := ![[116, 1], [63, 59, 117, 201, 1]]; D' := ![[116, 1], [63, 59, 117, 201, 1]]
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
  w := ![![317, 0, 0, 0, 0], ![116, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C3171 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A317.D 1) 317 where
  n := 4
  w := ![![317, 0, 0, 0, 0], ![63, 59, 122, 1005, 10]]
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

def I331N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![331, 0, 0, 0, 0], ![331, 0, 0, 1655, 0]] i)))

def P331P0 : CertificateIrreducibleZModOfList' 331 5 2 8 [31, 250, 0, 306, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [160, 196, 286, 136, 72], [177, 330, 108, 27, 286], [107, 1, 330, 86, 243], [218, 134, 269, 82, 61], [0, 1]]
 g := ![![[155, 131, 81, 262, 303], [131, 65, 162, 135, 58], [11, 195, 95, 96], [217, 118, 8, 283, 88], [142, 116, 208, 132], [0, 294], [1], []], ![[304, 230, 157, 135, 50, 71, 330, 99], [314, 2, 117, 312, 300, 252, 269, 140], [284, 56, 44, 268], [288, 327, 311, 143, 99, 14, 122, 137], [180, 31, 235, 180], [90, 95, 42, 161], [68, 145, 213, 98, 181, 227, 0, 86], [147, 279, 55, 219]], ![[232, 289, 84, 157, 125, 168, 18, 218], [103, 197, 74, 10, 302, 50, 264, 264], [205, 155, 97, 45], [305, 279, 177, 152, 115, 195, 261, 278], [280, 291, 230, 150], [246, 303, 62, 109], [143, 100, 156, 85, 140, 70, 168, 315], [118, 259, 218, 39]], ![[98, 222, 259, 180, 111, 252, 259, 47], [165, 226, 190, 300, 19, 101, 277, 187], [218, 285, 52, 216], [202, 205, 275, 303, 38, 228, 309, 38], [16, 176, 266, 245], [120, 192, 108, 85], [244, 110, 311, 173, 90, 5, 107, 285], [247, 255, 90, 131]], ![[208, 23, 107, 158, 84, 134, 85, 211], [176, 199, 35, 256, 18, 204, 280, 135], [205, 159, 7, 54], [260, 277, 106, 109, 113, 52, 83, 247], [80, 271, 71, 74], [4, 115, 62, 173], [24, 286, 243, 279, 158, 248, 64, 174], [86, 167, 74, 80]]]
 h' := ![![[160, 196, 286, 136, 72], [242, 122, 319, 68, 36], [185, 299, 231, 138, 148], [224, 7, 152, 144, 298], [263, 43, 73, 275, 95], [299, 97, 254, 105, 146], [300, 81, 0, 25], [0, 0, 1], [0, 1]], ![[177, 330, 108, 27, 286], [293, 221, 178, 135, 136], [155, 207, 8, 55, 127], [213, 287, 16, 123, 54], [18, 309, 13, 266, 145], [77, 150, 317, 108, 257], [259, 82, 236, 137, 278], [190, 109, 225, 79, 150], [160, 196, 286, 136, 72]], ![[107, 1, 330, 86, 243], [88, 67, 92, 103, 58], [262, 116, 91, 31, 287], [268, 119, 261, 301, 37], [225, 58, 126, 96, 297], [300, 182, 66, 73, 124], [225, 66, 294, 182, 42], [198, 182, 156, 275, 18], [177, 330, 108, 27, 286]], ![[218, 134, 269, 82, 61], [287, 319, 262, 140, 212], [194, 202, 84, 124, 303], [1, 158, 159, 268, 215], [111, 106, 280, 9, 242], [291, 137, 269, 240, 24], [286, 147, 27, 36, 167], [151, 69, 109, 2, 313], [107, 1, 330, 86, 243]], ![[0, 1], [94, 264, 142, 216, 220], [22, 169, 248, 314, 128], [95, 91, 74, 157, 58], [294, 146, 170, 16, 214], [78, 96, 87, 136, 111], [99, 286, 105, 282, 175], [173, 302, 171, 306, 181], [218, 134, 269, 82, 61]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [213, 202, 232, 301], [], [], []]
 b := ![[], [87, 33, 145, 91, 28], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A331 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 331 1 where
 D := ![[31, 250, 0, 306, 0, 1]]; D' := ![[31, 250, 0, 306, 0, 1]]
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
  w := ![![331, 0, 0, 0, 0], ![331, 0, 0, 1655, 0]]
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

def I337N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![337, 0, 0, 0, 0], ![135, 73, 1, 0, 0]] i)))

def I337N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![337, 0, 0, 0, 0], ![185, 114, 264, 5, 0]] i)))

def P337P0 : CertificateIrreducibleZModOfList' 337 2 2 8 [135, 73, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [264, 336], [0, 1]]
 g := ![![[28, 81], [98], [49], [28], [142, 211], [131], [45, 274], [1]], ![[181, 256], [98], [49], [28], [241, 126], [131], [263, 63], [1]]]
 h' := ![![[264, 336], [138, 328], [15, 182], [100, 7], [39, 238], [257, 124], [328, 192], [202, 264], [0, 1]], ![[0, 1], [121, 9], [209, 155], [263, 330], [189, 99], [304, 213], [129, 145], [139, 73], [264, 336]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [261]]
 b := ![[], [298, 299]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P337P1 : CertificateIrreducibleZModOfList' 337 3 2 8 [185, 114, 264, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [317, 190, 75], [93, 146, 262], [0, 1]]
 g := ![![[328, 44, 1], [187, 168], [166, 103], [321, 37], [99, 0, 148], [10, 54], [160, 73, 1], []], ![[0, 140, 284, 78], [69, 78], [41, 48], [215, 14], [146, 152, 216, 256], [46, 155], [207, 311, 282, 309], [14, 233]], ![[200, 239, 132, 206], [166, 181], [59, 91], [95, 181], [245, 59, 265, 110], [323, 113], [61, 78, 21, 295], [164, 233]]]
 h' := ![![[317, 190, 75], [100, 183, 336], [255, 2, 98], [136, 183, 281], [220, 309, 211], [275, 238, 252], [56, 270, 140], [0, 0, 1], [0, 1]], ![[93, 146, 262], [315, 125, 99], [264, 315, 304], [155, 48, 157], [43, 300, 61], [22, 280, 48], [118, 272, 250], [169, 271, 146], [317, 190, 75]], ![[0, 1], [55, 29, 239], [182, 20, 272], [116, 106, 236], [308, 65, 65], [175, 156, 37], [195, 132, 284], [214, 66, 190], [93, 146, 262]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [88, 75], []]
 b := ![[], [22, 308, 336], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A337 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 337 2 where
 D := ![[135, 73, 1], [185, 114, 264, 1]]; D' := ![[135, 73, 1], [185, 114, 264, 1]]
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
  w := ![![337, 0, 0, 0, 0], ![135, 73, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C3371 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A337.D 1) 337 where
  n := 3
  w := ![![337, 0, 0, 0, 0], ![185, 114, 264, 5, 0]]
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

def I347N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![347, 0, 0, 0, 0], ![227, 1, 0, 0, 0]] i)))

def I347N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![347, 0, 0, 0, 0], ![176, 63, 153, 600, 10]] i)))

def P347P0 : CertificateIrreducibleZModOfList' 347 1 2 8 [227, 1] where
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
 g := ![![[], [107], [], [3], [102], [], [87], [120, 1]]]
 h' := ![![[0, 1], [1], [169], [13], [95], [206], [30], [173], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P347P1 : CertificateIrreducibleZModOfList' 347 4 2 8 [176, 63, 148, 120, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [153, 74, 317, 109], [86, 22, 174, 312], [335, 250, 203, 273], [0, 1]]
 g := ![![[147, 185, 91, 121], [55, 286, 274, 39], [279, 58, 219], [336, 146, 95, 53], [291, 70, 110, 243], [2, 299, 278], [227, 1], []], ![[253, 172, 11, 337, 124, 267], [71, 39, 191, 264, 319, 16], [236, 165, 33], [138, 44, 94, 184, 146, 279], [297, 342, 173, 199, 131, 236], [101, 60, 243], [103, 292, 320, 208, 303, 115], [255, 156, 83]], ![[291, 313, 203, 161, 344, 21], [8, 114, 319, 19, 185, 141], [291, 258, 249], [330, 263, 70, 250, 313, 264], [135, 108, 196, 130, 225, 68], [184, 245, 143], [293, 36, 89, 163, 341, 318], [60, 93, 184]], ![[320, 255, 155, 77, 81, 265], [73, 148, 11, 241, 148, 264], [29, 243, 30], [165, 28, 262, 329, 70, 166], [345, 181, 110, 26, 7, 57], [246, 10, 53], [182, 100, 21, 132, 337, 171], [177, 243, 271]]]
 h' := ![![[153, 74, 317, 109], [36, 74, 49, 11], [319, 189, 275, 115], [201, 149, 255, 185], [140, 193, 229, 327], [122, 245, 338, 186], [300, 97, 0, 25], [0, 0, 1], [0, 1]], ![[86, 22, 174, 312], [269, 346, 155, 190], [42, 93, 72, 121], [262, 278, 331, 294], [197, 210, 339, 201], [332, 325, 80, 46], [8, 37, 11, 161], [43, 290, 50, 186], [153, 74, 317, 109]], ![[335, 250, 203, 273], [173, 251, 207, 113], [254, 320, 332, 76], [43, 63, 338, 292], [34, 264, 226, 94], [238, 285, 277, 139], [2, 303, 235, 181], [306, 292, 292, 310], [86, 22, 174, 312]], ![[0, 1], [340, 23, 283, 33], [330, 92, 15, 35], [323, 204, 117, 270], [59, 27, 247, 72], [13, 186, 346, 323], [119, 257, 101, 327], [222, 112, 4, 198], [335, 250, 203, 273]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [286, 317, 60], []]
 b := ![[], [], [258, 265, 59, 200], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A347 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 347 2 where
 D := ![[227, 1], [176, 63, 148, 120, 1]]; D' := ![[227, 1], [176, 63, 148, 120, 1]]
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
  w := ![![347, 0, 0, 0, 0], ![227, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C3471 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A347.D 1) 347 where
  n := 4
  w := ![![347, 0, 0, 0, 0], ![176, 63, 153, 600, 10]]
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

def I349N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![349, 0, 0, 0, 0], ![108, 1, 0, 0, 0]] i)))

def I349N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![349, 0, 0, 0, 0], ![273, 1, 0, 0, 0]] i)))

def I349N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![349, 0, 0, 0, 0], ![73, 133, 317, 5, 0]] i)))

def P349P0 : CertificateIrreducibleZModOfList' 349 1 2 8 [108, 1] where
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
 g := ![![[], [], [307], [313], [279], [], [320], [241, 1]]]
 h' := ![![[0, 1], [1], [348], [49], [231], [81], [340], [147], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P349P1 : CertificateIrreducibleZModOfList' 349 1 2 8 [273, 1] where
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
 g := ![![[], [], [225], [234], [320], [], [219], [76, 1]]]
 h' := ![![[0, 1], [1], [348], [334], [239], [147], [241], [192], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P349P2 : CertificateIrreducibleZModOfList' 349 3 2 8 [73, 133, 317, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [145, 205, 41], [236, 143, 308], [0, 1]]
 g := ![![[151, 95, 324], [277, 75], [314, 200, 12], [224, 320, 180], [267, 60, 204], [92, 283], [193, 32, 1], []], ![[174, 221, 87, 29], [213, 14], [154, 62, 303, 164], [189, 300, 22, 115], [191, 149, 286, 157], [156, 301], [256, 294, 45, 111], [104, 285]], ![[47, 44, 247, 332], [247, 108], [298, 54, 181, 67], [104, 164, 316, 48], [174, 263, 89, 108], [305, 178], [62, 94, 336, 337], [186, 285]]]
 h' := ![![[145, 205, 41], [1, 43, 331], [112, 334, 222], [51, 262, 330], [53, 270, 326], [153, 203, 309], [220, 264, 102], [0, 0, 1], [0, 1]], ![[236, 143, 308], [17, 176, 236], [301, 285, 70], [241, 16, 347], [21, 124, 103], [63, 120, 160], [102, 3, 282], [171, 34, 143], [145, 205, 41]], ![[0, 1], [281, 130, 131], [199, 79, 57], [125, 71, 21], [16, 304, 269], [151, 26, 229], [248, 82, 314], [238, 315, 205], [236, 143, 308]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [332, 215], []]
 b := ![[], [230, 224, 165], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A349 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 349 3 where
 D := ![[108, 1], [273, 1], [73, 133, 317, 1]]; D' := ![[108, 1], [273, 1], [73, 133, 317, 1]]
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
  w := ![![349, 0, 0, 0, 0], ![108, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C3491 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A349.D 1) 349 where
  n := 1
  w := ![![349, 0, 0, 0, 0], ![273, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C3492 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A349.D 2) 349 where
  n := 3
  w := ![![349, 0, 0, 0, 0], ![73, 133, 317, 5, 0]]
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

def I353N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![353, 0, 0, 0, 0], ![136, 1, 0, 0, 0]] i)))

def I353N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![353, 0, 0, 0, 0], ![112, 245, 120, 1085, 10]] i)))

def P353P0 : CertificateIrreducibleZModOfList' 353 1 2 8 [136, 1] where
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
 g := ![![[], [], [], [], [], [231], [185], [217, 1]]]
 h' := ![![[0, 1], [1], [1], [1], [1], [1], [256], [140], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P353P1 : CertificateIrreducibleZModOfList' 353 4 2 8 [112, 245, 115, 217, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [134, 89, 145, 264], [109, 64, 89, 334], [246, 199, 119, 108], [0, 1]]
 g := ![![[169, 144, 105, 73], [151, 102, 93], [69, 70, 172], [186, 202, 225], [175, 86, 46], [162, 301, 280, 272], [136, 1], []], ![[265, 290, 290, 6, 211, 299], [262, 338, 64], [157, 190, 165], [322, 121, 50], [114, 306, 292], [325, 131, 266, 204, 276, 339], [198, 232, 23, 335, 179, 28], [305, 212, 155]], ![[242, 28, 136, 312, 336, 42], [70, 83, 61], [185, 311, 270], [244, 324, 185], [324, 68, 42], [98, 246, 160, 174, 96, 8], [7, 268, 73, 139, 72, 209], [48, 177, 8]], ![[265, 194, 138, 200, 119, 234], [89, 187, 16], [58, 169, 164], [81, 143, 323], [125, 250, 184], [142, 144, 293, 5, 342, 247], [323, 245, 316, 132, 310, 26], [319, 210, 15]]]
 h' := ![![[134, 89, 145, 264], [78, 65, 196, 255], [80, 153, 348, 125], [237, 127, 169, 284], [281, 234, 234, 15], [212, 7, 193, 273], [300, 103, 0, 25], [0, 0, 1], [0, 1]], ![[109, 64, 89, 334], [33, 66, 311, 296], [28, 8, 214, 345], [204, 21, 56, 85], [209, 168, 331, 224], [312, 307, 232, 157], [0, 169, 37, 195], [34, 219, 298, 145], [134, 89, 145, 264]], ![[246, 199, 119, 108], [235, 78, 141, 268], [223, 289, 116, 240], [253, 272, 285, 99], [333, 239, 229, 140], [144, 260, 140, 116], [111, 191, 93, 90], [151, 18, 192, 288], [109, 64, 89, 334]], ![[0, 1], [29, 144, 58, 240], [141, 256, 28, 349], [304, 286, 196, 238], [145, 65, 265, 327], [348, 132, 141, 160], [127, 243, 223, 43], [78, 116, 215, 273], [246, 199, 119, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [160, 248, 82], []]
 b := ![[], [], [289, 67, 343, 283], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A353 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 353 2 where
 D := ![[136, 1], [112, 245, 115, 217, 1]]; D' := ![[136, 1], [112, 245, 115, 217, 1]]
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
  w := ![![353, 0, 0, 0, 0], ![136, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C3531 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A353.D 1) 353 where
  n := 4
  w := ![![353, 0, 0, 0, 0], ![112, 245, 120, 1085, 10]]
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

def I359N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![359, 0, 0, 0, 0], ![359, 0, 0, 1795, 0]] i)))

def P359P0 : CertificateIrreducibleZModOfList' 359 5 2 8 [59, 250, 0, 334, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [132, 171, 329, 153, 348], [192, 310, 298, 104, 353], [204, 276, 333, 25, 116], [190, 319, 117, 77, 260], [0, 1]]
 g := ![![[302, 1, 233, 118, 151], [309, 110, 73, 59, 158], [189, 5, 184, 127, 82], [194, 330, 210, 69], [222, 310, 249, 340], [253, 0, 266], [1], []], ![[44, 146, 128, 14, 243, 168, 287, 337], [146, 157, 337, 42, 257, 112, 258, 175], [94, 37, 336, 299, 148, 212, 259, 76], [208, 304, 241, 80], [28, 204, 46, 207], [139, 333, 84, 238, 343, 42, 328, 293], [38, 305, 72, 23, 310, 23, 177, 279], [197, 169, 224, 121]], ![[26, 108, 345, 249, 289, 315, 236, 52], [14, 212, 24, 275, 74, 43, 354, 353], [241, 23, 182, 5, 215, 39, 292, 71], [339, 69, 67, 235], [299, 318, 217, 91], [193, 167, 277, 51, 282, 49, 134, 278], [27, 148, 35, 166, 335, 139, 47, 87], [139, 242, 188, 36]], ![[284, 155, 305, 306, 247, 189, 32, 308], [134, 92, 315, 321, 208, 312, 50, 197], [228, 95, 289, 320, 348, 134, 41, 177], [152, 338, 169, 48], [310, 176, 129, 205], [280, 5, 216, 89, 193, 224, 131, 227], [239, 343, 166, 105, 50, 249, 63, 332], [230, 354, 56, 173]], ![[81, 64, 67, 113, 326, 136, 327, 213], [234, 295, 244, 284, 40, 305, 56, 56], [321, 7, 13, 204, 130, 74, 285, 56], [41, 233, 127, 9], [347, 298, 27, 110], [325, 258, 329, 55, 241, 141, 312, 314], [165, 175, 28, 27, 47, 342, 295, 61], [198, 182, 191, 108]]]
 h' := ![![[132, 171, 329, 153, 348], [78, 32, 104, 178, 200], [337, 262, 226, 32, 287], [142, 185, 45, 91, 338], [10, 87, 168, 52, 147], [151, 184, 164, 171, 281], [300, 109, 0, 25], [0, 0, 1], [0, 1]], ![[192, 310, 298, 104, 353], [283, 110, 281, 310, 340], [9, 348, 81, 311, 21], [114, 256, 219, 131, 74], [170, 198, 81, 66, 233], [130, 259, 272, 269, 267], [134, 121, 184, 304, 225], [57, 283, 319, 279, 244], [132, 171, 329, 153, 348]], ![[204, 276, 333, 25, 116], [80, 312, 232, 56, 160], [243, 76, 14, 39, 1], [121, 167, 308, 344, 293], [302, 309, 145, 318, 275], [102, 342, 91, 33, 74], [68, 227, 167, 286, 201], [302, 7, 7, 265, 122], [192, 310, 298, 104, 353]], ![[190, 319, 117, 77, 260], [281, 330, 215, 351, 224], [200, 172, 147, 185, 284], [9, 42, 89, 331, 138], [19, 71, 249, 4, 66], [0, 319, 265, 242, 271], [303, 89, 281, 7, 353], [44, 117, 330, 8, 120], [204, 276, 333, 25, 116]], ![[0, 1], [300, 293, 245, 182, 153], [299, 219, 250, 151, 125], [196, 68, 57, 180, 234], [183, 53, 75, 278, 356], [201, 332, 285, 3, 184], [336, 172, 86, 96, 298], [6, 311, 61, 166, 232], [190, 319, 117, 77, 260]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [125, 341, 15, 164], [], [], []]
 b := ![[], [91, 247, 108, 185, 276], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A359 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 359 1 where
 D := ![[59, 250, 0, 334, 0, 1]]; D' := ![[59, 250, 0, 334, 0, 1]]
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
  w := ![![359, 0, 0, 0, 0], ![359, 0, 0, 1795, 0]]
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


lemma PB1045I7_primes (p : ℕ) :
  p ∈ Set.range ![311, 313, 317, 331, 337, 347, 349, 353, 359] ↔ Nat.Prime p ∧ 307 < p ∧ p ≤ 359 := by
  rw [← List.mem_ofFn']
  convert primes_range 307 359 (by omega)
  decide

def PB1045I7 : PrimesBelowBoundCertificateInterval O 307 359 1045 where
  m := 9
  g := ![3, 4, 2, 1, 2, 2, 3, 2, 1]
  P := ![311, 313, 317, 331, 337, 347, 349, 353, 359]
  hP := PB1045I7_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I311N0, I311N1, I311N2]
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
    · exact ![311, 96721, 96721]
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
  β := ![I311N0, I313N0, I313N1, I313N2, I317N0, I347N0, I349N0, I349N1, I353N0]
  Il := ![[I311N0], [I313N0, I313N1, I313N2], [I317N0], [], [], [I347N0], [I349N0, I349N1], [I353N0], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
