
import IdealArithmetic.Examples.NF5_1_91125000000_1_K.RI5_1_91125000000_1_K
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 

instance hp257 : Fact (Nat.Prime 257) := {out := by norm_num}

def I257N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![257, 0, 0, 0, 0], ![255, 239, 1, 0, 0]] i)))

def I257N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![257, 0, 0, 0, 0], ![150, 70, 18, 2, 0]] i)))

def P257P0 : CertificateIrreducibleZModOfList' 257 2 2 8 [255, 239, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 256], [0, 1]]
 g := ![![[9, 128], [248], [226], [29], [227], [49], [67], [1]], ![[0, 129], [248], [226], [29], [227], [49], [67], [1]]]
 h' := ![![[18, 256], [98, 223], [170, 209], [80, 212], [153, 172], [124, 235], [138, 250], [2, 18], [0, 1]], ![[0, 1], [0, 34], [77, 48], [41, 45], [165, 85], [242, 22], [12, 7], [69, 239], [18, 256]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [161]]
 b := ![[], [175, 209]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P257P1 : CertificateIrreducibleZModOfList' 257 3 2 8 [150, 69, 18, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [119, 127, 31], [120, 129, 226], [0, 1]]
 g := ![![[114, 124, 26], [249, 23], [111, 30], [106, 140], [15, 248], [186, 4], [239, 1], []], ![[236, 116, 200, 215], [200, 81], [116, 2], [91, 168], [216, 157], [160, 189], [97, 193], [85, 190]], ![[150, 197, 73, 58], [172, 120], [113, 197], [126, 128], [219, 208], [49, 228], [7, 195], [147, 190]]]
 h' := ![![[119, 127, 31], [181, 207, 138], [3, 132, 58], [132, 67, 95], [94, 166, 59], [51, 122, 209], [130, 64, 255], [0, 0, 1], [0, 1]], ![[120, 129, 226], [54, 204, 61], [146, 35, 9], [29, 33, 197], [40, 214, 164], [40, 85, 160], [41, 215, 184], [126, 230, 129], [119, 127, 31]], ![[0, 1], [148, 103, 58], [48, 90, 190], [251, 157, 222], [167, 134, 34], [246, 50, 145], [237, 235, 75], [60, 27, 127], [120, 129, 226]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [251, 98], []]
 b := ![[], [81, 211, 30], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A257 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 257 2 where
 D := ![[255, 239, 1], [150, 69, 18, 1]]; D' := ![[255, 239, 1], [150, 69, 18, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8, 8]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P257P0
  | 1 => exact P257P1

def C2570 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A257.D 0) 257 where
  n := 2
  w := ![![257, 0, 0, 0, 0], ![255, 239, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C2571 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A257.D 1) 257 where
  n := 3
  w := ![![257, 0, 0, 0, 0], ![150, 70, 18, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K257 : KummerData 257 ![I257N0, I257N1] ![66049, 16974593] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A257
  C := by
    intro i
    match i with
    | 0 => exact C2570
    | 1 => exact C2571
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 257 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp263 : Fact (Nat.Prime 263) := {out := by norm_num}

def I263N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263, 0, 0, 0, 0], ![180, 1, 0, 0, 0]] i)))

def I263N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263, 0, 0, 0, 0], ![736, 2373, 10946, -2872, 22728]] i)))

def P263P0 : CertificateIrreducibleZModOfList' 263 1 2 8 [180, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [244], [105], [], [], [], [], [83, 1]]]
 h' := ![![[0, 1], [1], [36], [216], [74], [52], [234], [51], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P263P1 : CertificateIrreducibleZModOfList' 263 4 2 8 [88, 188, 51, 83, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [79, 98, 103, 118], [253, 150, 106, 16], [111, 14, 54, 129], [0, 1]]
 g := ![![[26, 137, 257, 122], [256, 139, 40, 151], [142, 109, 77, 8], [104, 35, 89], [71, 6, 3], [203, 25, 51], [1], []], ![[194, 127, 245, 261, 86, 146], [213, 46, 209, 175, 252, 199], [9, 132, 122, 158, 40, 209], [93, 89, 78], [96, 183, 117], [0, 238, 162], [6, 231, 50], [245, 42, 248]], ![[120, 196, 188, 160, 121, 102], [212, 28, 117, 217, 259, 242], [120, 49, 138, 220, 40, 166], [239, 199, 178], [82, 153, 49], [171, 33, 192], [8, 57, 151], [130, 28, 256]], ![[12, 1, 14, 79, 165, 23], [171, 46, 13, 255, 234, 50], [58, 243, 213, 150, 8, 33], [112, 154, 16], [259, 126, 248], [90, 173, 148], [240, 158, 22], [8, 66, 72]]]
 h' := ![![[79, 98, 103, 118], [90, 208, 202, 124], [128, 182, 23, 199], [142, 104, 129, 220], [160, 242, 202, 103], [137, 88, 57, 23], [175, 75, 212, 180], [0, 0, 1], [0, 1]], ![[253, 150, 106, 16], [14, 104, 78, 218], [18, 213, 197, 28], [173, 173, 236, 2], [97, 27, 111, 135], [225, 232, 113, 88], [15, 250, 229, 201], [198, 181, 232, 239], [79, 98, 103, 118]], ![[111, 14, 54, 129], [250, 173, 109, 47], [240, 148, 31, 92], [32, 206, 113, 149], [63, 205, 225, 21], [242, 228, 76, 7], [257, 216, 156, 79], [232, 78, 160, 64], [253, 150, 106, 16]], ![[0, 1], [228, 41, 137, 137], [174, 246, 12, 207], [11, 43, 48, 155], [98, 52, 251, 4], [3, 241, 17, 145], [104, 248, 192, 66], [45, 4, 133, 223], [111, 14, 54, 129]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [59, 72, 108], []]
 b := ![[], [], [72, 133, 195, 59], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A263 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 263 2 where
 D := ![[180, 1], [88, 188, 51, 83, 1]]; D' := ![[180, 1], [88, 188, 51, 83, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8, 8]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P263P0
  | 1 => exact P263P1

def C2630 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A263.D 0) 263 where
  n := 1
  w := ![![263, 0, 0, 0, 0], ![180, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C2631 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A263.D 1) 263 where
  n := 4
  w := ![![263, 0, 0, 0, 0], ![736, 2373, 10946, -2872, 22728]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K263 : KummerData 263 ![I263N0, I263N1] ![263, 4784350561] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A263
  C := by
    intro i
    match i with
    | 0 => exact C2630
    | 1 => exact C2631
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 263 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp269 : Fact (Nat.Prime 269) := {out := by norm_num}

def I269N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![269, 0, 0, 0, 0], ![15871, 538, 269, 0, 0]] i)))

def P269P0 : CertificateIrreducibleZModOfList' 269 5 2 8 [151, 13, 169, 0, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [249, 263, 38, 127, 110], [198, 246, 188, 249, 183], [205, 28, 181, 61, 263], [155, 0, 131, 101, 251], [0, 1]]
 g := ![![[205, 35, 102, 77, 93], [167, 153, 7, 30], [55, 142, 173, 22, 47], [205, 95, 89, 193, 222], [191, 59, 160, 169], [100, 0, 0, 1], [], []], ![[113, 201, 73, 185, 19, 170, 194, 230], [262, 7, 38, 232], [8, 127, 103, 145, 212, 258, 62, 76], [46, 23, 177, 207, 153, 70, 68, 85], [23, 155, 3, 258], [51, 89, 51, 20], [245, 112, 65, 66], [31, 10, 233, 264]], ![[83, 168, 46, 130, 94, 268, 77, 209], [36, 124, 152, 53], [150, 178, 114, 25, 263, 144, 243, 69], [151, 138, 264, 109, 158, 165, 142, 128], [180, 36, 109, 220], [160, 260, 222, 216], [250, 42, 254, 264], [52, 75, 212, 133]], ![[146, 13, 187, 226, 83, 211, 53, 100], [51, 5, 3, 218], [185, 221, 55, 146, 58, 267, 152, 149], [31, 147, 134, 34, 261, 24, 185, 57], [222, 9, 201, 150], [131, 144, 91, 216], [142, 70, 21, 222], [60, 204, 75, 36]], ![[69, 147, 193, 182, 212, 87, 72, 17], [75, 23, 58, 126], [169, 22, 85, 128, 162, 51, 37, 60], [251, 242, 152, 173, 79, 213, 130, 147], [253, 163, 167, 65], [120, 77, 79, 256], [143, 113, 79, 245], [220, 105, 130, 55]]]
 h' := ![![[249, 263, 38, 127, 110], [149, 36, 230, 212, 30], [34, 32, 104, 124, 179], [249, 88, 265, 51, 169], [162, 163, 77, 128, 130], [233, 45, 47, 118, 256], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[198, 246, 188, 249, 183], [123, 115, 157, 63, 68], [45, 15, 15, 21, 129], [191, 111, 258, 51, 91], [244, 108, 252, 169, 33], [36, 256, 67, 54, 142], [118, 54, 217, 133, 252], [23, 210, 197, 184, 55], [249, 263, 38, 127, 110]], ![[205, 28, 181, 61, 263], [31, 207, 63, 86, 47], [244, 263, 59, 124, 44], [261, 209, 43, 187, 65], [197, 105, 138, 197, 40], [137, 16, 246, 207, 36], [25, 160, 223, 268, 158], [148, 142, 115, 104, 159], [198, 246, 188, 249, 183]], ![[155, 0, 131, 101, 251], [154, 112, 226, 30, 72], [190, 181, 223, 164, 73], [157, 194, 156, 153, 252], [202, 38, 265, 157, 177], [38, 159, 261, 257, 227], [167, 119, 189, 227, 111], [147, 71, 36, 177, 130], [205, 28, 181, 61, 263]], ![[0, 1], [189, 68, 131, 147, 52], [111, 47, 137, 105, 113], [174, 205, 85, 96, 230], [172, 124, 75, 156, 158], [213, 62, 186, 171, 146], [176, 205, 178, 179, 16], [220, 115, 189, 73, 194], [155, 0, 131, 101, 251]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [231, 73, 115, 80], [], [], []]
 b := ![[], [130, 64, 66, 229, 146], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A269 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 269 1 where
 D := ![[151, 13, 169, 0, 0, 1]]; D' := ![[151, 13, 169, 0, 0, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8]
 n := ![5]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P269P0

def C2690 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A269.D 0) 269 where
  n := 5
  w := ![![269, 0, 0, 0, 0], ![15871, 538, 269, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K269 : KummerData 269 ![I269N0] ![1408514752349] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A269
  C := by
    intro i
    match i with
    | 0 => exact C2690
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 269 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp271 : Fact (Nat.Prime 271) := {out := by norm_num}

def I271N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![271, 0, 0, 0, 0], ![63, 1, 0, 0, 0]] i)))

def I271N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![271, 0, 0, 0, 0], ![256, 226, 1, 0, 0]] i)))

def I271N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![271, 0, 0, 0, 0], ![193, 253, 1, 0, 0]] i)))

def P271P0 : CertificateIrreducibleZModOfList' 271 1 2 8 [63, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [228], [80], [256], [], [], [], [208, 1]]]
 h' := ![![[0, 1], [270], [109], [132], [16], [4], [2], [175], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P271P1 : CertificateIrreducibleZModOfList' 271 2 2 8 [256, 226, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [45, 270], [0, 1]]
 g := ![![[3, 18], [51, 35], [216, 212], [108, 106], [238], [31], [128], [1]], ![[0, 253], [0, 236], [0, 59], [0, 165], [238], [31], [128], [1]]]
 h' := ![![[45, 270], [223, 254], [259, 199], [265, 235], [17, 102], [181, 77], [248, 64], [15, 45], [0, 1]], ![[0, 1], [0, 17], [0, 72], [0, 36], [0, 169], [123, 194], [147, 207], [143, 226], [45, 270]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [98]]
 b := ![[], [117, 49]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P271P2 : CertificateIrreducibleZModOfList' 271 2 2 8 [193, 253, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 270], [0, 1]]
 g := ![![[167, 141], [188, 175], [132, 144], [10, 219], [83], [211], [53], [1]], ![[266, 130], [86, 96], [14, 127], [158, 52], [83], [211], [53], [1]]]
 h' := ![![[18, 270], [30, 236], [269, 63], [238, 259], [134, 46], [94, 246], [191, 239], [78, 18], [0, 1]], ![[0, 1], [213, 35], [48, 208], [22, 12], [149, 225], [186, 25], [157, 32], [131, 253], [18, 270]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [196]]
 b := ![[], [202, 98]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A271 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 271 3 where
 D := ![[63, 1], [256, 226, 1], [193, 253, 1]]; D' := ![[63, 1], [256, 226, 1], [193, 253, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8, 8, 8]
 n := ![1, 2, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P271P0
  | 1 => exact P271P1
  | 2 => exact P271P2

def C2710 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A271.D 0) 271 where
  n := 1
  w := ![![271, 0, 0, 0, 0], ![63, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C2711 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A271.D 1) 271 where
  n := 2
  w := ![![271, 0, 0, 0, 0], ![256, 226, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C2712 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A271.D 2) 271 where
  n := 2
  w := ![![271, 0, 0, 0, 0], ![193, 253, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K271 : KummerData 271 ![I271N0, I271N1, I271N2] ![271, 73441, 73441] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A271
  C := by
    intro i
    match i with
    | 0 => exact C2710
    | 1 => exact C2711
    | 2 => exact C2712
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 271 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp277 : Fact (Nat.Prime 277) := {out := by norm_num}

def I277N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![277, 0, 0, 0, 0], ![147, 1, 0, 0, 0]] i)))

def I277N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![277, 0, 0, 0, 0], ![705, 2245, 10898, -2778, 22728]] i)))

def P277P0 : CertificateIrreducibleZModOfList' 277 1 2 8 [147, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [49], [], [190], [], [], [130, 1]]]
 h' := ![![[0, 1], [1], [276], [270], [47], [81], [9], [3], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P277P1 : CertificateIrreducibleZModOfList' 277 4 2 8 [57, 13, 3, 130, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [260, 34, 66, 251], [271, 86, 172, 179], [170, 156, 39, 124], [0, 1]]
 g := ![![[253, 234, 70, 238], [264, 41, 237], [40, 70, 65, 215], [54, 269, 70], [265, 238, 247, 28], [47, 113, 3], [1], []], ![[200, 25, 105, 274, 212, 50], [247, 92, 29], [49, 94, 181, 18, 27, 42], [117, 255, 91], [252, 35, 29, 176], [67, 111, 131], [86, 275, 19], [8, 98, 122]], ![[92, 29, 67, 98, 181, 212], [252, 158, 64], [275, 228, 94, 66, 230, 139], [137, 269, 203], [68, 52, 267, 145, 214, 253], [48, 147, 48], [201, 44, 70], [129, 1, 186]], ![[168, 185, 91, 142, 274, 132], [200, 208, 131], [208, 158, 257, 70, 231, 138], [15, 124, 141], [126, 267, 58, 96, 106, 134], [203, 258, 268], [178, 227, 156], [264, 206, 141]]]
 h' := ![![[260, 34, 66, 251], [128, 259, 102, 133], [213, 152, 185, 156], [249, 110, 229, 40], [130, 142, 185, 65], [16, 247, 115, 100], [220, 264, 274, 147], [0, 0, 1], [0, 1]], ![[271, 86, 172, 179], [127, 44, 276, 93], [112, 148, 194, 197], [102, 219, 241, 128], [257, 251, 25, 214], [75, 17, 49], [273, 33, 203, 193], [110, 79, 78, 236], [260, 34, 66, 251]], ![[170, 156, 39, 124], [129, 115, 163, 22], [221, 149, 149, 8], [203, 40, 58, 154], [16, 34, 233, 122], [190, 17, 235, 42], [106, 53, 98, 34], [162, 4, 147, 212], [271, 86, 172, 179]], ![[0, 1], [164, 136, 13, 29], [22, 105, 26, 193], [137, 185, 26, 232], [182, 127, 111, 153], [155, 273, 155, 135], [107, 204, 256, 180], [2, 194, 51, 106], [170, 156, 39, 124]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [273, 156, 252], []]
 b := ![[], [], [8, 17, 107, 240], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A277 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 277 2 where
 D := ![[147, 1], [57, 13, 3, 130, 1]]; D' := ![[147, 1], [57, 13, 3, 130, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8, 8]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P277P0
  | 1 => exact P277P1

def C2770 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A277.D 0) 277 where
  n := 1
  w := ![![277, 0, 0, 0, 0], ![147, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C2771 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A277.D 1) 277 where
  n := 4
  w := ![![277, 0, 0, 0, 0], ![705, 2245, 10898, -2778, 22728]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K277 : KummerData 277 ![I277N0, I277N1] ![277, 5887339441] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A277
  C := by
    intro i
    match i with
    | 0 => exact C2770
    | 1 => exact C2771
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 277 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp281 : Fact (Nat.Prime 281) := {out := by norm_num}

def I281N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![281, 0, 0, 0, 0], ![252, 1, 0, 0, 0]] i)))

def I281N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![281, 0, 0, 0, 0], ![257, 31, 1, 0, 0]] i)))

def I281N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![281, 0, 0, 0, 0], ![84, 279, 1, 0, 0]] i)))

def P281P0 : CertificateIrreducibleZModOfList' 281 1 2 8 [252, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [155], [256], [], [], [29, 1]]]
 h' := ![![[0, 1], [1], [1], [280], [118], [16], [4], [279], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P281P1 : CertificateIrreducibleZModOfList' 281 2 2 8 [257, 31, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [250, 280], [0, 1]]
 g := ![![[268, 157], [126], [170], [44, 169], [155, 245], [157], [118], [1]], ![[178, 124], [126], [170], [144, 112], [147, 36], [157], [118], [1]]]
 h' := ![![[250, 280], [263, 193], [274, 209], [213, 156], [67, 268], [6, 37], [36, 193], [24, 250], [0, 1]], ![[0, 1], [181, 88], [258, 72], [154, 125], [189, 13], [264, 244], [235, 88], [142, 31], [250, 280]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42]]
 b := ![[], [185, 21]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P281P2 : CertificateIrreducibleZModOfList' 281 2 2 8 [84, 279, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 280], [0, 1]]
 g := ![![[194, 228], [209], [100], [183, 209], [205, 123], [242], [4], [1]], ![[88, 53], [209], [100], [39, 72], [170, 158], [242], [4], [1]]]
 h' := ![![[2, 280], [143, 60], [175, 174], [83, 10], [202, 174], [199, 211], [257, 234], [197, 2], [0, 1]], ![[0, 1], [263, 221], [242, 107], [103, 271], [269, 107], [59, 70], [163, 47], [201, 279], [2, 280]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [237]]
 b := ![[], [22, 259]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A281 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 281 3 where
 D := ![[252, 1], [257, 31, 1], [84, 279, 1]]; D' := ![[252, 1], [257, 31, 1], [84, 279, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8, 8, 8]
 n := ![1, 2, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P281P0
  | 1 => exact P281P1
  | 2 => exact P281P2

def C2810 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A281.D 0) 281 where
  n := 1
  w := ![![281, 0, 0, 0, 0], ![252, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C2811 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A281.D 1) 281 where
  n := 2
  w := ![![281, 0, 0, 0, 0], ![257, 31, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C2812 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A281.D 2) 281 where
  n := 2
  w := ![![281, 0, 0, 0, 0], ![84, 279, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K281 : KummerData 281 ![I281N0, I281N1, I281N2] ![281, 78961, 78961] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A281
  C := by
    intro i
    match i with
    | 0 => exact C2810
    | 1 => exact C2811
    | 2 => exact C2812
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 281 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp283 : Fact (Nat.Prime 283) := {out := by norm_num}

def I283N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![283, 0, 0, 0, 0], ![161, 1, 0, 0, 0]] i)))

def I283N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![283, 0, 0, 0, 0], ![865, 2244, 11063, -2794, 22728]] i)))

def P283P0 : CertificateIrreducibleZModOfList' 283 1 2 8 [161, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [225], [], [54], [155], [], [], [122, 1]]]
 h' := ![![[0, 1], [282], [15], [79], [232], [116], [207], [168], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P283P1 : CertificateIrreducibleZModOfList' 283 4 2 8 [217, 20, 168, 122, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [218, 80, 271, 179], [1, 31, 119, 232], [225, 171, 176, 155], [0, 1]]
 g := ![![[252, 127, 101, 165], [61, 86, 144, 73], [272, 28, 61], [177, 235, 184, 40], [181, 230, 6, 7], [145, 120, 168], [1], []], ![[7, 210, 119, 228, 122, 127], [169, 113, 124, 262, 228, 110], [146, 19, 70], [188, 49, 132, 242, 219, 181], [171, 117, 266, 194, 166, 275], [224, 136, 208], [221, 263, 89], [197, 26, 62]], ![[89, 86, 170, 29, 164, 14], [221, 277, 191, 108, 109, 187], [188, 268, 195], [81, 146, 258, 226, 8, 22], [193, 4, 5, 35, 49, 182], [14, 193, 235], [202, 189, 137], [142, 235, 54]], ![[245, 214, 68, 158, 71, 157], [77, 15, 238, 82, 56, 29], [91, 63, 143], [164, 238, 60, 19, 258, 251], [21, 231, 9, 194, 84, 263], [246, 3, 34], [252, 97, 11], [58, 205, 253]]]
 h' := ![![[218, 80, 271, 179], [64, 11, 170, 62], [138, 28, 2, 140], [79, 5, 11, 108], [60, 42, 18, 235], [59, 116, 191, 63], [66, 263, 115, 161], [0, 0, 1], [0, 1]], ![[1, 31, 119, 232], [176, 238, 92, 150], [11, 241, 147, 237], [194, 223, 66, 97], [241, 225, 265, 73], [92, 92, 278, 14], [34, 135, 215, 162], [247, 111, 227, 70], [218, 80, 271, 179]], ![[225, 171, 176, 155], [164, 48, 129, 12], [164, 220, 142, 243], [121, 217, 54, 228], [172, 231, 104, 117], [270, 272, 226, 203], [55, 23, 188, 73], [34, 280, 262, 49], [1, 31, 119, 232]], ![[0, 1], [71, 269, 175, 59], [179, 77, 275, 229], [207, 121, 152, 133], [242, 68, 179, 141], [7, 86, 154, 3], [40, 145, 48, 170], [117, 175, 76, 164], [225, 171, 176, 155]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [111, 33, 275], []]
 b := ![[], [], [252, 39, 229, 244], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A283 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 283 2 where
 D := ![[161, 1], [217, 20, 168, 122, 1]]; D' := ![[161, 1], [217, 20, 168, 122, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8, 8]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P283P0
  | 1 => exact P283P1

def C2830 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A283.D 0) 283 where
  n := 1
  w := ![![283, 0, 0, 0, 0], ![161, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C2831 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A283.D 1) 283 where
  n := 4
  w := ![![283, 0, 0, 0, 0], ![865, 2244, 11063, -2794, 22728]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K283 : KummerData 283 ![I283N0, I283N1] ![283, 6414247921] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A283
  C := by
    intro i
    match i with
    | 0 => exact C2830
    | 1 => exact C2831
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 283 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp293 : Fact (Nat.Prime 293) := {out := by norm_num}

def I293N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![293, 0, 0, 0, 0], ![228, 89, 1, 0, 0]] i)))

def I293N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![293, 0, 0, 0, 0], ![39, 76, 204, 2, 0]] i)))

def P293P0 : CertificateIrreducibleZModOfList' 293 2 2 8 [228, 89, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [204, 292], [0, 1]]
 g := ![![[215, 9], [37], [55, 56], [15], [64], [173, 276], [10], [1]], ![[0, 284], [37], [52, 237], [15], [64], [221, 17], [10], [1]]]
 h' := ![![[204, 292], [26, 290], [59, 157], [151, 39], [73, 182], [111, 8], [187, 139], [65, 204], [0, 1]], ![[0, 1], [0, 3], [150, 136], [196, 254], [283, 111], [278, 285], [122, 154], [75, 89], [204, 292]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [204]]
 b := ![[], [144, 102]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P293P1 : CertificateIrreducibleZModOfList' 293 3 2 8 [39, 75, 204, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [109, 38, 277], [273, 254, 16], [0, 1]]
 g := ![![[170, 235, 143], [151, 69], [254, 77, 150], [106, 153], [250, 17], [199, 79, 123], [89, 1], []], ![[218, 212, 24, 61], [62, 81], [41, 110, 188, 26], [271, 186], [8, 283], [89, 89, 283, 202], [135, 56], [179, 256]], ![[173, 101, 33, 6], [25, 71], [174, 78, 26, 24], [218, 67], [145, 137], [49, 186, 264, 209], [243, 272], [147, 256]]]
 h' := ![![[109, 38, 277], [177, 36, 266], [56, 115, 216], [208, 3, 83], [151, 277, 175], [150, 134, 156], [45, 25, 228], [0, 0, 1], [0, 1]], ![[273, 254, 16], [135, 129, 184], [76, 218, 284], [258, 244, 231], [54, 65, 170], [69, 140, 269], [124, 181, 84], [212, 111, 254], [109, 38, 277]], ![[0, 1], [171, 128, 136], [248, 253, 86], [232, 46, 272], [108, 244, 241], [279, 19, 161], [157, 87, 274], [234, 182, 38], [273, 254, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51, 185], []]
 b := ![[], [221, 71, 213], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A293 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 293 2 where
 D := ![[228, 89, 1], [39, 75, 204, 1]]; D' := ![[228, 89, 1], [39, 75, 204, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8, 8]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P293P0
  | 1 => exact P293P1

def C2930 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A293.D 0) 293 where
  n := 2
  w := ![![293, 0, 0, 0, 0], ![228, 89, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C2931 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A293.D 1) 293 where
  n := 3
  w := ![![293, 0, 0, 0, 0], ![39, 76, 204, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K293 : KummerData 293 ![I293N0, I293N1] ![85849, 25153757] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A293
  C := by
    intro i
    match i with
    | 0 => exact C2930
    | 1 => exact C2931
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 293 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp307 : Fact (Nat.Prime 307) := {out := by norm_num}

def I307N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![307, 0, 0, 0, 0], ![6, 1, 0, 0, 0]] i)))

def I307N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![307, 0, 0, 0, 0], ![791, 2701, 10931, -2436, 22728]] i)))

def P307P0 : CertificateIrreducibleZModOfList' 307 1 2 8 [6, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [256], [], [], [102], [19], [], [301, 1]]]
 h' := ![![[0, 1], [306], [16], [4], [2], [193], [68], [36], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P307P1 : CertificateIrreducibleZModOfList' 307 4 2 8 [143, 298, 36, 301, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 181, 134, 214], [12, 16, 193, 131], [262, 109, 287, 269], [0, 1]]
 g := ![![[223, 73, 28, 286], [221, 43, 8, 304], [218, 241, 109], [213, 111, 133], [17, 87, 162, 223], [143, 40, 91, 36], [1], []], ![[196, 171, 113, 40, 279, 211], [227, 226, 75, 263, 38, 202], [205, 58, 24], [183, 17, 262], [37, 22, 244, 296, 202, 245], [252, 138, 91, 270, 9, 226], [82, 275, 212], [219, 261, 53]], ![[142, 176, 33, 101, 191, 138], [238, 230, 82, 92, 252, 2], [30, 128, 46], [36, 160, 89], [26, 149, 142, 229, 4, 43], [75, 191, 255, 122, 38, 157], [251, 216, 66], [76, 32, 276]], ![[159, 166, 262, 132, 58, 212], [256, 235, 8, 151, 288, 54], [135, 298, 44], [166, 190, 58], [171, 13, 73, 306, 244, 112], [206, 72, 126, 57, 252, 141], [237, 78, 234], [8, 53, 216]]]
 h' := ![![[39, 181, 134, 214], [18, 260, 197, 30], [95, 160, 53, 35], [252, 158, 75, 118], [25, 270, 230, 146], [120, 52, 194, 247], [164, 9, 271, 6], [0, 0, 1], [0, 1]], ![[12, 16, 193, 131], [170, 282, 140, 165], [298, 238, 199, 126], [270, 171, 270, 192], [246, 196, 56, 252], [155, 221, 201, 275], [229, 294, 224, 200], [290, 256, 13, 186], [39, 181, 134, 214]], ![[262, 109, 287, 269], [57, 140, 299, 181], [233, 108, 46, 134], [15, 134, 152, 254], [229, 134, 185, 150], [220, 305, 175, 48], [160, 253, 103, 189], [21, 176, 119, 56], [12, 16, 193, 131]], ![[0, 1], [258, 239, 285, 238], [288, 108, 9, 12], [49, 151, 117, 50], [122, 14, 143, 66], [114, 36, 44, 44], [251, 58, 16, 219], [267, 182, 174, 65], [262, 109, 287, 269]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [18, 276, 155], []]
 b := ![[], [], [67, 248, 193, 41], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A307 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 307 2 where
 D := ![[6, 1], [143, 298, 36, 301, 1]]; D' := ![[6, 1], [143, 298, 36, 301, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8, 8]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P307P0
  | 1 => exact P307P1

def C3070 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A307.D 0) 307 where
  n := 1
  w := ![![307, 0, 0, 0, 0], ![6, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C3071 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A307.D 1) 307 where
  n := 4
  w := ![![307, 0, 0, 0, 0], ![791, 2701, 10931, -2436, 22728]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K307 : KummerData 307 ![I307N0, I307N1] ![307, 8882874001] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A307
  C := by
    intro i
    match i with
    | 0 => exact C3070
    | 1 => exact C3071
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 307 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


lemma PB18792I6_primes (p : ℕ) :
  p ∈ Set.range ![257, 263, 269, 271, 277, 281, 283, 293, 307] ↔ Nat.Prime p ∧ 251 < p ∧ p ≤ 307 := by
  rw [← List.mem_ofFn']
  convert primes_range 251 307 (by omega)
  decide

def PB18792I6 : PrimesBelowBoundCertificateInterval O 251 307 18792 where
  m := 9
  g := ![2, 2, 1, 3, 2, 3, 2, 2, 2]
  P := ![257, 263, 269, 271, 277, 281, 283, 293, 307]
  hP := PB18792I6_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I257N0, I257N1]
    · exact ![I263N0, I263N1]
    · exact ![I269N0]
    · exact ![I271N0, I271N1, I271N2]
    · exact ![I277N0, I277N1]
    · exact ![I281N0, I281N1, I281N2]
    · exact ![I283N0, I283N1]
    · exact ![I293N0, I293N1]
    · exact ![I307N0, I307N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · convert (containsPrimesAbove_of_KummerData K257) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K263) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K269) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K271) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K277) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K281) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K283) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K293) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K307) <;> rfl
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![66049, 16974593]
    · exact ![263, 4784350561]
    · exact ![1408514752349]
    · exact ![271, 73441, 73441]
    · exact ![277, 5887339441]
    · exact ![281, 78961, 78961]
    · exact ![283, 6414247921]
    · exact ![85849, 25153757]
    · exact ![307, 8882874001]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact (card_quot_of_KummerData K257)
    · exact (card_quot_of_KummerData K263)
    · exact (card_quot_of_KummerData K269)
    · exact (card_quot_of_KummerData K271)
    · exact (card_quot_of_KummerData K277)
    · exact (card_quot_of_KummerData K281)
    · exact (card_quot_of_KummerData K283)
    · exact (card_quot_of_KummerData K293)
    · exact (card_quot_of_KummerData K307)
  β := ![I263N0, I271N0, I277N0, I281N0, I283N0, I307N0]
  Il := ![[], [I263N0], [], [I271N0], [I277N0], [I281N0], [I283N0], [], [I307N0]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
