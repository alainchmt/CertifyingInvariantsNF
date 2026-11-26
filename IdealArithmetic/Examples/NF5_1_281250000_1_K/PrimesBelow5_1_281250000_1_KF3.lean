
import IdealArithmetic.Examples.NF5_1_281250000_1_K.RI5_1_281250000_1_K
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 

instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0, 0, 0], ![57, 92, 1, 0, 0]] i)))

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0, 0, 0], ![6, 36, 15, 5, 0]] i)))

def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [57, 92, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [15, 106], [0, 1]]
 g := ![![[11, 92], [105, 100], [49], [66, 41], [83], [15, 1]], ![[0, 15], [0, 7], [49], [39, 66], [83], [30, 106]]]
 h' := ![![[15, 106], [7, 78], [64, 10], [90, 100], [85, 83], [1, 61], [0, 1]], ![[0, 1], [0, 29], [0, 97], [92, 7], [46, 24], [60, 46], [15, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37]]
 b := ![[], [102, 72]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P107P1 : CertificateIrreducibleZModOfList' 107 3 2 6 [6, 36, 15, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [40, 60, 5], [52, 46, 102], [0, 1]]
 g := ![![[29, 104, 48], [72, 67, 3], [36, 3], [34, 78, 40], [59, 11], [1]], ![[94, 10, 18, 15], [32, 20, 96, 24], [79, 100], [50, 77, 34, 2], [75, 89], [48, 71, 57, 18]], ![[78, 36, 45, 79], [17, 11, 41, 61], [106, 35], [88, 11, 61, 79], [6, 92], [90, 40, 82, 89]]]
 h' := ![![[40, 60, 5], [103, 83, 72], [98, 15, 18], [10, 29, 18], [3, 61, 88], [101, 71, 92], [0, 1]], ![[52, 46, 102], [23, 5, 89], [62, 4, 47], [106, 95, 10], [47, 88, 73], [47, 49, 93], [40, 60, 5]], ![[0, 1], [3, 19, 53], [95, 88, 42], [93, 90, 79], [96, 65, 53], [5, 94, 29], [52, 46, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [88, 75], []]
 b := ![[], [43, 20, 92], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A107 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 107 2 where
 D := ![[57, 92, 1], [6, 36, 15, 1]]; D' := ![[57, 92, 1], [6, 36, 15, 1]]
 heqm := by decide
 hProd := by decide
 s := ![6, 6]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P107P0
  | 1 => exact P107P1

def C1070 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A107.D 0) 107 where
  n := 2
  w := ![![107, 0, 0, 0, 0], ![57, 92, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C1071 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A107.D 1) 107 where
  n := 3
  w := ![![107, 0, 0, 0, 0], ![6, 36, 15, 5, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K107 : KummerData 107 ![I107N0, I107N1] ![11449, 1225043] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A107
  C := by
    intro i
    match i with
    | 0 => exact C1070
    | 1 => exact C1071
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 107 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0, 0, 0], ![327, -218, 0, 545, 0]] i)))

def P109P0 : CertificateIrreducibleZModOfList' 109 5 2 6 [27, 32, 0, 84, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [39, 13, 65, 101, 32], [102, 98, 101, 95, 17], [78, 54, 39, 105, 104], [108, 52, 13, 26, 65], [0, 1]]
 g := ![![[47, 64, 66, 43, 27], [27, 80, 89, 66], [104, 33, 84, 69, 83], [71, 67, 73, 0, 80], [0, 1], []], ![[4, 97, 97, 36, 30, 70, 40, 86], [80, 49, 31, 46], [62, 35, 10, 72, 48, 6, 62, 19], [44, 58, 85, 21, 66, 37, 29, 79], [52, 26, 59, 46], [96, 55, 33, 92, 3, 97, 58, 68]], ![[6, 70, 82, 85, 27, 72, 49, 72], [47, 94, 85, 94], [66, 39, 71, 29, 101, 93, 85, 11], [50, 106, 66, 26, 56, 20, 91, 79], [80, 8, 94, 104], [76, 86, 37, 63, 21, 99, 70, 8]], ![[69, 15, 43, 2, 16, 24, 8, 93], [43, 101, 76, 66], [22, 79, 108, 47, 8, 48, 37, 35], [76, 70, 75, 101, 83, 61, 21, 80], [34, 107, 45, 94], [8, 92, 4, 83, 76, 105, 27, 93]], ![[94, 94, 71, 28, 16, 35, 74, 24], [27, 31, 60, 89], [79, 29, 24, 21, 103, 90, 73, 14], [54, 79, 43, 11, 2, 22, 78, 54], [28, 59, 65, 48], [41, 6, 58, 56, 28, 48, 43, 54]]]
 h' := ![![[39, 13, 65, 101, 32], [56, 63, 64, 107, 71], [26, 95, 95, 58, 75], [45, 61, 27, 59, 44], [0, 82, 77, 0, 25], [0, 0, 0, 1], [0, 1]], ![[102, 98, 101, 95, 17], [91, 29, 74, 96, 101], [17, 83, 37, 15, 41], [28, 58, 97, 91, 2], [42, 26, 49, 87, 69], [47, 44, 15, 91, 68], [39, 13, 65, 101, 32]], ![[78, 54, 39, 105, 104], [30, 71, 88, 82, 58], [99, 105, 31, 90, 58], [66, 26, 78, 80, 53], [29, 91, 34, 13, 57], [3, 60, 53, 105, 70], [102, 98, 101, 95, 17]], ![[108, 52, 13, 26, 65], [45, 65, 20, 85, 104], [94, 50, 1, 63, 75], [67, 22, 82, 22, 50], [106, 77, 11, 49, 23], [77, 15, 62, 22, 58], [78, 54, 39, 105, 104]], ![[0, 1], [80, 99, 81, 66, 102], [68, 103, 54, 101, 78], [52, 51, 43, 75, 69], [4, 51, 47, 69, 44], [91, 99, 88, 108, 22], [108, 52, 13, 26, 65]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [90, 39, 5, 27], [], [], []]
 b := ![[], [2, 83, 81, 9, 23], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A109 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 109 1 where
 D := ![[27, 32, 0, 84, 0, 1]]; D' := ![[27, 32, 0, 84, 0, 1]]
 heqm := by decide
 hProd := by decide
 s := ![6]
 n := ![5]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P109P0

def C1090 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A109.D 0) 109 where
  n := 5
  w := ![![109, 0, 0, 0, 0], ![327, -218, 0, 545, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K109 : KummerData 109 ![I109N0] ![15386239549] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A109
  C := by
    intro i
    match i with
    | 0 => exact C1090
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 109 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0, 0, 0], ![42, 1, 0, 0, 0]] i)))

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0, 0, 0], ![9, 73, 49, 355, 10]] i)))

def P113P0 : CertificateIrreducibleZModOfList' 113 1 2 6 [42, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [], [18], [69, 71, 1]]]
 h' := ![![[0, 1], [112], [98], [95], [35], [40], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P113P1 : CertificateIrreducibleZModOfList' 113 4 2 6 [9, 73, 44, 71, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [40, 38, 75, 27], [104, 47, 54, 50], [11, 27, 97, 36], [0, 1]]
 g := ![![[96, 5, 56, 13], [105, 90, 64], [0, 17, 63], [23, 96, 53], [33, 25, 42, 1], []], ![[67, 93, 102, 2, 39, 75], [42, 90, 41], [85, 17, 11], [19, 16, 51], [20, 46, 62, 83, 48, 48], [23, 103, 63, 25, 40, 21]], ![[85, 17, 17, 60, 66, 61], [72, 59, 44], [50, 6, 9], [109, 80, 60], [77, 74, 10, 52, 47, 32], [70, 84, 61, 12, 28, 22]], ![[11, 23, 79, 90, 72, 72], [34, 74, 83], [61, 83, 100], [76, 98, 60], [34, 16, 6, 103, 102, 28], [96, 75, 80, 26, 74, 100]]]
 h' := ![![[40, 38, 75, 27], [56, 30, 28, 76], [60, 85, 7, 105], [88, 54, 74, 96], [42, 78, 74, 36], [0, 0, 0, 1], [0, 1]], ![[104, 47, 54, 50], [90, 84, 87, 77], [109, 70, 40, 70], [99, 61, 59, 24], [65, 87, 82, 27], [61, 11, 88, 39], [40, 38, 75, 27]], ![[11, 27, 97, 36], [23, 49, 75, 11], [85, 33, 41, 65], [99, 32, 51, 3], [17, 80, 19, 25], [110, 18, 105, 46], [104, 47, 54, 50]], ![[0, 1], [3, 63, 36, 62], [14, 38, 25, 99], [26, 79, 42, 103], [22, 94, 51, 25], [15, 84, 33, 27], [11, 27, 97, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [93, 93, 40], []]
 b := ![[], [], [5, 107, 43, 67], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A113 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 113 2 where
 D := ![[42, 1], [9, 73, 44, 71, 1]]; D' := ![[42, 1], [9, 73, 44, 71, 1]]
 heqm := by decide
 hProd := by decide
 s := ![6, 6]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P113P0
  | 1 => exact P113P1

def C1130 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A113.D 0) 113 where
  n := 1
  w := ![![113, 0, 0, 0, 0], ![42, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C1131 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A113.D 1) 113 where
  n := 4
  w := ![![113, 0, 0, 0, 0], ![9, 73, 49, 355, 10]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K113 : KummerData 113 ![I113N0, I113N1] ![113, 163047361] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A113
  C := by
    intro i
    match i with
    | 0 => exact C1130
    | 1 => exact C1131
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 113 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0, 0, 0], ![46, 1, 0, 0, 0]] i)))

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0, 0, 0], ![126, 80, 64, 405, 10]] i)))

def P127P0 : CertificateIrreducibleZModOfList' 127 1 2 6 [46, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [69], [50], [68], [122], [84, 81, 1]]]
 h' := ![![[0, 1], [1], [113], [47], [103], [73], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P127P1 : CertificateIrreducibleZModOfList' 127 4 2 6 [126, 80, 59, 81, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [37, 6, 113, 3], [102, 101, 75, 105], [34, 19, 66, 19], [0, 1]]
 g := ![![[37, 100, 38, 88], [31, 26, 122, 87], [79, 118, 107, 70], [112, 46, 88, 36], [7, 25, 46, 1], []], ![[26, 62, 82, 4, 119, 54], [103, 101, 16, 20, 23, 90], [16, 106, 0, 105, 95, 12], [62, 59, 11, 108, 24, 96], [15, 12, 33, 36, 19, 57], [109, 30, 5, 72, 102, 27]], ![[52, 87, 1, 106, 93, 59], [43, 38, 31, 93, 31, 118], [16, 71, 19, 33, 4, 45], [14, 36, 35, 70, 46, 48], [76, 121, 74, 59, 87, 123], [99, 74, 57, 69, 92, 20]], ![[23, 50, 107, 88, 11, 8], [125, 64, 119, 72, 2, 62], [77, 53, 55, 54, 106, 36], [123, 61, 23, 9, 47, 15], [35, 53, 40, 51, 38, 122], [63, 112, 60, 120, 23, 1]]]
 h' := ![![[37, 6, 113, 3], [31, 104, 29, 71], [79, 119, 115, 77], [112, 25, 90, 109], [7, 100, 46, 121], [0, 0, 0, 1], [0, 1]], ![[102, 101, 75, 105], [118, 103, 91, 48], [104, 60, 30, 86], [38, 67, 44, 125], [103, 121, 40, 64], [89, 77, 29, 107], [37, 6, 113, 3]], ![[34, 19, 66, 19], [35, 59, 117, 108], [19, 8, 12, 50], [43, 44, 84, 33], [3, 123, 47, 60], [95, 46, 116, 9], [102, 101, 75, 105]], ![[0, 1], [79, 115, 17, 27], [121, 67, 97, 41], [40, 118, 36, 114], [87, 37, 121, 9], [124, 4, 109, 10], [34, 19, 66, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [36, 81, 23], []]
 b := ![[], [], [29, 40, 67, 53], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A127 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 127 2 where
 D := ![[46, 1], [126, 80, 59, 81, 1]]; D' := ![[46, 1], [126, 80, 59, 81, 1]]
 heqm := by decide
 hProd := by decide
 s := ![6, 6]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P127P0
  | 1 => exact P127P1

def C1270 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A127.D 0) 127 where
  n := 1
  w := ![![127, 0, 0, 0, 0], ![46, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C1271 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A127.D 1) 127 where
  n := 4
  w := ![![127, 0, 0, 0, 0], ![126, 80, 64, 405, 10]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K127 : KummerData 127 ![I127N0, I127N1] ![127, 260144641] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A127
  C := by
    intro i
    match i with
    | 0 => exact C1270
    | 1 => exact C1271
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 127 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0, 0, 0], ![393, -131, 0, 655, 0]] i)))

def P131P0 : CertificateIrreducibleZModOfList' 131 5 2 7 [93, 119, 0, 106, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 130, 23, 65, 84], [62, 101, 35, 97, 128], [48, 108, 106, 111, 25], [128, 53, 98, 120, 25], [0, 1]]
 g := ![![[42, 103, 31, 65, 27], [112, 80, 112, 18, 108], [47, 11, 9, 7], [119, 54, 73, 62], [0, 25, 0, 1], [], []], ![[120, 69, 94, 36, 101, 110, 105, 16], [123, 2, 54, 80, 45, 17, 17, 27], [5, 76, 104, 77], [7, 12], [101, 98, 30, 49], [72, 102], [67, 41, 47, 113]], ![[80, 72, 100, 29, 87, 31, 38, 37], [70, 121, 59, 42, 2, 104, 12, 118], [98, 15, 75, 121], [99, 53, 64, 4], [89, 77, 42, 43], [7, 88, 119, 11], [18, 123, 73, 9]], ![[90, 63, 39, 50, 36, 58, 79, 36], [94, 45, 29, 17, 34, 70, 38, 107], [34, 97, 40, 100], [8, 5, 9, 105], [59, 40, 10, 3], [128, 44, 25, 9], [2, 103, 48, 101]], ![[28, 36, 81, 77, 130, 108, 50, 105], [105, 21, 98, 64, 17, 52, 29, 27], [106, 35, 15, 55], [74, 6, 20, 34], [62, 92, 94, 3], [63, 87, 87, 58], [106, 79, 105, 101]]]
 h' := ![![[24, 130, 23, 65, 84], [64, 11, 6, 79, 114], [122, 42, 78, 112, 34], [68, 74, 57, 69, 20], [0, 33, 38, 38, 113], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[62, 101, 35, 97, 128], [46, 104, 30, 73, 10], [22, 76, 12, 92, 23], [116, 87, 104, 119, 83], [51, 115, 87, 55], [76, 126, 111, 54, 124], [109, 87, 108, 44], [24, 130, 23, 65, 84]], ![[48, 108, 106, 111, 25], [16, 43, 116, 68, 72], [60, 91, 71, 38, 110], [129, 119, 88, 74, 120], [67, 64, 43, 115, 129], [109, 0, 95, 37, 82], [74, 122, 58, 68, 50], [62, 101, 35, 97, 128]], ![[128, 53, 98, 120, 25], [36, 64, 87, 72, 25], [25, 61, 67, 6, 46], [49, 19, 122, 2, 10], [20, 49, 100, 93, 74], [108, 73, 27, 24, 93], [22, 27, 10, 26, 3], [48, 108, 106, 111, 25]], ![[0, 1], [7, 40, 23, 101, 41], [74, 123, 34, 14, 49], [99, 94, 22, 129, 29], [13, 1, 125, 92, 77], [88, 63, 29, 16, 93], [107, 26, 85, 124, 78], [128, 53, 98, 120, 25]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [110, 79, 115, 36], [], [], []]
 b := ![[], [5, 115, 79, 101, 37], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A131 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 131 1 where
 D := ![[93, 119, 0, 106, 0, 1]]; D' := ![[93, 119, 0, 106, 0, 1]]
 heqm := by decide
 hProd := by decide
 s := ![7]
 n := ![5]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P131P0

def C1310 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A131.D 0) 131 where
  n := 5
  w := ![![131, 0, 0, 0, 0], ![393, -131, 0, 655, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K131 : KummerData 131 ![I131N0] ![38579489651] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A131
  C := by
    intro i
    match i with
    | 0 => exact C1310
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 131 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0, 0, 0], ![88, 75, 1, 0, 0]] i)))

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0, 0, 0], ![90, 32, 62, 5, 0]] i)))

def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [88, 75, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [62, 136], [0, 1]]
 g := ![![[46, 123], [135], [39], [10, 126], [16], [8], [1]], ![[0, 14], [135], [39], [13, 11], [16], [8], [1]]]
 h' := ![![[62, 136], [5, 64], [69, 51], [79, 83], [31, 20], [53, 133], [49, 62], [0, 1]], ![[0, 1], [0, 73], [80, 86], [19, 54], [38, 117], [79, 4], [57, 75], [62, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [94]]
 b := ![[], [50, 47]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P137P1 : CertificateIrreducibleZModOfList' 137 3 2 7 [90, 32, 62, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [83, 62, 47], [129, 74, 90], [0, 1]]
 g := ![![[28, 56, 39], [17, 103], [114, 18], [119, 99, 121], [101, 28], [75, 1], []], ![[1, 59, 113, 102], [26, 121], [106, 28], [76, 17, 6, 67], [118, 44], [39, 133], [116, 17]], ![[114, 50, 22, 97], [29, 76], [24, 103], [106, 117, 104, 26], [17, 135], [79, 8], [73, 17]]]
 h' := ![![[83, 62, 47], [45, 132, 54], [43, 36, 68], [113, 95, 93], [88, 134, 126], [100, 113, 113], [0, 0, 1], [0, 1]], ![[129, 74, 90], [87, 34, 62], [80, 118, 11], [116, 13, 113], [129, 23, 4], [36, 64, 110], [11, 118, 74], [83, 62, 47]], ![[0, 1], [29, 108, 21], [131, 120, 58], [109, 29, 68], [27, 117, 7], [119, 97, 51], [70, 19, 62], [129, 74, 90]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 78], []]
 b := ![[], [26, 88, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A137 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 137 2 where
 D := ![[88, 75, 1], [90, 32, 62, 1]]; D' := ![[88, 75, 1], [90, 32, 62, 1]]
 heqm := by decide
 hProd := by decide
 s := ![7, 7]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P137P0
  | 1 => exact P137P1

def C1370 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A137.D 0) 137 where
  n := 2
  w := ![![137, 0, 0, 0, 0], ![88, 75, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C1371 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A137.D 1) 137 where
  n := 3
  w := ![![137, 0, 0, 0, 0], ![90, 32, 62, 5, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K137 : KummerData 137 ![I137N0, I137N1] ![18769, 2571353] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A137
  C := by
    intro i
    match i with
    | 0 => exact C1370
    | 1 => exact C1371
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 137 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0, 0, 0], ![36, 1, 0, 0, 0]] i)))

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0, 0, 0], ![69, 1, 0, 0, 0]] i)))

def I139N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0, 0, 0], ![63, 37, 34, 5, 0]] i)))

def P139P0 : CertificateIrreducibleZModOfList' 139 1 2 7 [36, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [112], [], [57], [], [], [103, 1]]]
 h' := ![![[0, 1], [138], [116], [33], [125], [79], [45], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P139P1 : CertificateIrreducibleZModOfList' 139 1 2 7 [69, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [137], [], [83], [], [], [70, 1]]]
 h' := ![![[0, 1], [138], [89], [111], [120], [113], [35], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P139P2 : CertificateIrreducibleZModOfList' 139 3 2 7 [63, 37, 34, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [88, 57, 38], [17, 81, 101], [0, 1]]
 g := ![![[67, 105, 65], [27, 59, 42], [61, 65], [18, 47, 65], [52, 49], [105, 1], []], ![[112, 51, 31, 69], [92, 138, 9, 120], [108, 25], [121, 45, 25, 118], [11, 51], [130, 28], [133, 54]], ![[14, 106, 130, 94], [42, 57, 93, 123], [111, 35], [50, 87, 29, 119], [32, 69], [91, 52], [70, 54]]]
 h' := ![![[88, 57, 38], [106, 122, 75], [116, 91, 96], [117, 21, 64], [112, 3, 75], [57, 83, 7], [0, 0, 1], [0, 1]], ![[17, 81, 101], [52, 21, 8], [123, 88, 114], [106, 68, 5], [11, 49, 73], [136, 14, 107], [60, 41, 81], [88, 57, 38]], ![[0, 1], [17, 135, 56], [112, 99, 68], [135, 50, 70], [85, 87, 130], [4, 42, 25], [49, 98, 57], [17, 81, 101]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [110, 32], []]
 b := ![[], [65, 19, 65], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A139 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 139 3 where
 D := ![[36, 1], [69, 1], [63, 37, 34, 1]]; D' := ![[36, 1], [69, 1], [63, 37, 34, 1]]
 heqm := by decide
 hProd := by decide
 s := ![7, 7, 7]
 n := ![1, 1, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P139P0
  | 1 => exact P139P1
  | 2 => exact P139P2

def C1390 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A139.D 0) 139 where
  n := 1
  w := ![![139, 0, 0, 0, 0], ![36, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C1391 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A139.D 1) 139 where
  n := 1
  w := ![![139, 0, 0, 0, 0], ![69, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C1392 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A139.D 2) 139 where
  n := 3
  w := ![![139, 0, 0, 0, 0], ![63, 37, 34, 5, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K139 : KummerData 139 ![I139N0, I139N1, I139N2] ![139, 139, 2685619] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A139
  C := by
    intro i
    match i with
    | 0 => exact C1390
    | 1 => exact C1391
    | 2 => exact C1392
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 139 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0, 0, 0], ![138, 1, 0, 0, 0]] i)))

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0, 0, 0], ![143, 1, 0, 0, 0]] i)))

def I149N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0, 0, 0], ![9, 49, 17, 5, 0]] i)))

def P149P0 : CertificateIrreducibleZModOfList' 149 1 2 7 [138, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [145], [], [31], [], [11, 1]]]
 h' := ![![[0, 1], [148], [105], [61], [43], [39], [121], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P149P1 : CertificateIrreducibleZModOfList' 149 1 2 7 [143, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [25], [], [88], [], [6, 1]]]
 h' := ![![[0, 1], [1], [1], [5], [81], [104], [36], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P149P2 : CertificateIrreducibleZModOfList' 149 3 2 7 [9, 49, 17, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [63, 104, 23], [69, 44, 126], [0, 1]]
 g := ![![[142, 77, 47], [121, 7], [85, 86, 17], [40, 4], [127, 102, 86], [132, 1], []], ![[79, 123, 65, 97], [8, 42], [103, 120, 26, 122], [8, 104], [138, 114, 114, 65], [43, 148], [112, 82]], ![[39, 145, 37, 83], [35, 76], [65, 26, 27, 38], [56, 113], [109, 137, 84, 52], [68, 88], [9, 82]]]
 h' := ![![[63, 104, 23], [56, 10, 14], [129, 66, 56], [104, 54, 49], [49, 27, 2], [4, 79, 91], [0, 0, 1], [0, 1]], ![[69, 44, 126], [122, 35, 101], [94, 13, 108], [42, 87, 120], [73, 25, 113], [123, 119, 10], [130, 24, 44], [63, 104, 23]], ![[0, 1], [110, 104, 34], [53, 70, 134], [114, 8, 129], [97, 97, 34], [129, 100, 48], [61, 125, 104], [69, 44, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [124, 14], []]
 b := ![[], [84, 145, 116], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A149 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 149 3 where
 D := ![[138, 1], [143, 1], [9, 49, 17, 1]]; D' := ![[138, 1], [143, 1], [9, 49, 17, 1]]
 heqm := by decide
 hProd := by decide
 s := ![7, 7, 7]
 n := ![1, 1, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P149P0
  | 1 => exact P149P1
  | 2 => exact P149P2

def C1490 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A149.D 0) 149 where
  n := 1
  w := ![![149, 0, 0, 0, 0], ![138, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C1491 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A149.D 1) 149 where
  n := 1
  w := ![![149, 0, 0, 0, 0], ![143, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C1492 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A149.D 2) 149 where
  n := 3
  w := ![![149, 0, 0, 0, 0], ![9, 49, 17, 5, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K149 : KummerData 149 ![I149N0, I149N1, I149N2] ![149, 149, 3307949] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A149
  C := by
    intro i
    match i with
    | 0 => exact C1490
    | 1 => exact C1491
    | 2 => exact C1492
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 149 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0, 0, 0], ![302, -151, 0, 755, 0]] i)))

def P151P0 : CertificateIrreducibleZModOfList' 151 5 2 7 [2, 99, 0, 126, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 133, 50, 56, 144], [118, 111, 21, 58, 78], [46, 20, 9, 29, 106], [137, 37, 71, 8, 125], [0, 1]]
 g := ![![[75, 14, 47, 5, 69], [3, 3, 45, 112, 76], [146, 79, 42, 39, 1], [56, 0, 33, 4], [73, 0, 25, 0, 1], [], []], ![[110, 7, 10, 107, 63, 97, 137, 19], [42, 0, 30, 3, 5, 104, 28, 72], [113, 105, 52, 28, 106, 110, 36, 85], [52, 113, 127, 38], [110, 22, 125, 66, 143, 50], [39, 106, 136, 138], [144, 37, 122, 49]], ![[138, 132, 142, 118, 53, 142, 111, 45], [102, 87, 51, 20, 101, 68, 99, 74], [106, 141, 67, 86, 42, 117, 99, 29], [89, 101, 28, 95], [58, 84, 94, 73, 113, 144, 87, 55], [116, 26, 42, 124], [124, 39, 139, 44]], ![[10, 133, 17, 22, 147, 106, 81, 66], [132, 132, 3, 137, 74, 44, 20, 28], [40, 16, 43, 147, 33, 7, 5, 126], [126, 16, 102, 118], [23, 91, 96, 63, 73, 94, 0, 73], [144, 59, 12, 45], [63, 71, 108, 62]], ![[59, 12, 94, 91, 33, 136, 1, 116], [29, 42, 126, 88, 135, 130, 52, 43], [31, 73, 135, 76, 131, 100, 69, 11], [109, 31, 115, 1], [115, 125, 83, 75, 125, 130, 69, 17], [149, 57, 12, 20], [137, 135, 37, 72]]]
 h' := ![![[1, 133, 50, 56, 144], [145, 99, 89, 11, 62], [10, 54, 17, 9, 23], [64, 102, 26, 95, 1], [5, 21, 101, 105, 149], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[118, 111, 21, 58, 78], [145, 148, 23, 76, 45], [94, 138, 148, 0, 128], [138, 84, 125, 82, 22], [98, 128, 54, 24, 75], [147, 129, 96, 6], [15, 130, 141, 4, 17], [1, 133, 50, 56, 144]], ![[46, 20, 9, 29, 106], [6, 58, 61, 132, 13], [128, 48, 41, 28, 40], [59, 84, 86, 0, 125], [29, 123, 65, 26, 47], [67, 98, 14, 69, 18], [86, 101, 1, 51, 107], [118, 111, 21, 58, 78]], ![[137, 37, 71, 8, 125], [134, 2, 91, 37, 89], [83, 77, 6, 73, 63], [27, 123, 89, 60, 119], [85, 13, 74, 129, 32], [139, 89, 139, 116, 58], [27, 142, 23, 129, 137], [46, 20, 9, 29, 106]], ![[0, 1], [11, 146, 38, 46, 93], [144, 136, 90, 41, 48], [72, 60, 127, 65, 35], [130, 17, 8, 18, 150], [48, 137, 53, 111, 74], [73, 80, 136, 118, 41], [137, 37, 71, 8, 125]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [75, 138, 42, 124], [], [], []]
 b := ![[], [2, 38, 13, 83, 104], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A151 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 151 1 where
 D := ![[2, 99, 0, 126, 0, 1]]; D' := ![[2, 99, 0, 126, 0, 1]]
 heqm := by decide
 hProd := by decide
 s := ![7]
 n := ![5]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P151P0

def C1510 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A151.D 0) 151 where
  n := 5
  w := ![![151, 0, 0, 0, 0], ![302, -151, 0, 755, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K151 : KummerData 151 ![I151N0] ![78502725751] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A151
  C := by
    intro i
    match i with
    | 0 => exact C1510
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 151 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


lemma PB1045I3_primes (p : ℕ) :
  p ∈ Set.range ![107, 109, 113, 127, 131, 137, 139, 149, 151] ↔ Nat.Prime p ∧ 103 < p ∧ p ≤ 151 := by
  rw [← List.mem_ofFn']
  convert primes_range 103 151 (by omega)
  decide

def PB1045I3 : PrimesBelowBoundCertificateInterval O 103 151 1045 where
  m := 9
  g := ![2, 1, 2, 2, 1, 2, 3, 3, 1]
  P := ![107, 109, 113, 127, 131, 137, 139, 149, 151]
  hP := PB1045I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I107N0, I107N1]
    · exact ![I109N0]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1]
    · exact ![I131N0]
    · exact ![I137N0, I137N1]
    · exact ![I139N0, I139N1, I139N2]
    · exact ![I149N0, I149N1, I149N2]
    · exact ![I151N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · convert (containsPrimesAbove_of_KummerData K107) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K109) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K113) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K127) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K131) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K137) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K139) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K149) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K151) <;> rfl
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![11449, 1225043]
    · exact ![15386239549]
    · exact ![113, 163047361]
    · exact ![127, 260144641]
    · exact ![38579489651]
    · exact ![18769, 2571353]
    · exact ![139, 139, 2685619]
    · exact ![149, 149, 3307949]
    · exact ![78502725751]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact (card_quot_of_KummerData K107)
    · exact (card_quot_of_KummerData K109)
    · exact (card_quot_of_KummerData K113)
    · exact (card_quot_of_KummerData K127)
    · exact (card_quot_of_KummerData K131)
    · exact (card_quot_of_KummerData K137)
    · exact (card_quot_of_KummerData K139)
    · exact (card_quot_of_KummerData K149)
    · exact (card_quot_of_KummerData K151)
  β := ![I113N0, I127N0, I139N0, I139N1, I149N0, I149N1]
  Il := ![[], [], [I113N0], [I127N0], [], [], [I139N0, I139N1], [I149N0, I149N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
