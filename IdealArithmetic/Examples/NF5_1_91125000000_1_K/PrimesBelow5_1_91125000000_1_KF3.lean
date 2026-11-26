
import IdealArithmetic.Examples.NF5_1_91125000000_1_K.RI5_1_91125000000_1_K
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 

instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0, 0, 0], ![40, 106, 1, 0, 0]] i)))

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0, 0, 0], ![35, 69, 1, 2, 0]] i)))

def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [40, 106, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 106], [0, 1]]
 g := ![![[8, 99], [68, 39], [92], [39, 102], [23], [1, 1]], ![[0, 8], [0, 68], [92], [34, 5], [23], [2, 106]]]
 h' := ![![[1, 106], [62, 45], [57, 50], [45, 78], [38, 40], [67, 68], [0, 1]], ![[0, 1], [0, 62], [0, 57], [16, 29], [78, 67], [28, 39], [1, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [72, 70]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P107P1 : CertificateIrreducibleZModOfList' 107 3 2 6 [35, 68, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [90, 20, 51], [16, 86, 56], [0, 1]]
 g := ![![[28, 26, 52], [63, 1, 30], [42, 36], [3, 78, 9], [28, 1], [1]], ![[7, 30, 104, 91], [34, 95], [31, 99], [101, 82, 46, 7], [99, 101], [30, 95, 83, 78]], ![[79, 103, 42, 30], [5, 53, 21, 75], [64, 33], [94, 77, 42, 105], [17, 41], [4, 52, 32, 29]]]
 h' := ![![[90, 20, 51], [42, 22, 65], [32, 83, 64], [2, 60, 6], [31, 39, 104], [72, 39, 106], [0, 1]], ![[16, 86, 56], [28, 44, 78], [29, 47], [77, 49, 45], [51, 18, 19], [29, 98, 84], [90, 20, 51]], ![[0, 1], [33, 41, 71], [86, 84, 43], [20, 105, 56], [56, 50, 91], [104, 77, 24], [16, 86, 56]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [84, 88], []]
 b := ![[], [47, 41, 78], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A107 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 107 2 where
 D := ![[40, 106, 1], [35, 68, 1, 1]]; D' := ![[40, 106, 1], [35, 68, 1, 1]]
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
  w := ![![107, 0, 0, 0, 0], ![40, 106, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C1071 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A107.D 1) 107 where
  n := 3
  w := ![![107, 0, 0, 0, 0], ![35, 69, 1, 2, 0]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0, 0, 0], ![15805, 545, 109, 0, 0]] i)))

def P109P0 : CertificateIrreducibleZModOfList' 109 5 2 6 [85, 20, 9, 0, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 62, 70, 94, 94], [12, 40, 15, 12, 73], [13, 53, 90, 83, 60], [78, 62, 43, 29, 100], [0, 1]]
 g := ![![[82, 48, 36, 51, 94], [92, 61, 60, 81], [105, 56, 45, 76, 82], [77, 33, 81], [0, 1], []], ![[21, 44, 46, 45, 36, 10, 105, 87], [100, 88, 98, 88], [79, 34, 55, 64, 41, 10, 52, 75], [88, 108, 14, 6, 57, 105, 100, 78], [22, 43, 64, 75], [59, 87, 16, 95, 68, 65, 12, 4]], ![[75, 16, 67, 16, 60, 98, 67, 9], [40, 89, 72, 29], [9, 77, 92, 81, 72, 61, 48, 71], [37, 24, 98, 6, 18, 33, 40, 1], [42, 104, 67, 45], [33, 98, 63, 83, 30, 40, 4, 105]], ![[47, 44, 63, 98, 42, 17, 64, 49], [30, 41, 71, 66], [105, 74, 41, 20, 45, 73, 9, 71], [81, 61, 97, 59, 34, 42, 36, 60], [66, 53, 49, 22], [0, 99, 30, 89, 90, 83, 93, 71]], ![[13, 65, 30, 74, 10, 12, 107, 15], [66, 52, 100, 108], [13, 67, 78, 54, 37, 95, 102, 105], [37, 89, 22, 15, 107, 11, 15, 102], [48, 8, 55, 100], [90, 25, 11, 37, 42, 59, 71, 34]]]
 h' := ![![[6, 62, 70, 94, 94], [88, 20, 9, 54, 58], [13, 32, 64, 76, 9], [104, 15, 46, 76, 55], [0, 24, 89, 100], [0, 0, 0, 1], [0, 1]], ![[12, 40, 15, 12, 73], [38, 50, 73, 71, 105], [6, 13, 54, 24, 52], [98, 27, 56, 91, 70], [101, 94, 63, 93, 55], [106, 83, 91, 90, 27], [6, 62, 70, 94, 94]], ![[13, 53, 90, 83, 60], [13, 53, 29, 46, 71], [19, 15, 86, 17, 47], [47, 78, 20, 21, 70], [87, 68, 105, 11, 60], [13, 6, 6, 73, 46], [12, 40, 15, 12, 73]], ![[78, 62, 43, 29, 100], [46, 50, 56, 5, 76], [31, 79, 89, 86, 34], [59, 15, 100, 69, 60], [20, 52, 99, 34, 108], [17, 35, 13, 24, 26], [13, 53, 90, 83, 60]], ![[0, 1], [43, 45, 51, 42, 17], [58, 79, 34, 15, 76], [82, 83, 105, 70, 72], [35, 89, 80, 89, 104], [55, 94, 108, 30, 10], [78, 62, 43, 29, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [98, 19, 73, 37], [], [], []]
 b := ![[], [47, 89, 100, 46, 17], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A109 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 109 1 where
 D := ![[85, 20, 9, 0, 0, 1]]; D' := ![[85, 20, 9, 0, 0, 1]]
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
  w := ![![109, 0, 0, 0, 0], ![15805, 545, 109, 0, 0]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0, 0, 0], ![37, 104, 1, 0, 0]] i)))

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0, 0, 0], ![76, 45, 9, 2, 0]] i)))

def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [37, 104, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 112], [0, 1]]
 g := ![![[70, 60], [72], [69], [11], [98, 15], [9, 1]], ![[45, 53], [72], [69], [11], [7, 98], [18, 112]]]
 h' := ![![[9, 112], [32, 88], [53, 80], [32, 71], [103, 24], [6, 44], [0, 1]], ![[0, 1], [33, 25], [95, 33], [106, 42], [93, 89], [63, 69], [9, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [108]]
 b := ![[], [96, 54]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P113P1 : CertificateIrreducibleZModOfList' 113 3 2 6 [76, 44, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [107, 76, 14], [110, 36, 99], [0, 1]]
 g := ![![[9, 38, 22], [1, 102], [105, 109], [70, 25], [77, 63, 81], [1]], ![[9, 96, 106, 85], [18, 109], [], [80, 106], [72, 59, 12, 64], [107, 98, 104, 32]], ![[100, 1, 13, 105], [76, 81], [41, 109], [72, 72], [10, 67, 60, 13], [85, 30, 99, 81]]]
 h' := ![![[107, 76, 14], [99, 83, 94], [47, 73, 21], [2, 52, 30], [24, 86, 5], [37, 69, 104], [0, 1]], ![[110, 36, 99], [100, 86, 26], [15, 102, 83], [44, 14], [19, 79, 28], [14, 7, 77], [107, 76, 14]], ![[0, 1], [49, 57, 106], [66, 51, 9], [73, 47, 83], [11, 61, 80], [67, 37, 45], [110, 36, 99]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [104, 59], []]
 b := ![[], [93, 17, 20], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A113 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 113 2 where
 D := ![[37, 104, 1], [76, 44, 9, 1]]; D' := ![[37, 104, 1], [76, 44, 9, 1]]
 heqm := by decide
 hProd := by decide
 s := ![6, 6]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P113P0
  | 1 => exact P113P1

def C1130 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A113.D 0) 113 where
  n := 2
  w := ![![113, 0, 0, 0, 0], ![37, 104, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C1131 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A113.D 1) 113 where
  n := 3
  w := ![![113, 0, 0, 0, 0], ![76, 45, 9, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K113 : KummerData 113 ![I113N0, I113N1] ![12769, 1442897] where
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0, 0, 0], ![98, 116, 1, 0, 0]] i)))

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0, 0, 0], ![91, 24, 11, 2, 0]] i)))

def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [98, 116, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 126], [0, 1]]
 g := ![![[123, 35], [59, 87], [54, 99], [21, 36], [46, 21], [11, 1]], ![[0, 92], [0, 40], [0, 28], [36, 91], [23, 106], [22, 126]]]
 h' := ![![[11, 126], [60, 110], [42, 77], [101, 37], [64, 6], [65, 23], [0, 1]], ![[0, 1], [0, 17], [0, 50], [0, 90], [3, 121], [64, 104], [11, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60]]
 b := ![[], [89, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P127P1 : CertificateIrreducibleZModOfList' 127 3 2 6 [91, 23, 11, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 75, 19], [108, 51, 108], [0, 1]]
 g := ![![[99, 108, 73], [19, 74, 72], [85, 116, 122], [23, 105, 44], [60, 64, 121], [1]], ![[32, 48, 12, 50], [73, 50, 35, 68], [123, 28, 7, 17], [52, 35, 40, 37], [118, 23, 119, 60], [87, 46, 61, 1]], ![[88, 124, 32, 23], [23, 101, 112, 46], [51, 69, 70, 66], [111, 31, 76, 57], [19, 22, 58, 85], [86, 110, 126, 126]]]
 h' := ![![[8, 75, 19], [49, 85, 33], [12, 100, 31], [66, 77, 54], [1, 61, 60], [36, 104, 116], [0, 1]], ![[108, 51, 108], [21, 56, 123], [43, 90, 52], [43, 53, 26], [33, 94, 28], [88, 85, 18], [8, 75, 19]], ![[0, 1], [93, 113, 98], [63, 64, 44], [117, 124, 47], [115, 99, 39], [47, 65, 120], [108, 51, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44, 84], []]
 b := ![[], [87, 50, 29], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A127 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 127 2 where
 D := ![[98, 116, 1], [91, 23, 11, 1]]; D' := ![[98, 116, 1], [91, 23, 11, 1]]
 heqm := by decide
 hProd := by decide
 s := ![6, 6]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P127P0
  | 1 => exact P127P1

def C1270 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A127.D 0) 127 where
  n := 2
  w := ![![127, 0, 0, 0, 0], ![98, 116, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C1271 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A127.D 1) 127 where
  n := 3
  w := ![![127, 0, 0, 0, 0], ![91, 24, 11, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K127 : KummerData 127 ![I127N0, I127N1] ![16129, 2048383] where
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] i)))

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0, 0, 0], ![4, 1, 0, 0, 0]] i)))

def I131N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0, 0, 0], ![22, 1, 0, 0, 0]] i)))

def I131N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0, 0, 0], ![44, 1, 0, 0, 0]] i)))

def I131N4 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0, 0, 0], ![61, 1, 0, 0, 0]] i)))

def P131P0 : CertificateIrreducibleZModOfList' 131 1 2 7 [0, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[130], [], [], [], [], [], [0, 1]]]
 h' := ![![[0, 1], [], [], [], [], [], [], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P131P1 : CertificateIrreducibleZModOfList' 131 1 2 7 [4, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [33], [], [], [], [], [127, 1]]]
 h' := ![![[0, 1], [130], [65], [117], [36], [125], [16], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P131P2 : CertificateIrreducibleZModOfList' 131 1 2 7 [22, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [125], [], [], [], [], [109, 1]]]
 h' := ![![[0, 1], [1], [16], [4], [129], [28], [91], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P131P3 : CertificateIrreducibleZModOfList' 131 1 2 7 [44, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [3], [], [], [], [], [87, 1]]]
 h' := ![![[0, 1], [130], [38], [13], [12], [55], [102], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P131P4 : CertificateIrreducibleZModOfList' 131 1 2 7 [61, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [58], [], [], [], [], [70, 1]]]
 h' := ![![[0, 1], [130], [53], [61], [89], [58], [53], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A131 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 131 5 where
 D := ![[0, 1], [4, 1], [22, 1], [44, 1], [61, 1]]; D' := ![[0, 1], [4, 1], [22, 1], [44, 1], [61, 1]]
 heqm := by decide
 hProd := by decide
 s := ![7, 7, 7, 7, 7]
 n := ![1, 1, 1, 1, 1]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P131P0
  | 1 => exact P131P1
  | 2 => exact P131P2
  | 3 => exact P131P3
  | 4 => exact P131P4

def C1310 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A131.D 0) 131 where
  n := 1
  w := ![![131, 0, 0, 0, 0], ![0, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C1311 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A131.D 1) 131 where
  n := 1
  w := ![![131, 0, 0, 0, 0], ![4, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C1312 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A131.D 2) 131 where
  n := 1
  w := ![![131, 0, 0, 0, 0], ![22, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C1313 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A131.D 3) 131 where
  n := 1
  w := ![![131, 0, 0, 0, 0], ![44, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C1314 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A131.D 4) 131 where
  n := 1
  w := ![![131, 0, 0, 0, 0], ![61, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K131 : KummerData 131 ![I131N0, I131N1, I131N2, I131N3, I131N4] ![131, 131, 131, 131, 131] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A131
  C := by
    intro i
    match i with
    | 0 => exact C1310
    | 1 => exact C1311
    | 2 => exact C1312
    | 3 => exact C1313
    | 4 => exact C1314
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 131 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0, 0, 0], ![77, 1, 0, 0, 0]] i)))

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0, 0, 0], ![773, 2287, 10933, -2918, 22728]] i)))

def P137P0 : CertificateIrreducibleZModOfList' 137 1 2 7 [77, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [16], [], [], [60, 1]]]
 h' := ![![[0, 1], [1], [1], [1], [133], [74], [38], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P137P1 : CertificateIrreducibleZModOfList' 137 4 2 7 [125, 125, 38, 60, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [74, 82, 45, 80], [62, 16, 58, 60], [78, 38, 34, 134], [0, 1]]
 g := ![![[29, 135, 124, 61], [80, 97, 37], [76, 91, 2], [72, 126, 91, 77], [130, 88, 38], [1], []], ![[55, 24, 102, 2, 73, 75], [50], [92, 94, 105], [63, 117, 54, 47, 75, 106], [101, 134, 81], [51, 80, 9], [36, 87, 98]], ![[45, 2, 114, 123, 93, 126], [16, 82, 7], [49, 24, 49], [2, 93, 36, 120, 71, 63], [71, 83, 15], [21, 37, 56], [54, 22, 38]], ![[66, 8, 109, 56, 93, 89], [50, 66, 69], [56, 92, 68], [120, 14, 113, 55, 86, 6], [12, 22, 135], [128, 71, 122], [16, 78, 9]]]
 h' := ![![[74, 82, 45, 80], [124, 28, 59, 46], [73, 102, 60, 41], [42, 85, 94, 31], [60, 27, 51, 112], [12, 12, 99, 77], [0, 0, 1], [0, 1]], ![[62, 16, 58, 60], [68, 86, 103, 30], [4, 107, 18], [63, 106, 122, 70], [55, 126, 28, 83], [79, 87, 27, 128], [17, 49, 125, 134], [74, 82, 45, 80]], ![[78, 38, 34, 134], [119, 40, 36, 57], [8, 66, 78, 12], [70, 4, 121, 130], [39, 37, 119, 130], [134, 5, 96, 120], [108, 19, 88, 59], [62, 16, 58, 60]], ![[0, 1], [124, 120, 76, 4], [88, 136, 118, 84], [85, 79, 74, 43], [133, 84, 76, 86], [20, 33, 52, 86], [111, 69, 60, 81], [78, 38, 34, 134]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [38, 93, 18], []]
 b := ![[], [], [14, 75, 115, 123], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A137 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 137 2 where
 D := ![[77, 1], [125, 125, 38, 60, 1]]; D' := ![[77, 1], [125, 125, 38, 60, 1]]
 heqm := by decide
 hProd := by decide
 s := ![7, 7]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P137P0
  | 1 => exact P137P1

def C1370 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A137.D 0) 137 where
  n := 1
  w := ![![137, 0, 0, 0, 0], ![77, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C1371 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A137.D 1) 137 where
  n := 4
  w := ![![137, 0, 0, 0, 0], ![773, 2287, 10933, -2918, 22728]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K137 : KummerData 137 ![I137N0, I137N1] ![137, 352275361] where
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

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0, 0, 0], ![15846, 556, 139, 0, 0]] i)))

def P139P0 : CertificateIrreducibleZModOfList' 139 5 2 7 [126, 31, 39, 0, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [101, 7, 6, 7, 58], [75, 18, 137, 126, 96], [100, 104, 136, 59, 84], [2, 9, 138, 86, 40], [0, 1]]
 g := ![![[104, 42, 32, 89, 38], [24, 82, 11, 88, 54], [106, 86, 11, 49], [79, 84, 109, 28, 127], [100, 0, 0, 1], [], []], ![[111, 62, 73, 26, 11, 93, 114, 110], [10, 122, 8, 131, 82, 64, 60, 134], [84, 105, 107, 6], [91, 46, 9, 64, 28, 64, 62, 90], [43, 100, 80, 121], [106, 27, 93, 69], [82, 50, 117, 28]], ![[137, 105, 136, 48, 36, 72, 54, 112], [93, 74, 48, 5, 58, 82, 91, 120], [12, 11, 83, 5], [76, 124, 1, 123, 85, 107, 67, 66], [0, 91, 90, 41], [29, 18, 39, 7], [63, 63, 6, 42]], ![[41, 118, 110, 15, 27, 132, 99, 108], [77, 57, 128, 126, 64, 24, 93, 10], [9, 73, 37, 28], [72, 25, 20, 62, 118, 117, 18, 62], [42, 67, 98, 31], [1, 45, 50, 37], [57, 58, 43, 106]], ![[38, 85, 41, 19, 32, 62, 30, 56], [58, 51, 89, 35, 86, 14, 84, 119], [91, 98, 68, 122], [48, 33, 10, 63, 100, 121, 39, 32], [65, 85, 73, 127], [131, 45, 53, 57], [3, 88, 69, 71]]]
 h' := ![![[101, 7, 6, 7, 58], [34, 130, 133, 8, 49], [124, 79, 26, 72, 101], [54, 71, 95, 110, 7], [49, 97, 131, 13, 108], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[75, 18, 137, 126, 96], [6, 81, 138, 56, 25], [104, 93, 49, 75, 94], [92, 113, 125, 28, 59], [66, 76, 85, 117, 61], [52, 120, 56, 9, 128], [8, 78, 119, 38, 25], [101, 7, 6, 7, 58]], ![[100, 104, 136, 59, 84], [92, 112, 21, 96, 123], [68, 73, 86, 80, 6], [107, 17, 53, 44, 12], [96, 57, 68, 52, 100], [97, 116, 9, 18, 72], [50, 37, 1, 51, 29], [75, 18, 137, 126, 96]], ![[2, 9, 138, 86, 40], [69, 114, 96, 32, 67], [35, 17, 134, 113, 52], [14, 71, 30, 56, 81], [31, 2, 2, 75, 125], [67, 108, 65, 131, 46], [38, 49, 82, 63, 71], [100, 104, 136, 59, 84]], ![[0, 1], [46, 119, 29, 86, 14], [52, 16, 122, 77, 25], [26, 6, 114, 40, 119], [102, 46, 131, 21, 23], [77, 73, 9, 120, 31], [43, 114, 75, 126, 14], [2, 9, 138, 86, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20, 101, 91, 126], [], [], []]
 b := ![[], [48, 132, 49, 121, 17], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A139 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 139 1 where
 D := ![[126, 31, 39, 0, 0, 1]]; D' := ![[126, 31, 39, 0, 0, 1]]
 heqm := by decide
 hProd := by decide
 s := ![7]
 n := ![5]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P139P0

def C1390 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A139.D 0) 139 where
  n := 5
  w := ![![139, 0, 0, 0, 0], ![15846, 556, 139, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K139 : KummerData 139 ![I139N0] ![51888844699] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A139
  C := by
    intro i
    match i with
    | 0 => exact C1390
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 139 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0, 0, 0], ![20, 1, 0, 0, 0]] i)))

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0, 0, 0], ![82, 1, 0, 0, 0]] i)))

def I149N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0, 0, 0], ![74, 123, 47, 2, 0]] i)))

def P149P0 : CertificateIrreducibleZModOfList' 149 1 2 7 [20, 1] where
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
 g := ![![[], [], [67], [], [80], [], [129, 1]]]
 h' := ![![[0, 1], [1], [1], [31], [39], [123], [102], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P149P1 : CertificateIrreducibleZModOfList' 149 1 2 7 [82, 1] where
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
 g := ![![[], [], [129], [], [95], [], [67, 1]]]
 h' := ![![[0, 1], [1], [1], [125], [107], [63], [19], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P149P2 : CertificateIrreducibleZModOfList' 149 3 2 7 [74, 122, 47, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [35, 116, 19], [67, 32, 130], [0, 1]]
 g := ![![[70, 55, 19], [8, 132], [40, 116, 26], [106, 129], [146, 98, 1], [102, 1], []], ![[28, 40, 20, 124], [88, 142], [11, 52, 133, 61], [77, 53], [39, 56, 60, 88], [93, 130], [106, 63]], ![[138, 33, 6, 127], [95, 100], [103, 29, 53, 53], [129, 42], [72, 134, 130, 121], [142, 46], [144, 63]]]
 h' := ![![[35, 116, 19], [106, 56, 67], [20, 121, 70], [18, 62, 18], [73, 36, 125], [51, 147, 1], [0, 0, 1], [0, 1]], ![[67, 32, 130], [80, 71, 79], [143, 49, 69], [11, 113, 115], [14, 6, 65], [67, 128, 143], [86, 62, 32], [35, 116, 19]], ![[0, 1], [121, 22, 3], [44, 128, 10], [148, 123, 16], [3, 107, 108], [8, 23, 5], [91, 87, 116], [67, 32, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [85, 130], []]
 b := ![[], [80, 60, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A149 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 149 3 where
 D := ![[20, 1], [82, 1], [74, 122, 47, 1]]; D' := ![[20, 1], [82, 1], [74, 122, 47, 1]]
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
  w := ![![149, 0, 0, 0, 0], ![20, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C1491 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A149.D 1) 149 where
  n := 1
  w := ![![149, 0, 0, 0, 0], ![82, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C1492 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A149.D 2) 149 where
  n := 3
  w := ![![149, 0, 0, 0, 0], ![74, 123, 47, 2, 0]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0, 0, 0], ![26, 1, 0, 0, 0]] i)))

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0, 0, 0], ![65, 1, 0, 0, 0]] i)))

def I151N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0, 0, 0], ![114, 99, 60, 2, 0]] i)))

def P151P0 : CertificateIrreducibleZModOfList' 151 1 2 7 [26, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [29], [94], [], [84], [], [125, 1]]]
 h' := ![![[0, 1], [1], [123], [68], [81], [50], [72], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P151P1 : CertificateIrreducibleZModOfList' 151 1 2 7 [65, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [72], [91], [], [81], [], [86, 1]]]
 h' := ![![[0, 1], [1], [125], [98], [20], [9], [148], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P151P2 : CertificateIrreducibleZModOfList' 151 3 2 7 [114, 98, 60, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [115, 84, 51], [127, 66, 100], [0, 1]]
 g := ![![[48, 45, 4], [95, 78, 43], [149, 7, 97], [107, 121], [105, 88, 86], [91, 1], []], ![[101, 140, 94, 13], [140, 21, 80, 93], [92, 22, 123, 129], [43, 69], [54, 80, 137, 15], [67, 128], [35, 34]], ![[26, 104, 80, 9], [110, 78, 117, 47], [33, 30, 51, 123], [8, 34], [46, 111, 27, 10], [109, 110], [137, 34]]]
 h' := ![![[115, 84, 51], [42, 109, 2], [77, 93, 63], [53, 49, 61], [110, 125, 140], [45, 28, 29], [0, 0, 1], [0, 1]], ![[127, 66, 100], [92, 115, 104], [53, 30, 143], [55, 90, 32], [27, 52, 62], [35, 136, 20], [24, 85, 66], [115, 84, 51]], ![[0, 1], [109, 78, 45], [140, 28, 96], [150, 12, 58], [96, 125, 100], [149, 138, 102], [58, 66, 84], [127, 66, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20, 12], []]
 b := ![[], [143, 74, 133], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A151 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 151 3 where
 D := ![[26, 1], [65, 1], [114, 98, 60, 1]]; D' := ![[26, 1], [65, 1], [114, 98, 60, 1]]
 heqm := by decide
 hProd := by decide
 s := ![7, 7, 7]
 n := ![1, 1, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P151P0
  | 1 => exact P151P1
  | 2 => exact P151P2

def C1510 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A151.D 0) 151 where
  n := 1
  w := ![![151, 0, 0, 0, 0], ![26, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C1511 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A151.D 1) 151 where
  n := 1
  w := ![![151, 0, 0, 0, 0], ![65, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C1512 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A151.D 2) 151 where
  n := 3
  w := ![![151, 0, 0, 0, 0], ![114, 99, 60, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K151 : KummerData 151 ![I151N0, I151N1, I151N2] ![151, 151, 3442951] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A151
  C := by
    intro i
    match i with
    | 0 => exact C1510
    | 1 => exact C1511
    | 2 => exact C1512
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 151 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


lemma PB18792I3_primes (p : ℕ) :
  p ∈ Set.range ![107, 109, 113, 127, 131, 137, 139, 149, 151] ↔ Nat.Prime p ∧ 103 < p ∧ p ≤ 151 := by
  rw [← List.mem_ofFn']
  convert primes_range 103 151 (by omega)
  decide

def PB18792I3 : PrimesBelowBoundCertificateInterval O 103 151 18792 where
  m := 9
  g := ![2, 1, 2, 2, 5, 2, 1, 3, 3]
  P := ![107, 109, 113, 127, 131, 137, 139, 149, 151]
  hP := PB18792I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I107N0, I107N1]
    · exact ![I109N0]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1]
    · exact ![I131N0, I131N1, I131N2, I131N3, I131N4]
    · exact ![I137N0, I137N1]
    · exact ![I139N0]
    · exact ![I149N0, I149N1, I149N2]
    · exact ![I151N0, I151N1, I151N2]
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
    · exact ![12769, 1442897]
    · exact ![16129, 2048383]
    · exact ![131, 131, 131, 131, 131]
    · exact ![137, 352275361]
    · exact ![51888844699]
    · exact ![149, 149, 3307949]
    · exact ![151, 151, 3442951]
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
  β := ![I107N0, I113N0, I127N0, I131N0, I131N1, I131N2, I131N3, I131N4, I137N0, I149N0, I149N1, I151N0, I151N1]
  Il := ![[I107N0], [], [I113N0], [I127N0], [I131N0, I131N1, I131N2, I131N3, I131N4], [I137N0], [], [I149N0, I149N1], [I151N0, I151N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
