
import IdealArithmetic.Examples.NF5_1_91125000000_1_K.RI5_1_91125000000_1_K
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 

instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0, 0, 0], ![65, 1, 0, 0, 0]] i)))

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0, 0, 0], ![696, 2219, 11038, -2854, 22728]] i)))

def P157P0 : CertificateIrreducibleZModOfList' 157 1 2 7 [65, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [27], [141], [108], [], [92, 1]]]
 h' := ![![[0, 1], [156], [129], [98], [45], [39], [143], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P157P1 : CertificateIrreducibleZModOfList' 157 4 2 7 [48, 25, 143, 92, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [141, 119, 143, 7], [0, 37, 120, 143], [81, 0, 51, 7], [0, 1]]
 g := ![![[105, 125, 43, 89], [128, 74, 126], [82, 16, 26, 33], [42, 76, 6, 16], [76, 8, 125, 143], [1], []], ![[110, 135, 59, 40, 26, 85], [62, 19, 13], [39, 24, 137, 60, 141, 62], [16, 0, 28, 24, 109, 96], [76, 153, 138, 88, 51, 116], [19, 80, 17], [112, 6, 49]], ![[67, 154, 31, 66, 115, 9], [105, 149, 113], [126, 100, 20, 153, 121, 146], [77, 101, 145, 73, 7, 13], [29, 150, 152, 18, 8, 3], [87, 27, 37], [6, 117, 39]], ![[44, 13, 92, 53, 37, 38], [79, 18, 44], [85, 1, 61, 5, 34, 26], [98, 91, 25, 136, 103, 5], [82, 140, 50, 19, 94, 112], [141, 54, 52], [27, 131, 49]]]
 h' := ![![[141, 119, 143, 7], [100, 46, 84, 106], [146, 5, 98, 122], [25, 125, 60, 70], [120, 20, 90, 153], [109, 132, 14, 65], [0, 0, 1], [0, 1]], ![[0, 37, 120, 143], [112, 123, 96, 34], [24, 116, 83, 135], [66, 65, 156, 11], [49, 86, 146, 9], [140, 132, 17, 143], [61, 12, 16, 71], [141, 119, 143, 7]], ![[81, 0, 51, 7], [114, 37, 112, 70], [75, 11, 93, 120], [72, 124, 57, 144], [21, 31, 38, 10], [111, 21, 56, 110], [26, 43, 110, 42], [0, 37, 120, 143]], ![[0, 1], [25, 108, 22, 104], [150, 25, 40, 94], [114, 0, 41, 89], [109, 20, 40, 142], [131, 29, 70, 153], [84, 102, 30, 44], [81, 0, 51, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [36, 28, 46], []]
 b := ![[], [], [147, 141, 137, 93], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A157 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 157 2 where
 D := ![[65, 1], [48, 25, 143, 92, 1]]; D' := ![[65, 1], [48, 25, 143, 92, 1]]
 heqm := by decide
 hProd := by decide
 s := ![7, 7]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P157P0
  | 1 => exact P157P1

def C1570 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A157.D 0) 157 where
  n := 1
  w := ![![157, 0, 0, 0, 0], ![65, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C1571 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A157.D 1) 157 where
  n := 4
  w := ![![157, 0, 0, 0, 0], ![696, 2219, 11038, -2854, 22728]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K157 : KummerData 157 ![I157N0, I157N1] ![157, 607573201] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A157
  C := by
    intro i
    match i with
    | 0 => exact C1570
    | 1 => exact C1571
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 157 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp163 : Fact (Nat.Prime 163) := {out := by norm_num}

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0, 0, 0], ![85, 1, 0, 0, 0]] i)))

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0, 0, 0], ![674, 2302, 10948, -2882, 22728]] i)))

def P163P0 : CertificateIrreducibleZModOfList' 163 1 2 7 [85, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [140], [], [], [], [38], [78, 1]]]
 h' := ![![[0, 1], [162], [38], [53], [85], [30], [53], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P163P1 : CertificateIrreducibleZModOfList' 163 4 2 7 [26, 122, 53, 78, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [153, 28, 75, 114], [27, 150, 81, 71], [68, 147, 7, 141], [0, 1]]
 g := ![![[38, 8, 118, 34], [140, 160, 151, 64], [25, 85, 71], [1, 137, 126], [57], [85, 1], []], ![[3, 56, 136, 107, 133, 23], [59, 62, 76, 138, 129, 45], [46, 2, 53], [125, 85, 4], [125, 106, 93], [85, 2, 92, 40, 94, 138], [139, 157, 119]], ![[136, 50, 113, 116, 56, 150], [71, 114, 69, 38, 30, 74], [88, 131, 36], [5, 21, 6], [161, 47, 24], [99, 12, 134, 5, 41, 150], [147, 50, 151]], ![[106, 36, 81, 31, 145, 116], [123, 60, 107, 10, 102, 122], [64, 99, 62], [62, 99, 4], [33, 7, 134], [125, 123, 78, 58, 19, 78], [1, 82, 158]]]
 h' := ![![[153, 28, 75, 114], [109, 153, 150, 69], [23, 1, 137, 155], [64, 22, 126, 76], [116, 23, 124, 146], [72, 36, 100], [0, 0, 1], [0, 1]], ![[27, 150, 81, 71], [87, 12, 134, 52], [142, 70, 23, 107], [94, 112, 131, 78], [128, 61, 140, 2], [66, 106, 96, 147], [72, 79, 150, 24], [153, 28, 75, 114]], ![[68, 147, 7, 141], [113, 69, 63, 3], [109, 30, 102, 137], [21, 58, 149, 157], [92, 19, 0, 13], [140, 74, 54, 137], [4, 113, 92, 160], [27, 150, 81, 71]], ![[0, 1], [132, 92, 142, 39], [5, 62, 64, 90], [56, 134, 83, 15], [53, 60, 62, 2], [52, 110, 76, 42], [34, 134, 83, 142], [68, 147, 7, 141]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [64, 139, 76], []]
 b := ![[], [], [35, 66, 26, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A163 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 163 2 where
 D := ![[85, 1], [26, 122, 53, 78, 1]]; D' := ![[85, 1], [26, 122, 53, 78, 1]]
 heqm := by decide
 hProd := by decide
 s := ![7, 7]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P163P0
  | 1 => exact P163P1

def C1630 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A163.D 0) 163 where
  n := 1
  w := ![![163, 0, 0, 0, 0], ![85, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C1631 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A163.D 1) 163 where
  n := 4
  w := ![![163, 0, 0, 0, 0], ![674, 2302, 10948, -2882, 22728]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K163 : KummerData 163 ![I163N0, I163N1] ![163, 705911761] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A163
  C := by
    intro i
    match i with
    | 0 => exact C1630
    | 1 => exact C1631
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 163 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp167 : Fact (Nat.Prime 167) := {out := by norm_num}

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0, 0, 0], ![140, 13, 1, 0, 0]] i)))

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0, 0, 0], ![7, 30, 154, 2, 0]] i)))

def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [140, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [154, 166], [0, 1]]
 g := ![![[49, 65], [89, 65], [12, 27], [32], [93], [107, 2], [1]], ![[39, 102], [79, 102], [162, 140], [32], [93], [81, 165], [1]]]
 h' := ![![[154, 166], [65, 30], [157, 137], [30, 148], [1, 115], [50, 60], [27, 154], [0, 1]], ![[0, 1], [9, 137], [46, 30], [110, 19], [9, 52], [105, 107], [29, 13], [154, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [135, 85]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P167P1 : CertificateIrreducibleZModOfList' 167 3 2 7 [7, 29, 154, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [58, 166, 110], [122, 0, 57], [0, 1]]
 g := ![![[111, 9, 132], [90, 0, 122], [105, 158, 66], [25, 137], [31, 147], [140, 13, 1], []], ![[109, 1, 35, 105], [157, 159, 146, 109], [88, 83, 144, 140], [46, 3], [28, 22], [37, 41], [100, 76]], ![[107, 98, 106, 44], [137, 39, 113, 127], [56, 119, 164, 42], [123, 32], [5, 115], [125, 32, 75, 57], [153, 76]]]
 h' := ![![[58, 166, 110], [38, 42, 93], [100, 140, 17], [139, 101, 147], [100, 130, 114], [22, 24, 100], [0, 0, 1], [0, 1]], ![[122, 0, 57], [60, 153, 111], [68, 165, 36], [145, 51, 88], [48, 39, 105], [113, 51, 135], [159, 126], [58, 166, 110]], ![[0, 1], [30, 139, 130], [165, 29, 114], [61, 15, 99], [134, 165, 115], [154, 92, 99], [119, 41, 166], [122, 0, 57]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [83, 90], []]
 b := ![[], [157, 2, 151], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A167 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 167 2 where
 D := ![[140, 13, 1], [7, 29, 154, 1]]; D' := ![[140, 13, 1], [7, 29, 154, 1]]
 heqm := by decide
 hProd := by decide
 s := ![7, 7]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P167P0
  | 1 => exact P167P1

def C1670 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A167.D 0) 167 where
  n := 2
  w := ![![167, 0, 0, 0, 0], ![140, 13, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C1671 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A167.D 1) 167 where
  n := 3
  w := ![![167, 0, 0, 0, 0], ![7, 30, 154, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K167 : KummerData 167 ![I167N0, I167N1] ![27889, 4657463] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A167
  C := by
    intro i
    match i with
    | 0 => exact C1670
    | 1 => exact C1671
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 167 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp173 : Fact (Nat.Prime 173) := {out := by norm_num}

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0, 0, 0], ![24, 114, 1, 0, 0]] i)))

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0, 0, 0], ![37, 171, 59, 2, 0]] i)))

def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [24, 114, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [59, 172], [0, 1]]
 g := ![![[48, 137], [116], [153, 33], [152, 92], [57], [137, 21], [1]], ![[0, 36], [116], [24, 140], [44, 81], [57], [165, 152], [1]]]
 h' := ![![[59, 172], [121, 39], [134, 156], [158, 129], [17, 28], [172, 24], [149, 59], [0, 1]], ![[0, 1], [0, 134], [169, 17], [157, 44], [112, 145], [31, 149], [170, 114], [59, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [120]]
 b := ![[], [133, 60]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P173P1 : CertificateIrreducibleZModOfList' 173 3 2 7 [37, 170, 59, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [71, 131, 116], [43, 41, 57], [0, 1]]
 g := ![![[129, 80, 140], [42, 100], [75, 61, 49], [152, 113, 140], [92, 139], [24, 114, 1], []], ![[12, 89, 131, 64], [70, 31], [146, 98, 99, 138], [95, 98, 111, 4], [73, 55], [22, 138, 119, 25], [110, 135]], ![[159, 127, 103, 16], [58, 67], [25, 136, 168, 106], [59, 112, 43, 119], [27, 109], [82, 166, 125, 35], [169, 135]]]
 h' := ![![[71, 131, 116], [52, 17, 113], [166, 3, 10], [85, 112, 7], [66, 47, 113], [150, 6, 100], [0, 0, 1], [0, 1]], ![[43, 41, 57], [89, 40, 31], [55, 152, 66], [129, 127, 131], [157, 164, 51], [104, 106, 125], [106, 97, 41], [71, 131, 116]], ![[0, 1], [160, 116, 29], [24, 18, 97], [23, 107, 35], [80, 135, 9], [120, 61, 121], [94, 76, 131], [43, 41, 57]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [130, 117], []]
 b := ![[], [154, 145, 84], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A173 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 173 2 where
 D := ![[24, 114, 1], [37, 170, 59, 1]]; D' := ![[24, 114, 1], [37, 170, 59, 1]]
 heqm := by decide
 hProd := by decide
 s := ![7, 7]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P173P0
  | 1 => exact P173P1

def C1730 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A173.D 0) 173 where
  n := 2
  w := ![![173, 0, 0, 0, 0], ![24, 114, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C1731 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A173.D 1) 173 where
  n := 3
  w := ![![173, 0, 0, 0, 0], ![37, 171, 59, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K173 : KummerData 173 ![I173N0, I173N1] ![29929, 5177717] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A173
  C := by
    intro i
    match i with
    | 0 => exact C1730
    | 1 => exact C1731
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 173 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp179 : Fact (Nat.Prime 179) := {out := by norm_num}

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0, 0, 0], ![15752, 537, 179, 0, 0]] i)))

def P179P0 : CertificateIrreducibleZModOfList' 179 5 2 7 [32, 12, 79, 0, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [32, 96, 25, 106, 99], [11, 39, 55, 22, 120], [141, 6, 93, 57, 136], [174, 37, 6, 173, 3], [0, 1]]
 g := ![![[178, 78, 117, 136, 135], [119, 84, 128, 18, 142], [43, 52, 139, 85], [154, 104, 118, 138], [155], [1], []], ![[86, 84, 134, 15, 63, 118, 67, 160], [136, 142, 2, 44, 148, 56, 39, 109], [78, 149, 145, 31], [99, 23, 177, 3], [123, 164, 24, 138, 140, 129, 166, 18], [53, 82, 122, 51, 95, 157, 83, 96], [39, 76, 45, 135]], ![[136, 95, 39, 60, 72, 51, 7, 148], [45, 92, 156, 50, 101, 38, 146, 6], [112, 50, 176, 25], [55, 78, 125, 158], [53, 135, 30, 99, 30, 7, 66, 44], [105, 6, 111, 137, 62, 156, 9, 92], [90, 80, 89, 80]], ![[16, 117, 18, 25, 115, 16, 119, 26], [90, 103, 71, 106, 4, 70, 137, 130], [42, 17, 40, 61], [166, 143, 7, 65], [47, 61, 32, 88, 28, 85, 124, 94], [43, 158, 19, 88, 107, 76, 153, 50], [55, 84, 110, 59]], ![[145, 100, 159, 65, 139, 27, 103, 141], [163, 4, 12, 48, 143, 148, 74, 12], [16, 100, 79, 59], [19, 135, 37, 76], [151, 114, 19, 54, 120, 110, 2, 158], [169, 148, 135, 114, 64, 83, 5, 17], [155, 72, 143, 9]]]
 h' := ![![[32, 96, 25, 106, 99], [130, 77, 20, 153, 80], [104, 112, 4, 102, 58], [103, 65, 38, 162, 117], [52, 59, 158, 9, 106], [147, 167, 100], [0, 0, 1], [0, 1]], ![[11, 39, 55, 22, 120], [6, 170, 50, 2, 78], [29, 153, 178, 34, 151], [52, 120, 122, 156, 63], [101, 120, 32, 113, 19], [96, 153, 105, 23, 172], [134, 22, 13, 4, 121], [32, 96, 25, 106, 99]], ![[141, 6, 93, 57, 136], [158, 129, 53, 165, 143], [32, 148, 33, 166, 3], [6, 19, 36, 54, 174], [100, 83, 73, 159, 64], [133, 35, 102, 4, 31], [105, 82, 47, 17, 106], [11, 39, 55, 22, 120]], ![[174, 37, 6, 173, 3], [128, 127, 150, 41, 148], [170, 115, 0, 18, 144], [145, 154, 136, 168, 47], [96, 104, 6, 140, 94], [149, 82, 52, 16, 48], [42, 134, 26, 7, 160], [141, 6, 93, 57, 136]], ![[0, 1], [44, 34, 85, 176, 88], [77, 9, 143, 38, 2], [54, 0, 26, 176, 136], [29, 171, 89, 116, 75], [31, 100, 178, 136, 107], [77, 120, 92, 151, 150], [174, 37, 6, 173, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41, 1, 42, 83], [], [], []]
 b := ![[], [166, 39, 92, 41, 142], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A179 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 179 1 where
 D := ![[32, 12, 79, 0, 0, 1]]; D' := ![[32, 12, 79, 0, 0, 1]]
 heqm := by decide
 hProd := by decide
 s := ![7]
 n := ![5]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P179P0

def C1790 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A179.D 0) 179 where
  n := 5
  w := ![![179, 0, 0, 0, 0], ![15752, 537, 179, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K179 : KummerData 179 ![I179N0] ![183765996899] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A179
  C := by
    intro i
    match i with
    | 0 => exact C1790
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 179 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp181 : Fact (Nat.Prime 181) := {out := by norm_num}

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0, 0, 0], ![15747, 543, 181, 0, 0]] i)))

def P181P0 : CertificateIrreducibleZModOfList' 181 5 2 7 [27, 18, 81, 0, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [94, 85, 145, 27, 114], [7, 40, 43, 108, 91], [40, 63, 176, 37, 167], [40, 173, 179, 9, 171], [0, 1]]
 g := ![![[144, 164, 134, 57, 14], [70, 147, 19, 106], [130, 47, 87, 149, 119], [69, 115, 42, 38], [45], [1], []], ![[132, 160, 166, 134, 167, 5, 23, 145], [174, 104, 88, 25], [37, 88, 180, 68, 161, 108, 86, 138], [168, 15, 155, 67], [66, 35, 139, 74, 150, 51, 55, 94], [88, 6, 106, 163, 76, 148, 81, 34], [80, 123, 2, 145]], ![[48, 21, 132, 50, 67, 121, 6, 115], [68, 48, 76, 136], [23, 69, 149, 67, 105, 121, 152, 22], [10, 167, 27, 45], [93, 105, 146, 2, 78, 116, 35, 179], [122, 144, 150, 160, 107, 13, 106, 107], [122, 123, 108, 136]], ![[22, 101, 140, 17, 180, 25, 143, 36], [72, 163, 79, 87], [11, 71, 125, 98, 93, 16, 109, 12], [102, 3, 172, 12], [121, 1, 100, 176, 9, 35, 156, 142], [79, 55, 41, 55, 173, 5, 1, 172], [90, 61, 50, 15]], ![[23, 113, 160, 80, 28, 169, 20, 141], [41, 13, 132, 135], [99, 58, 115, 114, 178, 67, 38, 89], [20, 72, 29, 75], [120, 35, 158, 111, 96, 174, 94, 157], [75, 175, 141, 4, 147, 94, 49, 41], [169, 121, 1, 100]]]
 h' := ![![[94, 85, 145, 27, 114], [74, 8, 148, 4, 75], [110, 125, 108, 164, 58], [117, 80, 145, 91, 149], [52, 100, 42, 173, 20], [154, 163, 100], [0, 0, 1], [0, 1]], ![[7, 40, 43, 108, 91], [23, 20, 141, 100, 117], [14, 6, 174, 136, 176], [154, 102, 123, 22, 123], [76, 53, 19, 18, 130], [163, 161, 166, 41, 179], [160, 178, 35, 65, 111], [94, 85, 145, 27, 114]], ![[40, 63, 176, 37, 167], [76, 84, 70, 124, 7], [37, 89, 64, 76, 91], [128, 178, 143, 5, 166], [6, 119, 10, 151, 81], [61, 63, 68, 179, 38], [13, 111, 41, 52, 24], [7, 40, 43, 108, 91]], ![[40, 173, 179, 9, 171], [62, 13, 36, 62, 165], [14, 10, 109, 91, 79], [146, 127, 81, 170, 176], [179, 32, 118, 70, 115], [56, 53, 38, 142, 67], [75, 144, 166, 66, 152], [40, 63, 176, 37, 167]], ![[0, 1], [98, 56, 148, 72, 179], [149, 132, 88, 76, 139], [141, 56, 51, 74, 110], [89, 58, 173, 131, 16], [155, 103, 171, 0, 78], [114, 110, 119, 179, 75], [40, 173, 179, 9, 171]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [98, 11, 71, 64], [], [], []]
 b := ![[], [20, 43, 180, 26, 82], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A181 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 181 1 where
 D := ![[27, 18, 81, 0, 0, 1]]; D' := ![[27, 18, 81, 0, 0, 1]]
 heqm := by decide
 hProd := by decide
 s := ![7]
 n := ![5]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P181P0

def C1810 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A181.D 0) 181 where
  n := 5
  w := ![![181, 0, 0, 0, 0], ![15747, 543, 181, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K181 : KummerData 181 ![I181N0] ![194264244901] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A181
  C := by
    intro i
    match i with
    | 0 => exact C1810
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 181 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp191 : Fact (Nat.Prime 191) := {out := by norm_num}

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0, 0, 0], ![15853, 573, 191, 0, 0]] i)))

def P191P0 : CertificateIrreducibleZModOfList' 191 5 2 7 [133, 48, 91, 0, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [113, 166, 185, 146, 53], [23, 167, 140, 100, 128], [156, 155, 132, 179, 45], [90, 84, 116, 148, 156], [0, 1]]
 g := ![![[25, 101, 130, 104, 60], [22, 177, 109, 46, 109], [6, 167, 72, 29, 150], [110, 81, 179, 80, 17], [68], [1], []], ![[132, 75, 79, 154, 177, 102, 132, 173], [95, 3, 22, 121, 44, 64, 175, 140], [25, 172, 117, 171, 7, 49, 121, 14], [147, 119, 158, 6, 174, 162, 134, 145], [104, 32, 74, 159, 45, 108, 96, 105], [16, 103, 154, 114, 122, 186, 96, 155], [121, 52, 5, 135]], ![[42, 51, 121, 51, 21, 82, 121, 23], [56, 154, 59, 115, 160, 43, 136, 3], [115, 33, 164, 0, 114, 157, 66, 97], [138, 147, 39, 59, 104, 27, 150, 12], [108, 72, 103, 139, 6, 30, 95, 98], [168, 152, 175, 190, 134, 90, 25, 130], [84, 0, 6, 149]], ![[106, 116, 129, 64, 56, 32, 20, 158], [86, 130, 144, 96, 167, 110, 116, 20], [144, 63, 12, 190, 85, 27, 96, 177], [70, 128, 124, 162, 144, 85, 110, 50], [72, 38, 109, 77, 123, 15, 18, 184], [10, 39, 152, 120, 81, 34, 61, 17], [126, 182, 66, 115]], ![[121, 102, 180, 76, 4, 77, 75, 162], [59, 146, 68, 82, 58, 98, 73, 18], [12, 37, 15, 40, 30, 22, 168, 25], [35, 23, 141, 18, 170, 98, 55, 160], [179, 91, 77, 186, 59, 84, 95, 103], [78, 186, 15, 170, 78, 0, 27, 65], [66, 32, 145, 79]]]
 h' := ![![[113, 166, 185, 146, 53], [130, 52, 77, 67, 92], [157, 47, 35, 133, 49], [77, 87, 83, 141, 36], [124, 100, 86, 152, 141], [58, 143, 100], [0, 0, 1], [0, 1]], ![[23, 167, 140, 100, 128], [45, 172, 141, 93, 18], [111, 128, 1, 92, 125], [184, 141, 1, 46, 148], [3, 105, 122, 95, 8], [113, 74, 170, 20, 163], [114, 153, 186, 55, 71], [113, 166, 185, 146, 53]], ![[156, 155, 132, 179, 45], [155, 78, 41, 168, 148], [145, 56, 55, 177, 10], [102, 15, 46, 16, 97], [78, 109, 72, 153, 20], [52, 5, 42, 142, 168], [53, 21, 102, 122, 2], [23, 167, 140, 100, 128]], ![[90, 84, 116, 148, 156], [39, 5, 17, 154, 143], [175, 19, 10, 19, 128], [21, 103, 28, 45, 179], [82, 122, 7, 3, 116], [122, 120, 170, 37, 151], [129, 152, 130, 50, 174], [156, 155, 132, 179, 45]], ![[0, 1], [43, 75, 106, 91, 172], [129, 132, 90, 152, 70], [54, 36, 33, 134, 113], [143, 137, 95, 170, 97], [136, 40, 91, 183, 91], [86, 56, 154, 155, 135], [90, 84, 116, 148, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [146, 138, 156, 81], [], [], []]
 b := ![[], [31, 163, 156, 107, 121], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A191 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 191 1 where
 D := ![[133, 48, 91, 0, 0, 1]]; D' := ![[133, 48, 91, 0, 0, 1]]
 heqm := by decide
 hProd := by decide
 s := ![7]
 n := ![5]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P191P0

def C1910 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A191.D 0) 191 where
  n := 5
  w := ![![191, 0, 0, 0, 0], ![15853, 573, 191, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K191 : KummerData 191 ![I191N0] ![254194901951] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A191
  C := by
    intro i
    match i with
    | 0 => exact C1910
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 191 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp193 : Fact (Nat.Prime 193) := {out := by norm_num}

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0, 0, 0], ![10, 167, 1, 0, 0]] i)))

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0, 0, 0], ![165, 88, 26, 2, 0]] i)))

def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [10, 167, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [26, 192], [0, 1]]
 g := ![![[36, 75], [14], [134], [162], [85], [42], [26, 1]], ![[56, 118], [14], [134], [162], [85], [42], [52, 192]]]
 h' := ![![[26, 192], [149, 70], [17, 173], [149, 110], [178, 111], [16, 49], [126, 87], [0, 1]], ![[0, 1], [39, 123], [76, 20], [114, 83], [169, 82], [132, 144], [72, 106], [26, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [176]]
 b := ![[], [14, 88]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P193P1 : CertificateIrreducibleZModOfList' 193 3 2 7 [165, 87, 26, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [64, 164, 158], [103, 28, 35], [0, 1]]
 g := ![![[85, 8, 108], [55, 143], [90, 84], [72, 59], [83, 181], [72, 97], [1]], ![[8, 60, 155, 188], [114, 110], [106, 108], [50, 166], [153, 131], [101, 1], [20, 167, 136, 164]], ![[120, 64, 27, 159], [34, 112], [100, 190], [6, 8], [14, 128], [172, 46], [127, 24, 49, 29]]]
 h' := ![![[64, 164, 158], [192, 173, 84], [14, 103, 23], [179, 166, 108], [155, 186, 161], [98, 72, 48], [28, 106, 167], [0, 1]], ![[103, 28, 35], [154, 138, 157], [67, 150, 127], [103, 132, 109], [61, 160, 121], [122, 3, 175], [31, 160, 1], [64, 164, 158]], ![[0, 1], [72, 75, 145], [144, 133, 43], [168, 88, 169], [0, 40, 104], [103, 118, 163], [43, 120, 25], [103, 28, 35]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [143, 44], []]
 b := ![[], [144, 16, 95], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A193 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 193 2 where
 D := ![[10, 167, 1], [165, 87, 26, 1]]; D' := ![[10, 167, 1], [165, 87, 26, 1]]
 heqm := by decide
 hProd := by decide
 s := ![7, 7]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P193P0
  | 1 => exact P193P1

def C1930 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A193.D 0) 193 where
  n := 2
  w := ![![193, 0, 0, 0, 0], ![10, 167, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C1931 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A193.D 1) 193 where
  n := 3
  w := ![![193, 0, 0, 0, 0], ![165, 88, 26, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K193 : KummerData 193 ![I193N0, I193N1] ![37249, 7189057] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A193
  C := by
    intro i
    match i with
    | 0 => exact C1930
    | 1 => exact C1931
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 193 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0, 0, 0], ![50, 1, 0, 0, 0]] i)))

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0, 0, 0], ![767, 2441, 11031, -2744, 22728]] i)))

def P197P0 : CertificateIrreducibleZModOfList' 197 1 2 7 [50, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [150], [], [], [], [136, 147, 1]]]
 h' := ![![[0, 1], [196], [183], [100], [187], [160], [95], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P197P1 : CertificateIrreducibleZModOfList' 197 4 2 7 [119, 192, 136, 147, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [143, 178, 158, 80], [147, 188, 46, 180], [154, 27, 190, 134], [0, 1]]
 g := ![![[166, 93, 144, 160], [133, 32, 43], [160, 31, 157, 83], [61, 34, 196], [49, 13, 150], [0, 50, 1], []], ![[105, 46, 140, 14, 83, 18], [56, 163, 143], [153, 108, 124, 42, 105, 128], [177, 182, 150], [178, 116, 173], [95, 142, 164], [67, 146, 161, 90, 44, 194]], ![[150, 124, 100, 26, 70, 185], [16, 80, 160], [145, 187, 98, 1, 131, 13], [145, 156, 26], [142, 140, 10], [48, 84, 37], [138, 177, 36, 183, 97, 12]], ![[86, 95, 70, 52, 51, 92], [178, 161, 64], [146, 99, 94, 181, 139, 174], [128, 191, 1], [140, 173, 15], [179, 31, 155], [175, 105, 38, 68, 40, 143]]]
 h' := ![![[143, 178, 158, 80], [163, 26, 81, 95], [69, 170, 178, 35], [164, 151, 169, 110], [79, 77, 3, 14], [0, 157, 131, 100], [0, 0, 0, 1], [0, 1]], ![[147, 188, 46, 180], [170, 190, 64, 58], [50, 132, 37, 52], [184, 105, 112, 108], [94, 88, 56, 100], [0, 145, 53, 31], [43, 156, 98, 178], [143, 178, 158, 80]], ![[154, 27, 190, 134], [95, 11, 51, 156], [63, 161, 135, 102], [157, 86, 192, 172], [43, 142, 166, 82], [183, 157, 132, 124], [24, 186, 14, 148], [147, 188, 46, 180]], ![[0, 1], [133, 167, 1, 85], [32, 128, 44, 8], [175, 52, 118, 4], [108, 87, 169, 1], [107, 132, 78, 139], [138, 52, 85, 67], [154, 27, 190, 134]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [36, 109, 109], []]
 b := ![[], [], [129, 100, 59, 18], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A197 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 197 2 where
 D := ![[50, 1], [119, 192, 136, 147, 1]]; D' := ![[50, 1], [119, 192, 136, 147, 1]]
 heqm := by decide
 hProd := by decide
 s := ![7, 7]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P197P0
  | 1 => exact P197P1

def C1970 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A197.D 0) 197 where
  n := 1
  w := ![![197, 0, 0, 0, 0], ![50, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C1971 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A197.D 1) 197 where
  n := 4
  w := ![![197, 0, 0, 0, 0], ![767, 2441, 11031, -2744, 22728]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K197 : KummerData 197 ![I197N0, I197N1] ![197, 1506138481] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A197
  C := by
    intro i
    match i with
    | 0 => exact C1970
    | 1 => exact C1971
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 197 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


lemma PB18792I4_primes (p : ℕ) :
  p ∈ Set.range ![157, 163, 167, 173, 179, 181, 191, 193, 197] ↔ Nat.Prime p ∧ 151 < p ∧ p ≤ 197 := by
  rw [← List.mem_ofFn']
  convert primes_range 151 197 (by omega)
  decide

def PB18792I4 : PrimesBelowBoundCertificateInterval O 151 197 18792 where
  m := 9
  g := ![2, 2, 2, 2, 1, 1, 1, 2, 2]
  P := ![157, 163, 167, 173, 179, 181, 191, 193, 197]
  hP := PB18792I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1]
    · exact ![I173N0, I173N1]
    · exact ![I179N0]
    · exact ![I181N0]
    · exact ![I191N0]
    · exact ![I193N0, I193N1]
    · exact ![I197N0, I197N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · convert (containsPrimesAbove_of_KummerData K157) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K163) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K167) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K173) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K179) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K181) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K191) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K193) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K197) <;> rfl
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![157, 607573201]
    · exact ![163, 705911761]
    · exact ![27889, 4657463]
    · exact ![29929, 5177717]
    · exact ![183765996899]
    · exact ![194264244901]
    · exact ![254194901951]
    · exact ![37249, 7189057]
    · exact ![197, 1506138481]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact (card_quot_of_KummerData K157)
    · exact (card_quot_of_KummerData K163)
    · exact (card_quot_of_KummerData K167)
    · exact (card_quot_of_KummerData K173)
    · exact (card_quot_of_KummerData K179)
    · exact (card_quot_of_KummerData K181)
    · exact (card_quot_of_KummerData K191)
    · exact (card_quot_of_KummerData K193)
    · exact (card_quot_of_KummerData K197)
  β := ![I157N0, I163N0, I197N0]
  Il := ![[I157N0], [I163N0], [], [], [], [], [], [], [I197N0]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
