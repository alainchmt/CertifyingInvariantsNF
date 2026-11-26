
import IdealArithmetic.Examples.NF5_1_281250000_1_K.RI5_1_281250000_1_K
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 

instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0, 0, 0], ![54, 1, 0, 0, 0]] i)))

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0, 0, 0], ![66, 1, 0, 0, 0]] i)))

def I157N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0, 0, 0], ![117, 1, 0, 0, 0]] i)))

def I157N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0, 0, 0], ![75, 77, 1, 0, 0]] i)))

def P157P0 : CertificateIrreducibleZModOfList' 157 1 2 7 [54, 1] where
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
 g := ![![[], [], [111], [56], [14], [], [103, 1]]]
 h' := ![![[0, 1], [156], [129], [116], [29], [93], [90], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P157P1 : CertificateIrreducibleZModOfList' 157 1 2 7 [66, 1] where
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
 g := ![![[], [], [48], [90], [115], [], [91, 1]]]
 h' := ![![[0, 1], [156], [129], [26], [103], [30], [117], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P157P2 : CertificateIrreducibleZModOfList' 157 1 2 7 [117, 1] where
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
 g := ![![[], [], [106], [93], [37], [], [40, 1]]]
 h' := ![![[0, 1], [1], [1], [109], [67], [115], [30], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P157P3 : CertificateIrreducibleZModOfList' 157 2 2 7 [75, 77, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [80, 156], [0, 1]]
 g := ![![[135, 67], [126], [26, 27], [118, 113], [88, 141], [120], [1]], ![[0, 90], [126], [145, 130], [52, 44], [64, 16], [120], [1]]]
 h' := ![![[80, 156], [87, 99], [91, 122], [99, 59], [151, 37], [79, 112], [82, 80], [0, 1]], ![[0, 1], [0, 58], [117, 35], [109, 98], [128, 120], [90, 45], [45, 77], [80, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [17, 82]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A157 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 157 4 where
 D := ![[54, 1], [66, 1], [117, 1], [75, 77, 1]]; D' := ![[54, 1], [66, 1], [117, 1], [75, 77, 1]]
 heqm := by decide
 hProd := by decide
 s := ![7, 7, 7, 7]
 n := ![1, 1, 1, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P157P0
  | 1 => exact P157P1
  | 2 => exact P157P2
  | 3 => exact P157P3

def C1570 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A157.D 0) 157 where
  n := 1
  w := ![![157, 0, 0, 0, 0], ![54, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C1571 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A157.D 1) 157 where
  n := 1
  w := ![![157, 0, 0, 0, 0], ![66, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C1572 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A157.D 2) 157 where
  n := 1
  w := ![![157, 0, 0, 0, 0], ![117, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C1573 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A157.D 3) 157 where
  n := 2
  w := ![![157, 0, 0, 0, 0], ![75, 77, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K157 : KummerData 157 ![I157N0, I157N1, I157N2, I157N3] ![157, 157, 157, 24649] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A157
  C := by
    intro i
    match i with
    | 0 => exact C1570
    | 1 => exact C1571
    | 2 => exact C1572
    | 3 => exact C1573
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 157 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp163 : Fact (Nat.Prime 163) := {out := by norm_num}

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0, 0, 0], ![121, 27, 1, 0, 0]] i)))

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0, 0, 0], ![77, 94, 136, 5, 0]] i)))

def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [121, 27, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [136, 162], [0, 1]]
 g := ![![[11, 97], [1, 54], [9], [150], [160], [54, 77], [1]], ![[0, 66], [10, 109], [9], [150], [160], [94, 86], [1]]]
 h' := ![![[136, 162], [42, 74], [142, 39], [116, 160], [70, 65], [149, 117], [42, 136], [0, 1]], ![[0, 1], [0, 89], [67, 124], [34, 3], [108, 98], [87, 46], [119, 27], [136, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [155]]
 b := ![[], [109, 159]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P163P1 : CertificateIrreducibleZModOfList' 163 3 2 7 [77, 94, 136, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [79, 10, 66], [111, 152, 97], [0, 1]]
 g := ![![[90, 77, 60], [156, 10, 4], [146, 60], [96, 88], [144, 40], [146, 27, 1], []], ![[106, 87, 73, 52], [9, 106, 108, 130], [132, 118], [52, 36], [42, 156], [40, 162, 39, 162], [105, 118]], ![[46, 51, 26, 144], [55, 111, 35, 26], [153, 26], [125, 113], [2, 132], [126, 63, 62, 83], [74, 118]]]
 h' := ![![[79, 10, 66], [50, 33, 68], [109, 57, 2], [58, 42, 95], [21, 90, 96], [5, 8, 23], [0, 0, 1], [0, 1]], ![[111, 152, 97], [4, 23, 126], [109, 48, 154], [161, 75, 97], [116, 131, 157], [116, 108, 112], [112, 65, 152], [79, 10, 66]], ![[0, 1], [122, 107, 132], [122, 58, 7], [161, 46, 134], [13, 105, 73], [2, 47, 28], [103, 98, 10], [111, 152, 97]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [115, 125], []]
 b := ![[], [86, 138, 129], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A163 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 163 2 where
 D := ![[121, 27, 1], [77, 94, 136, 1]]; D' := ![[121, 27, 1], [77, 94, 136, 1]]
 heqm := by decide
 hProd := by decide
 s := ![7, 7]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P163P0
  | 1 => exact P163P1

def C1630 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A163.D 0) 163 where
  n := 2
  w := ![![163, 0, 0, 0, 0], ![121, 27, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C1631 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A163.D 1) 163 where
  n := 3
  w := ![![163, 0, 0, 0, 0], ![77, 94, 136, 5, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K163 : KummerData 163 ![I163N0, I163N1] ![26569, 4330747] where
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0, 0, 0], ![43, 1, 0, 0, 0]] i)))

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0, 0, 0], ![94, 58, 159, 620, 10]] i)))

def P167P0 : CertificateIrreducibleZModOfList' 167 1 2 7 [43, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [66], [16], [], [], [144], [124, 1]]]
 h' := ![![[0, 1], [1], [147], [4], [2], [154], [12], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P167P1 : CertificateIrreducibleZModOfList' 167 4 2 7 [94, 58, 154, 124, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [77, 83, 22, 134], [146, 152, 3, 55], [154, 98, 142, 145], [0, 1]]
 g := ![![[104, 134, 57, 97], [17, 45, 101, 107], [59, 81, 98, 8], [76, 18, 84], [119, 155, 124], [43, 1], []], ![[40, 137, 105, 133, 85, 79], [153, 141, 107, 59, 121, 51], [123, 135, 76, 80, 43, 53], [23, 133, 126], [101, 17, 57], [80, 93, 11, 131, 149, 80], [42, 118, 87]], ![[3, 15, 43, 123, 28, 74], [135, 11, 6, 7, 62, 109], [140, 128, 137, 22, 2, 101], [138, 3, 27], [154, 136, 65], [20, 5, 153, 50, 82, 109], [165, 145, 19]], ![[2, 26, 27, 138], [102, 91, 104, 10, 37, 163], [52, 79, 62, 10, 75, 23], [31, 6, 61], [76, 40, 94], [74, 48, 121, 115, 127, 149], [102, 35, 150]]]
 h' := ![![[77, 83, 22, 134], [72, 17, 78, 40], [132, 51, 131, 146], [137, 7, 143, 26], [157, 37, 148, 77], [133, 84, 0, 25], [0, 0, 1], [0, 1]], ![[146, 152, 3, 55], [149, 72, 97, 92], [108, 20, 84, 82], [107, 68, 55, 160], [91, 14, 61, 136], [147, 22, 152, 70], [144, 89, 143, 37], [77, 83, 22, 134]], ![[154, 98, 142, 145], [112, 55, 2, 35], [150, 34, 149, 33], [147, 127, 43, 44], [107, 12, 92, 148], [80, 69, 3, 30], [128, 142, 64, 134], [146, 152, 3, 55]], ![[0, 1], [75, 23, 157], [147, 62, 137, 73], [103, 132, 93, 104], [126, 104, 33, 140], [151, 159, 12, 42], [100, 103, 126, 163], [154, 98, 142, 145]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [110, 130, 40], []]
 b := ![[], [], [47, 166, 56, 60], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A167 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 167 2 where
 D := ![[43, 1], [94, 58, 154, 124, 1]]; D' := ![[43, 1], [94, 58, 154, 124, 1]]
 heqm := by decide
 hProd := by decide
 s := ![7, 7]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P167P0
  | 1 => exact P167P1

def C1670 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A167.D 0) 167 where
  n := 1
  w := ![![167, 0, 0, 0, 0], ![43, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C1671 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A167.D 1) 167 where
  n := 4
  w := ![![167, 0, 0, 0, 0], ![94, 58, 159, 620, 10]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K167 : KummerData 167 ![I167N0, I167N1] ![167, 777796321] where
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0, 0, 0], ![125, 41, 1, 0, 0]] i)))

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0, 0, 0], ![136, 147, 132, 5, 0]] i)))

def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [125, 41, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [132, 172], [0, 1]]
 g := ![![[46, 64], [21], [27, 95], [148, 122], [24], [149, 124], [1]], ![[17, 109], [21], [111, 78], [163, 51], [24], [82, 49], [1]]]
 h' := ![![[132, 172], [102, 8], [85, 114], [11, 21], [135, 128], [59, 71], [48, 132], [0, 1]], ![[0, 1], [120, 165], [82, 59], [15, 152], [77, 45], [89, 102], [172, 41], [132, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [127]]
 b := ![[], [134, 150]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P173P1 : CertificateIrreducibleZModOfList' 173 3 2 7 [136, 147, 132, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [89, 135, 98], [125, 37, 75], [0, 1]]
 g := ![![[138, 156, 54], [6, 43], [80, 68, 158], [73, 95, 13], [162, 169], [150, 41, 1], []], ![[58, 37, 19, 70], [116, 57], [34, 36, 86, 170], [122, 102, 138, 42], [2, 51], [42, 43, 13, 87], [7, 89]], ![[166, 143, 109, 20], [169, 117], [159, 92, 84, 161], [14, 57, 114, 134], [30, 40], [148, 54, 71, 2], [30, 89]]]
 h' := ![![[89, 135, 98], [64, 112, 153], [19, 89, 133], [106, 110, 136], [135, 40, 94], [14, 54, 160], [0, 0, 1], [0, 1]], ![[125, 37, 75], [56, 109, 29], [98, 158, 149], [125, 46, 69], [170, 22, 132], [31, 50, 140], [49, 171, 37], [89, 135, 98]], ![[0, 1], [106, 125, 164], [9, 99, 64], [161, 17, 141], [119, 111, 120], [96, 69, 46], [127, 2, 135], [125, 37, 75]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [79, 152], []]
 b := ![[], [97, 121, 62], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A173 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 173 2 where
 D := ![[125, 41, 1], [136, 147, 132, 1]]; D' := ![[125, 41, 1], [136, 147, 132, 1]]
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
  w := ![![173, 0, 0, 0, 0], ![125, 41, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C1731 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A173.D 1) 173 where
  n := 3
  w := ![![173, 0, 0, 0, 0], ![136, 147, 132, 5, 0]]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0, 0, 0], ![358, -179, 0, 895, 0]] i)))

def P179P0 : CertificateIrreducibleZModOfList' 179 5 2 7 [58, 71, 0, 154, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [168, 8, 90, 129, 129], [130, 139, 159, 151, 73], [21, 35, 122, 100, 79], [39, 175, 166, 157, 77], [0, 1]]
 g := ![![[65, 86, 94, 6, 124], [4, 145, 105, 109, 89], [124, 0, 36, 68], [159, 56, 164, 43], [82, 0, 88], [1], []], ![[111, 7, 157, 88, 12, 81, 125, 31], [168, 90, 47, 130, 161, 178, 119, 172], [88, 79, 26, 125], [59, 176, 22, 60], [89, 85, 56, 20, 134, 28, 107, 56], [162, 147, 81, 76, 99, 55, 24, 125], [103, 152, 167, 173]], ![[83, 158, 116, 165, 86, 149, 137, 109], [19, 172, 87, 106, 177, 12, 132, 63], [103, 165, 148, 29], [39, 38, 57, 60], [127, 115, 89, 111, 155, 21, 1, 2], [151, 126, 175, 2, 102, 144, 70, 33], [122, 61, 29, 138]], ![[67, 3, 24, 125, 56, 111, 33, 111], [95, 24, 20, 32, 91, 59, 87, 10], [166, 39, 106, 61], [127, 46, 29, 88], [36, 146, 176, 28, 117, 86, 129, 127], [89, 25, 11, 7, 135, 106, 151, 41], [163, 36, 48, 155]], ![[165, 95, 43, 75, 65, 33, 35, 142], [158, 10, 111, 133, 124, 110, 135, 74], [14, 8, 49, 88], [122, 92, 0, 43], [135, 94, 64, 70, 73, 90, 157, 29], [53, 44, 122, 12, 128, 148, 122, 121], [102, 106, 13, 22]]]
 h' := ![![[168, 8, 90, 129, 129], [126, 86, 173, 81, 126], [176, 164, 161, 134, 140], [108, 15, 16, 39, 28], [77, 48, 89, 127, 143], [121, 108, 0, 25], [0, 0, 1], [0, 1]], ![[130, 139, 159, 151, 73], [149, 74, 80, 178, 26], [16, 23, 38, 65, 132], [114, 174, 14, 123, 150], [80, 81, 6, 149, 113], [56, 112, 131, 8, 172], [54, 163, 160, 50, 96], [168, 8, 90, 129, 129]], ![[21, 35, 122, 100, 79], [139, 81, 13, 100, 147], [148, 19, 20, 176, 90], [173, 113, 57, 4, 108], [65, 130, 97, 85, 113], [63, 154, 76, 87, 122], [158, 133, 53, 16, 101], [130, 139, 159, 151, 73]], ![[39, 175, 166, 157, 77], [159, 167, 44, 123, 33], [65, 17, 78, 43, 55], [122, 120, 27, 123, 47], [68, 46, 125, 176, 25], [143, 93, 168, 162, 102], [116, 160, 114, 121, 61], [21, 35, 122, 100, 79]], ![[0, 1], [111, 129, 48, 55, 26], [28, 135, 61, 119, 120], [126, 115, 65, 69, 25], [20, 53, 41, 0, 143], [43, 70, 162, 76, 141], [80, 81, 30, 171, 100], [39, 175, 166, 157, 77]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56, 131, 17, 84], [], [], []]
 b := ![[], [165, 132, 91, 81, 16], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A179 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 179 1 where
 D := ![[58, 71, 0, 154, 0, 1]]; D' := ![[58, 71, 0, 154, 0, 1]]
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
  w := ![![179, 0, 0, 0, 0], ![358, -179, 0, 895, 0]]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0, 0, 0], ![4, 1, 0, 0, 0]] i)))

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0, 0, 0], ![36, 63, 1, 0, 0]] i)))

def I181N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0, 0, 0], ![13, 114, 1, 0, 0]] i)))

def P181P0 : CertificateIrreducibleZModOfList' 181 1 2 7 [4, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [45], [], [43], [75], [177, 1]]]
 h' := ![![[0, 1], [1], [1], [81], [9], [62], [16], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P181P1 : CertificateIrreducibleZModOfList' 181 2 2 7 [36, 63, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [118, 180], [0, 1]]
 g := ![![[47, 176], [42], [18, 25], [64], [133, 5], [106, 168], [1]], ![[0, 5], [42], [72, 156], [64], [180, 176], [20, 13], [1]]]
 h' := ![![[118, 180], [101, 151], [76, 122], [76, 176], [99, 173], [166, 154], [145, 118], [0, 1]], ![[0, 1], [0, 30], [173, 59], [29, 5], [60, 8], [57, 27], [132, 63], [118, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [20, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P181P2 : CertificateIrreducibleZModOfList' 181 2 2 7 [13, 114, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [67, 180], [0, 1]]
 g := ![![[148, 14], [125], [122, 145], [9], [137, 5], [9, 145], [1]], ![[0, 167], [125], [63, 36], [9], [110, 176], [131, 36], [1]]]
 h' := ![![[67, 180], [43, 75], [43, 135], [0, 67], [29, 178], [64, 154], [168, 67], [0, 1]], ![[0, 1], [0, 106], [38, 46], [145, 114], [9, 3], [65, 27], [132, 114], [67, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [107]]
 b := ![[], [63, 144]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A181 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 181 3 where
 D := ![[4, 1], [36, 63, 1], [13, 114, 1]]; D' := ![[4, 1], [36, 63, 1], [13, 114, 1]]
 heqm := by decide
 hProd := by decide
 s := ![7, 7, 7]
 n := ![1, 2, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P181P0
  | 1 => exact P181P1
  | 2 => exact P181P2

def C1810 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A181.D 0) 181 where
  n := 1
  w := ![![181, 0, 0, 0, 0], ![4, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C1811 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A181.D 1) 181 where
  n := 2
  w := ![![181, 0, 0, 0, 0], ![36, 63, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C1812 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A181.D 2) 181 where
  n := 2
  w := ![![181, 0, 0, 0, 0], ![13, 114, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K181 : KummerData 181 ![I181N0, I181N1, I181N2] ![181, 32761, 32761] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A181
  C := by
    intro i
    match i with
    | 0 => exact C1810
    | 1 => exact C1811
    | 2 => exact C1812
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 181 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp191 : Fact (Nat.Prime 191) := {out := by norm_num}

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0, 0, 0], ![79, 1, 0, 0, 0]] i)))

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0, 0, 0], ![137, 1, 0, 0, 0]] i)))

def I191N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0, 0, 0], ![136, 91, 166, 5, 0]] i)))

def P191P0 : CertificateIrreducibleZModOfList' 191 1 2 7 [79, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [162], [170], [169], [5], [24], [112, 1]]]
 h' := ![![[0, 1], [190], [131], [19], [178], [14], [129], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P191P1 : CertificateIrreducibleZModOfList' 191 1 2 7 [137, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [46], [133], [64], [177], [118], [54, 1]]]
 h' := ![![[0, 1], [1], [115], [18], [8], [69], [51], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P191P2 : CertificateIrreducibleZModOfList' 191 3 2 7 [136, 91, 166, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 143, 69], [1, 47, 122], [0, 1]]
 g := ![![[56, 81, 121], [62, 152, 125], [87, 93, 24], [14, 187, 96], [81, 11, 30], [152, 25, 1], []], ![[145, 91, 60, 160], [85, 28, 68, 109], [27, 96, 155, 51], [4, 2, 180, 26], [95, 168, 133, 144], [145, 105, 91, 3], [93, 177]], ![[154, 38, 80, 139], [84, 86, 100, 113], [149, 190, 175, 173], [88, 63, 45, 190], [130, 12, 159, 95], [123, 69, 188, 127], [40, 177]]]
 h' := ![![[24, 143, 69], [163, 144, 11], [10, 99, 121], [6, 58, 129], [62, 136, 67], [147, 149, 52], [0, 0, 1], [0, 1]], ![[1, 47, 122], [134, 72, 139], [150, 65, 103], [187, 80, 133], [140, 155, 118], [167, 113, 119], [152, 114, 47], [24, 143, 69]], ![[0, 1], [70, 166, 41], [176, 27, 158], [167, 53, 120], [22, 91, 6], [148, 120, 20], [100, 77, 143], [1, 47, 122]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [154, 53], []]
 b := ![[], [154, 35, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A191 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 191 3 where
 D := ![[79, 1], [137, 1], [136, 91, 166, 1]]; D' := ![[79, 1], [137, 1], [136, 91, 166, 1]]
 heqm := by decide
 hProd := by decide
 s := ![7, 7, 7]
 n := ![1, 1, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P191P0
  | 1 => exact P191P1
  | 2 => exact P191P2

def C1910 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A191.D 0) 191 where
  n := 1
  w := ![![191, 0, 0, 0, 0], ![79, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C1911 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A191.D 1) 191 where
  n := 1
  w := ![![191, 0, 0, 0, 0], ![137, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C1912 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A191.D 2) 191 where
  n := 3
  w := ![![191, 0, 0, 0, 0], ![136, 91, 166, 5, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K191 : KummerData 191 ![I191N0, I191N1, I191N2] ![191, 191, 6967871] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A191
  C := by
    intro i
    match i with
    | 0 => exact C1910
    | 1 => exact C1911
    | 2 => exact C1912
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 191 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp193 : Fact (Nat.Prime 193) := {out := by norm_num}

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0, 0, 0], ![54, 1, 0, 0, 0]] i)))

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0, 0, 0], ![159, 1, 0, 0, 0]] i)))

def I193N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0, 0, 0], ![183, 1, 0, 0, 0]] i)))

def I193N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0, 0, 0], ![181, 183, 1, 0, 0]] i)))

def P193P0 : CertificateIrreducibleZModOfList' 193 1 2 7 [54, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [], [], [], [21, 139, 1]]]
 h' := ![![[0, 1], [1], [192], [81], [9], [190], [24], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P193P1 : CertificateIrreducibleZModOfList' 193 1 2 7 [159, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [], [], [], [191, 34, 1]]]
 h' := ![![[0, 1], [192], [112], [43], [64], [185], [125], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P193P2 : CertificateIrreducibleZModOfList' 193 1 2 7 [183, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [], [], [], [100, 10, 1]]]
 h' := ![![[0, 1], [192], [81], [184], [50], [67], [35], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P193P3 : CertificateIrreducibleZModOfList' 193 2 2 7 [181, 183, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [10, 192], [0, 1]]
 g := ![![[33, 16], [175], [32], [49], [112], [192], [10, 1]], ![[0, 177], [175], [32], [49], [112], [192], [20, 192]]]
 h' := ![![[10, 192], [40, 189], [177, 91], [76, 15], [35, 7], [106, 43], [120, 112], [0, 1]], ![[0, 1], [0, 4], [122, 102], [33, 178], [105, 186], [150, 150], [82, 81], [10, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [73]]
 b := ![[], [107, 133]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A193 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 193 4 where
 D := ![[54, 1], [159, 1], [183, 1], [181, 183, 1]]; D' := ![[54, 1], [159, 1], [183, 1], [181, 183, 1]]
 heqm := by decide
 hProd := by decide
 s := ![7, 7, 7, 7]
 n := ![1, 1, 1, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P193P0
  | 1 => exact P193P1
  | 2 => exact P193P2
  | 3 => exact P193P3

def C1930 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A193.D 0) 193 where
  n := 1
  w := ![![193, 0, 0, 0, 0], ![54, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C1931 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A193.D 1) 193 where
  n := 1
  w := ![![193, 0, 0, 0, 0], ![159, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C1932 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A193.D 2) 193 where
  n := 1
  w := ![![193, 0, 0, 0, 0], ![183, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C1933 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A193.D 3) 193 where
  n := 2
  w := ![![193, 0, 0, 0, 0], ![181, 183, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K193 : KummerData 193 ![I193N0, I193N1, I193N2, I193N3] ![193, 193, 193, 37249] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A193
  C := by
    intro i
    match i with
    | 0 => exact C1930
    | 1 => exact C1931
    | 2 => exact C1932
    | 3 => exact C1933
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 193 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0, 0, 0], ![62, 1, 0, 0, 0]] i)))

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0, 0, 0], ![46, 16, 81, 675, 10]] i)))

def P197P0 : CertificateIrreducibleZModOfList' 197 1 2 7 [62, 1] where
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
 g := ![![[], [], [54], [], [], [], [101, 135, 1]]]
 h' := ![![[0, 1], [1], [1], [60], [81], [188], [42], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P197P1 : CertificateIrreducibleZModOfList' 197 4 2 7 [46, 16, 76, 135, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [152, 180, 63, 160], [109, 154, 92, 87], [195, 59, 42, 147], [0, 1]]
 g := ![![[168, 106, 77, 164], [88, 0, 193], [26, 55, 121, 16], [37, 60, 174], [86, 52, 85], [25, 62, 1], []], ![[38, 190, 195, 78, 187, 23], [124, 118, 116], [170, 90, 193, 162, 14, 34], [115, 110, 92], [68, 154, 36], [137, 6, 146], [107, 181, 154, 75, 168, 173]], ![[57, 192, 170, 82, 129, 165], [95, 149, 81], [77, 188, 36, 109, 2, 194], [24], [84, 119, 158], [51, 121, 132], [129, 19, 94, 73, 174, 129]], ![[100, 196, 80, 164, 158, 189], [160, 162, 171], [75, 82, 107, 166, 37, 123], [89, 93, 175], [5, 60, 90], [74, 101, 178], [121, 93, 49, 31, 174, 95]]]
 h' := ![![[152, 180, 63, 160], [88, 12, 144, 19], [183, 90, 80, 169], [9, 144, 35, 193], [23, 76, 7, 78], [32, 97, 17, 171], [0, 0, 0, 1], [0, 1]], ![[109, 154, 92, 87], [24, 139, 2, 82], [58, 60, 14, 71], [179, 175, 185, 176], [100, 60, 95, 180], [43, 27, 9, 191], [89, 159, 154, 151], [152, 180, 63, 160]], ![[195, 59, 42, 147], [139, 60, 36, 57], [136, 186, 19, 188], [140, 49, 152, 153], [72, 29, 157], [28, 168, 153, 54], [124, 28, 70, 138], [109, 154, 92, 87]], ![[0, 1], [189, 183, 15, 39], [76, 58, 84, 163], [124, 26, 22, 69], [188, 32, 135, 136], [157, 102, 18, 175], [139, 10, 170, 104], [195, 59, 42, 147]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [87, 47, 74], []]
 b := ![[], [], [88, 171, 102, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A197 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 197 2 where
 D := ![[62, 1], [46, 16, 76, 135, 1]]; D' := ![[62, 1], [46, 16, 76, 135, 1]]
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
  w := ![![197, 0, 0, 0, 0], ![62, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C1971 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A197.D 1) 197 where
  n := 4
  w := ![![197, 0, 0, 0, 0], ![46, 16, 81, 675, 10]]
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


lemma PB1045I4_primes (p : ℕ) :
  p ∈ Set.range ![157, 163, 167, 173, 179, 181, 191, 193, 197] ↔ Nat.Prime p ∧ 151 < p ∧ p ≤ 197 := by
  rw [← List.mem_ofFn']
  convert primes_range 151 197 (by omega)
  decide

def PB1045I4 : PrimesBelowBoundCertificateInterval O 151 197 1045 where
  m := 9
  g := ![4, 2, 2, 2, 1, 3, 3, 4, 2]
  P := ![157, 163, 167, 173, 179, 181, 191, 193, 197]
  hP := PB1045I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I157N0, I157N1, I157N2, I157N3]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1]
    · exact ![I173N0, I173N1]
    · exact ![I179N0]
    · exact ![I181N0, I181N1, I181N2]
    · exact ![I191N0, I191N1, I191N2]
    · exact ![I193N0, I193N1, I193N2, I193N3]
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
    · exact ![157, 157, 157, 24649]
    · exact ![26569, 4330747]
    · exact ![167, 777796321]
    · exact ![29929, 5177717]
    · exact ![183765996899]
    · exact ![181, 32761, 32761]
    · exact ![191, 191, 6967871]
    · exact ![193, 193, 193, 37249]
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
  β := ![I157N0, I157N1, I157N2, I167N0, I181N0, I191N0, I191N1, I193N0, I193N1, I193N2, I197N0]
  Il := ![[I157N0, I157N1, I157N2], [], [I167N0], [], [], [I181N0], [I191N0, I191N1], [I193N0, I193N1, I193N2], [I197N0]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
