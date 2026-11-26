
import IdealArithmetic.Examples.NF5_1_91125000000_1_K.RI5_1_91125000000_1_K
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 

instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0, 0, 0], ![64, 1, 0, 0, 0]] i)))

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0, 0, 0], ![71, 1, 0, 0, 0]] i)))

def I199N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0, 0, 0], ![6, 150, 64, 2, 0]] i)))

def P199P0 : CertificateIrreducibleZModOfList' 199 1 2 7 [64, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [28], [103], [], [], [], [116, 135, 1]]]
 h' := ![![[0, 1], [198], [174], [125], [18], [139], [138], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P199P1 : CertificateIrreducibleZModOfList' 199 1 2 7 [71, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [14], [117], [], [], [], [66, 128, 1]]]
 h' := ![![[0, 1], [1], [51], [52], [98], [140], [90], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P199P2 : CertificateIrreducibleZModOfList' 199 3 2 7 [6, 149, 64, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [107, 153, 50], [28, 45, 149], [0, 1]]
 g := ![![[148, 122, 46], [149, 144, 161], [70, 7, 9], [124, 86], [80, 70], [106, 116], [1]], ![[55, 155, 71, 47], [105, 185, 116, 5], [185, 18, 90, 178], [22, 47], [176, 56], [190, 125], [11, 153, 65, 28]], ![[41, 131, 139, 83], [187, 56, 158, 107], [67, 136, 40, 41], [44, 126], [23, 4], [37, 126], [152, 164, 196, 171]]]
 h' := ![![[107, 153, 50], [101, 105, 134], [177, 139, 165], [8, 135, 196], [126, 53, 177], [196, 24, 95], [193, 50, 135], [0, 1]], ![[28, 45, 149], [85, 111, 136], [167, 45, 47], [117, 135, 48], [100, 113, 68], [165, 155, 102], [132, 128, 18], [107, 153, 50]], ![[0, 1], [53, 182, 128], [66, 15, 186], [163, 128, 154], [167, 33, 153], [107, 20, 2], [145, 21, 46], [28, 45, 149]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [145, 96], []]
 b := ![[], [176, 162, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A199 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 199 3 where
 D := ![[64, 1], [71, 1], [6, 149, 64, 1]]; D' := ![[64, 1], [71, 1], [6, 149, 64, 1]]
 heqm := by decide
 hProd := by decide
 s := ![7, 7, 7]
 n := ![1, 1, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P199P0
  | 1 => exact P199P1
  | 2 => exact P199P2

def C1990 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A199.D 0) 199 where
  n := 1
  w := ![![199, 0, 0, 0, 0], ![64, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C1991 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A199.D 1) 199 where
  n := 1
  w := ![![199, 0, 0, 0, 0], ![71, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C1992 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A199.D 2) 199 where
  n := 3
  w := ![![199, 0, 0, 0, 0], ![6, 150, 64, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K199 : KummerData 199 ![I199N0, I199N1, I199N2] ![199, 199, 7880599] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A199
  C := by
    intro i
    match i with
    | 0 => exact C1990
    | 1 => exact C1991
    | 2 => exact C1992
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 199 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp211 : Fact (Nat.Prime 211) := {out := by norm_num}

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0, 0, 0], ![31, 1, 0, 0, 0]] i)))

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0, 0, 0], ![182, 1, 0, 0, 0]] i)))

def I211N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0, 0, 0], ![94, 60, 209, 2, 0]] i)))

def P211P0 : CertificateIrreducibleZModOfList' 211 1 2 7 [31, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [34], [], [], [148], [], [117, 180, 1]]]
 h' := ![![[0, 1], [1], [178], [173], [54], [123], [171], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P211P1 : CertificateIrreducibleZModOfList' 211 1 2 7 [182, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [80], [], [], [96], [], [208, 29, 1]]]
 h' := ![![[0, 1], [210], [49], [204], [41], [184], [124], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P211P2 : CertificateIrreducibleZModOfList' 211 3 2 7 [94, 59, 209, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [83, 148, 188], [130, 62, 23], [0, 1]]
 g := ![![[154, 145, 144], [22, 102, 144], [45, 161], [191, 99], [1, 135, 24], [194, 4], [1]], ![[208, 45, 108, 173], [27, 53, 29, 78], [21, 203], [174, 173], [30, 111, 168, 14], [102, 16], [128, 33, 175, 71]], ![[0, 101, 80, 165], [114, 139, 100, 8], [31, 113], [40, 49], [156, 32, 192, 175], [102, 36], [51, 204, 137, 140]]]
 h' := ![![[83, 148, 188], [42, 38, 12], [116, 166, 199], [166, 117, 43], [117, 74, 47], [95, 114, 92], [117, 152, 2], [0, 1]], ![[130, 62, 23], [58, 149, 81], [152, 81, 80], [4, 71, 186], [193, 111, 157], [58, 6, 128], [183, 167, 4], [83, 148, 188]], ![[0, 1], [0, 24, 118], [92, 175, 143], [91, 23, 193], [106, 26, 7], [0, 91, 202], [127, 103, 205], [130, 62, 23]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [168, 25], []]
 b := ![[], [36, 180, 102], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A211 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 211 3 where
 D := ![[31, 1], [182, 1], [94, 59, 209, 1]]; D' := ![[31, 1], [182, 1], [94, 59, 209, 1]]
 heqm := by decide
 hProd := by decide
 s := ![7, 7, 7]
 n := ![1, 1, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P211P0
  | 1 => exact P211P1
  | 2 => exact P211P2

def C2110 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A211.D 0) 211 where
  n := 1
  w := ![![211, 0, 0, 0, 0], ![31, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C2111 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A211.D 1) 211 where
  n := 1
  w := ![![211, 0, 0, 0, 0], ![182, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C2112 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A211.D 2) 211 where
  n := 3
  w := ![![211, 0, 0, 0, 0], ![94, 60, 209, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K211 : KummerData 211 ![I211N0, I211N1, I211N2] ![211, 211, 9393931] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A211
  C := by
    intro i
    match i with
    | 0 => exact C2110
    | 1 => exact C2111
    | 2 => exact C2112
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 211 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp223 : Fact (Nat.Prime 223) := {out := by norm_num}

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0, 0, 0], ![84, 59, 1, 0, 0]] i)))

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0, 0, 0], ![4, 53, 164, 2, 0]] i)))

def P223P0 : CertificateIrreducibleZModOfList' 223 2 2 7 [84, 59, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [164, 222], [0, 1]]
 g := ![![[83, 19], [162, 53], [6, 2], [98, 47], [139, 177], [28], [164, 1]], ![[77, 204], [157, 170], [111, 221], [1, 176], [177, 46], [28], [105, 222]]]
 h' := ![![[164, 222], [218, 58], [165, 62], [19, 15], [143, 173], [148, 203], [50, 52], [0, 1]], ![[0, 1], [141, 165], [75, 161], [26, 208], [194, 50], [213, 20], [104, 171], [164, 222]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58]]
 b := ![[], [75, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P223P1 : CertificateIrreducibleZModOfList' 223 3 2 7 [4, 52, 164, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [80, 149, 82], [202, 73, 141], [0, 1]]
 g := ![![[203, 0, 15], [167, 17, 169], [99, 99, 64], [86, 23, 74], [48, 4, 203], [104, 136], [1]], ![[216, 81, 21, 43], [15, 138, 161, 218], [71, 77, 123, 178], [43, 74, 25, 217], [42, 31, 158, 7], [115, 65], [46, 126, 175, 112]], ![[119, 17, 59, 208], [128, 140, 94, 129], [8, 145, 17, 84], [201, 2, 92, 46], [17, 153, 170, 117], [114, 146], [108, 133, 169, 111]]]
 h' := ![![[80, 149, 82], [1, 215, 125], [50, 177, 210], [102, 188, 215], [31, 50, 48], [46, 39, 181], [219, 171, 59], [0, 1]], ![[202, 73, 141], [130, 158, 218], [106, 97, 185], [150, 6, 114], [100, 208, 22], [55, 50, 132], [31, 159, 43], [80, 149, 82]], ![[0, 1], [55, 73, 103], [209, 172, 51], [186, 29, 117], [211, 188, 153], [102, 134, 133], [119, 116, 121], [202, 73, 141]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [205, 118], []]
 b := ![[], [26, 203, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A223 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 223 2 where
 D := ![[84, 59, 1], [4, 52, 164, 1]]; D' := ![[84, 59, 1], [4, 52, 164, 1]]
 heqm := by decide
 hProd := by decide
 s := ![7, 7]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P223P0
  | 1 => exact P223P1

def C2230 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A223.D 0) 223 where
  n := 2
  w := ![![223, 0, 0, 0, 0], ![84, 59, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C2231 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A223.D 1) 223 where
  n := 3
  w := ![![223, 0, 0, 0, 0], ![4, 53, 164, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K223 : KummerData 223 ![I223N0, I223N1] ![49729, 11089567] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A223
  C := by
    intro i
    match i with
    | 0 => exact C2230
    | 1 => exact C2231
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 223 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp227 : Fact (Nat.Prime 227) := {out := by norm_num}

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0, 0, 0], ![226, 1, 0, 0, 0]] i)))

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0, 0, 0], ![705, 2231, 10896, -3036, 22728]] i)))

def P227P0 : CertificateIrreducibleZModOfList' 227 1 2 7 [226, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [1], [], [], [], [1], [1, 1, 1]]]
 h' := ![![[0, 1], [1], [1], [1], [1], [1], [1], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P227P1 : CertificateIrreducibleZModOfList' 227 4 2 7 [57, 128, 1, 1, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 156, 28, 37], [143, 9, 122, 38], [79, 61, 77, 152], [0, 1]]
 g := ![![[211, 32, 201, 167], [156, 39, 120, 74], [26, 60, 53], [201, 78, 172], [146, 64, 160], [100, 0, 226, 1], []], ![[168, 88, 147, 188, 70, 20], [46, 135, 64, 100, 137, 157], [111, 94, 101], [18, 64, 11], [73, 203, 103], [198, 34, 64, 104, 200, 218], [197, 215, 37, 47, 102, 32]], ![[64, 109, 69, 143, 89, 51], [152, 193, 171, 223, 31, 211], [125, 109, 186], [143, 13, 212], [153, 146, 195], [34, 218, 146, 82, 10, 88], [141, 183, 65, 74, 110, 165]], ![[63, 35, 190, 120, 192, 174], [33, 78, 51, 171, 144, 170], [212, 189, 212], [98, 34, 219], [89, 95, 76], [172, 165, 37, 116, 164, 193], [36, 190, 176, 184, 136, 118]]]
 h' := ![![[4, 156, 28, 37], [188, 42, 123, 103], [206, 117, 204, 55], [107, 118, 108, 31], [21, 224, 154, 132], [202, 139, 184, 198], [0, 0, 0, 1], [0, 1]], ![[143, 9, 122, 38], [199, 82, 27, 89], [218, 33, 137, 68], [125, 181, 179, 76], [4, 114, 70, 187], [83, 46, 46, 28], [185, 208, 3, 104], [4, 156, 28, 37]], ![[79, 61, 77, 152], [179, 222, 56, 83], [41, 16, 102, 178], [105, 1, 118, 58], [159, 117, 11, 165], [150, 132, 35, 60], [128, 182, 132, 55], [143, 9, 122, 38]], ![[0, 1], [173, 108, 21, 179], [139, 61, 11, 153], [54, 154, 49, 62], [173, 226, 219, 197], [5, 137, 189, 168], [213, 64, 92, 67], [79, 61, 77, 152]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [166, 24, 222], []]
 b := ![[], [], [191, 28, 172, 30], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A227 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 227 2 where
 D := ![[226, 1], [57, 128, 1, 1, 1]]; D' := ![[226, 1], [57, 128, 1, 1, 1]]
 heqm := by decide
 hProd := by decide
 s := ![7, 7]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P227P0
  | 1 => exact P227P1

def C2270 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A227.D 0) 227 where
  n := 1
  w := ![![227, 0, 0, 0, 0], ![226, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C2271 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A227.D 1) 227 where
  n := 4
  w := ![![227, 0, 0, 0, 0], ![705, 2231, 10896, -3036, 22728]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K227 : KummerData 227 ![I227N0, I227N1] ![227, 2655237841] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A227
  C := by
    intro i
    match i with
    | 0 => exact C2270
    | 1 => exact C2271
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 227 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp229 : Fact (Nat.Prime 229) := {out := by norm_num}

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0, 0, 0], ![15801, 687, 229, 0, 0]] i)))

def P229P0 : CertificateIrreducibleZModOfList' 229 5 2 7 [81, 162, 129, 0, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [104, 5, 219, 41, 188], [58, 54, 221, 117, 126], [163, 13, 35, 134, 17], [133, 156, 212, 166, 127], [0, 1]]
 g := ![![[174, 175, 160, 150, 71], [181, 96, 112, 60], [128, 29, 22, 124, 85], [214, 185, 174, 169], [95, 197, 118, 153], [0, 0, 1], []], ![[113, 54, 103, 119, 125, 176, 212, 59], [69, 116, 5, 167], [135, 228, 218, 102, 215, 117, 134, 84], [142, 59, 13, 4], [49, 1, 22, 154], [36, 213, 87, 80, 214, 141, 186, 40], [209, 66, 180, 225, 1, 203, 205, 8]], ![[170, 67, 15, 130, 217, 81, 70, 26], [225, 13, 189, 209], [127, 47, 198, 13, 84, 224, 79, 17], [219, 38, 88, 183], [143, 183, 212, 224], [130, 160, 101, 203, 84, 133, 142, 55], [157, 221, 154, 30, 140, 219, 219, 61]], ![[203, 72, 182, 18, 174, 99, 158, 224], [41, 62, 184, 60], [84, 171, 132, 160, 107, 192, 46, 71], [146, 68, 6, 196], [123, 114, 28, 91], [167, 159, 87, 137, 66, 148, 144, 130], [82, 179, 128, 30, 145, 102, 75, 104]], ![[86, 221, 130, 128, 147, 78, 190, 131], [3, 168, 66, 183], [7, 32, 50, 162, 87, 36, 146, 29], [39, 207, 213, 209], [191, 11, 193, 70], [24, 226, 102, 113, 146, 108, 132, 67], [134, 65, 34, 100, 131, 91, 67, 207]]]
 h' := ![![[104, 5, 219, 41, 188], [71, 78, 191, 63, 23], [166, 43, 5, 91, 212], [107, 192, 211, 133, 90], [91, 26, 88, 99, 216], [0, 0, 148, 67, 100], [0, 0, 0, 1], [0, 1]], ![[58, 54, 221, 117, 126], [85, 100, 132, 204, 17], [117, 196, 207, 23, 25], [213, 140, 182, 71, 19], [223, 173, 30, 175, 2], [191, 73, 196, 47, 200], [33, 63, 6, 153, 42], [104, 5, 219, 41, 188]], ![[163, 13, 35, 134, 17], [69, 222, 139, 26, 73], [64, 21, 42, 74, 74], [108, 215, 219, 148, 180], [108, 206, 211, 204, 99], [142, 174, 182, 40, 37], [111, 123, 192, 58, 111], [58, 54, 221, 117, 126]], ![[133, 156, 212, 166, 127], [126, 66, 28, 226, 95], [87, 99, 215, 194, 17], [140, 135, 40, 7, 139], [150, 132, 205, 147, 215], [91, 93, 83, 183, 159], [127, 121, 17, 129, 103], [163, 13, 35, 134, 17]], ![[0, 1], [107, 221, 197, 168, 21], [11, 99, 218, 76, 130], [96, 5, 35, 99, 30], [222, 150, 153, 62, 155], [218, 118, 78, 121, 191], [29, 151, 14, 117, 202], [133, 156, 212, 166, 127]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [157, 17, 21, 78], [], [], []]
 b := ![[], [186, 138, 4, 8, 41], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A229 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 229 1 where
 D := ![[81, 162, 129, 0, 0, 1]]; D' := ![[81, 162, 129, 0, 0, 1]]
 heqm := by decide
 hProd := by decide
 s := ![7]
 n := ![5]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P229P0

def C2290 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A229.D 0) 229 where
  n := 5
  w := ![![229, 0, 0, 0, 0], ![15801, 687, 229, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K229 : KummerData 229 ![I229N0] ![629763392149] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A229
  C := by
    intro i
    match i with
    | 0 => exact C2290
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 229 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp233 : Fact (Nat.Prime 233) := {out := by norm_num}

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0, 0, 0], ![91, 1, 0, 0, 0]] i)))

def I233N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0, 0, 0], ![187, 1, 0, 0, 0]] i)))

def I233N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0, 0, 0], ![216, 1, 0, 0, 0]] i)))

def I233N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0, 0, 0], ![143, 205, 1, 0, 0]] i)))

def P233P0 : CertificateIrreducibleZModOfList' 233 1 2 7 [91, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [64], [], [71], [126, 142, 1]]]
 h' := ![![[0, 1], [1], [1], [1], [8], [63], [184], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P233P1 : CertificateIrreducibleZModOfList' 233 1 2 7 [187, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [76], [], [102], [19, 46, 1]]]
 h' := ![![[0, 1], [1], [1], [1], [92], [32], [175], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P233P2 : CertificateIrreducibleZModOfList' 233 1 2 7 [216, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [225], [], [167], [56, 17, 1]]]
 h' := ![![[0, 1], [232], [89], [97], [218], [43], [20], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P233P3 : CertificateIrreducibleZModOfList' 233 2 2 7 [143, 205, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [28, 232], [0, 1]]
 g := ![![[166, 66], [183], [132], [212, 144], [81], [155, 102], [28, 1]], ![[150, 167], [183], [132], [50, 89], [81], [215, 131], [56, 232]]]
 h' := ![![[28, 232], [137, 84], [207, 79], [207, 83], [35, 12], [203, 224], [190, 175], [0, 1]], ![[0, 1], [159, 149], [89, 154], [201, 150], [138, 221], [184, 9], [197, 58], [28, 232]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [211]]
 b := ![[], [154, 222]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A233 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 233 4 where
 D := ![[91, 1], [187, 1], [216, 1], [143, 205, 1]]; D' := ![[91, 1], [187, 1], [216, 1], [143, 205, 1]]
 heqm := by decide
 hProd := by decide
 s := ![7, 7, 7, 7]
 n := ![1, 1, 1, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P233P0
  | 1 => exact P233P1
  | 2 => exact P233P2
  | 3 => exact P233P3

def C2330 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A233.D 0) 233 where
  n := 1
  w := ![![233, 0, 0, 0, 0], ![91, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C2331 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A233.D 1) 233 where
  n := 1
  w := ![![233, 0, 0, 0, 0], ![187, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C2332 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A233.D 2) 233 where
  n := 1
  w := ![![233, 0, 0, 0, 0], ![216, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C2333 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A233.D 3) 233 where
  n := 2
  w := ![![233, 0, 0, 0, 0], ![143, 205, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K233 : KummerData 233 ![I233N0, I233N1, I233N2, I233N3] ![233, 233, 233, 54289] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A233
  C := by
    intro i
    match i with
    | 0 => exact C2330
    | 1 => exact C2331
    | 2 => exact C2332
    | 3 => exact C2333
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 233 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp239 : Fact (Nat.Prime 239) := {out := by norm_num}

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] i)))

def I239N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0, 0, 0], ![152, 1, 0, 0, 0]] i)))

def I239N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0, 0, 0], ![123, 75, 86, 2, 0]] i)))

def P239P0 : CertificateIrreducibleZModOfList' 239 1 2 7 [1, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [1], [1], [1], [], [1], [1, 238, 1]]]
 h' := ![![[0, 1], [238], [238], [238], [1], [238], [238], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P239P1 : CertificateIrreducibleZModOfList' 239 1 2 7 [152, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [11], [61], [51], [], [18], [160, 87, 1]]]
 h' := ![![[0, 1], [1], [49], [135], [216], [132], [58], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P239P2 : CertificateIrreducibleZModOfList' 239 3 2 7 [123, 74, 86, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [86, 51, 156], [67, 187, 83], [0, 1]]
 g := ![![[112, 43, 44], [196, 56, 180], [79, 2, 144], [178, 214, 45], [209, 150], [51, 223, 226], [1]], ![[46, 208, 48, 73], [236, 104, 96, 171], [7, 109, 101, 28], [179, 177, 97, 63], [60, 15], [23, 165, 192, 172], [33, 37, 176, 140]], ![[112, 41, 158, 83], [18, 227, 189, 211], [85, 69, 171, 153], [32, 41, 238, 187], [15, 220], [161, 51, 156, 2], [84, 37, 189, 99]]]
 h' := ![![[86, 51, 156], [31, 150, 98], [82, 115, 53], [94, 181, 227], [1, 50, 146], [180, 178, 110], [116, 165, 153], [0, 1]], ![[67, 187, 83], [233, 134, 140], [66, 176, 127], [41, 206, 180], [65, 64, 208], [6, 71, 60], [81, 100, 98], [86, 51, 156]], ![[0, 1], [70, 194, 1], [78, 187, 59], [136, 91, 71], [94, 125, 124], [79, 229, 69], [46, 213, 227], [67, 187, 83]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24, 141], []]
 b := ![[], [163, 97, 114], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A239 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 239 3 where
 D := ![[1, 1], [152, 1], [123, 74, 86, 1]]; D' := ![[1, 1], [152, 1], [123, 74, 86, 1]]
 heqm := by decide
 hProd := by decide
 s := ![7, 7, 7]
 n := ![1, 1, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P239P0
  | 1 => exact P239P1
  | 2 => exact P239P2

def C2390 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A239.D 0) 239 where
  n := 1
  w := ![![239, 0, 0, 0, 0], ![1, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C2391 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A239.D 1) 239 where
  n := 1
  w := ![![239, 0, 0, 0, 0], ![152, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C2392 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A239.D 2) 239 where
  n := 3
  w := ![![239, 0, 0, 0, 0], ![123, 75, 86, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K239 : KummerData 239 ![I239N0, I239N1, I239N2] ![239, 239, 13651919] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A239
  C := by
    intro i
    match i with
    | 0 => exact C2390
    | 1 => exact C2391
    | 2 => exact C2392
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 239 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp241 : Fact (Nat.Prime 241) := {out := by norm_num}

def I241N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0, 0, 0], ![201, 1, 0, 0, 0]] i)))

def I241N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0, 0, 0], ![139, 3, 1, 0, 0]] i)))

def I241N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0, 0, 0], ![145, 37, 1, 0, 0]] i)))

def P241P0 : CertificateIrreducibleZModOfList' 241 1 2 7 [201, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [], [143], [150], [154, 40, 1]]]
 h' := ![![[0, 1], [1], [1], [240], [177], [216], [135], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P241P1 : CertificateIrreducibleZModOfList' 241 2 2 7 [139, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [238, 240], [0, 1]]
 g := ![![[163, 100], [229], [158], [75], [68, 36], [181, 30], [238, 1]], ![[104, 141], [229], [158], [75], [201, 205], [91, 211], [235, 240]]]
 h' := ![![[238, 240], [228, 10], [27, 62], [96, 53], [188, 202], [146, 235], [176, 111], [0, 1]], ![[0, 1], [198, 231], [82, 179], [178, 188], [64, 39], [164, 6], [84, 130], [238, 240]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [115]]
 b := ![[], [26, 178]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P241P2 : CertificateIrreducibleZModOfList' 241 2 2 7 [145, 37, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [204, 240], [0, 1]]
 g := ![![[213, 123], [201], [29], [212], [90, 214], [123, 120], [204, 1]], ![[0, 118], [201], [29], [212], [125, 27], [21, 121], [167, 240]]]
 h' := ![![[204, 240], [13, 72], [210, 116], [199, 92], [205, 104], [240, 93], [63, 19], [0, 1]], ![[0, 1], [0, 169], [15, 125], [169, 149], [213, 137], [173, 148], [83, 222], [204, 240]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [146]]
 b := ![[], [25, 73]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A241 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 241 3 where
 D := ![[201, 1], [139, 3, 1], [145, 37, 1]]; D' := ![[201, 1], [139, 3, 1], [145, 37, 1]]
 heqm := by decide
 hProd := by decide
 s := ![7, 7, 7]
 n := ![1, 2, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P241P0
  | 1 => exact P241P1
  | 2 => exact P241P2

def C2410 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A241.D 0) 241 where
  n := 1
  w := ![![241, 0, 0, 0, 0], ![201, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C2411 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A241.D 1) 241 where
  n := 2
  w := ![![241, 0, 0, 0, 0], ![139, 3, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C2412 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A241.D 2) 241 where
  n := 2
  w := ![![241, 0, 0, 0, 0], ![145, 37, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K241 : KummerData 241 ![I241N0, I241N1, I241N2] ![241, 58081, 58081] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A241
  C := by
    intro i
    match i with
    | 0 => exact C2410
    | 1 => exact C2411
    | 2 => exact C2412
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 241 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp251 : Fact (Nat.Prime 251) := {out := by norm_num}

def I251N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![251, 0, 0, 0, 0], ![149, 1, 0, 0, 0]] i)))

def I251N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![251, 0, 0, 0, 0], ![205, 160, 1, 0, 0]] i)))

def I251N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![251, 0, 0, 0, 0], ![152, 193, 1, 0, 0]] i)))

def P251P0 : CertificateIrreducibleZModOfList' 251 1 2 7 [149, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [219], [], [1], [219], [149], [113, 102, 1]]]
 h' := ![![[0, 1], [250], [113], [102], [250], [138], [231], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P251P1 : CertificateIrreducibleZModOfList' 251 2 2 7 [205, 160, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [91, 250], [0, 1]]
 g := ![![[62, 60], [67, 92], [13], [244, 4], [43, 89], [125, 179], [91, 1]], ![[0, 191], [156, 159], [13], [106, 247], [110, 162], [99, 72], [182, 250]]]
 h' := ![![[91, 250], [70, 173], [117, 208], [180, 196], [221, 2], [228, 66], [170, 44], [0, 1]], ![[0, 1], [0, 78], [220, 43], [195, 55], [152, 249], [210, 185], [158, 207], [91, 250]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [91]]
 b := ![[], [126, 171]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P251P2 : CertificateIrreducibleZModOfList' 251 2 2 7 [152, 193, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [58, 250], [0, 1]]
 g := ![![[102, 180], [248, 39], [84], [4, 52], [], [157, 91], [58, 1]], ![[0, 71], [0, 212], [84], [8, 199], [], [164, 160], [116, 250]]]
 h' := ![![[58, 250], [205, 96], [225, 87], [145, 109], [0, 110], [232], [220, 200], [0, 1]], ![[0, 1], [0, 155], [0, 164], [192, 142], [105, 141], [232], [23, 51], [58, 250]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51]]
 b := ![[], [139, 151]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A251 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 251 3 where
 D := ![[149, 1], [205, 160, 1], [152, 193, 1]]; D' := ![[149, 1], [205, 160, 1], [152, 193, 1]]
 heqm := by decide
 hProd := by decide
 s := ![7, 7, 7]
 n := ![1, 2, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P251P0
  | 1 => exact P251P1
  | 2 => exact P251P2

def C2510 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A251.D 0) 251 where
  n := 1
  w := ![![251, 0, 0, 0, 0], ![149, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C2511 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A251.D 1) 251 where
  n := 2
  w := ![![251, 0, 0, 0, 0], ![205, 160, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C2512 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A251.D 2) 251 where
  n := 2
  w := ![![251, 0, 0, 0, 0], ![152, 193, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K251 : KummerData 251 ![I251N0, I251N1, I251N2] ![251, 63001, 63001] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A251
  C := by
    intro i
    match i with
    | 0 => exact C2510
    | 1 => exact C2511
    | 2 => exact C2512
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 251 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


lemma PB18792I5_primes (p : ℕ) :
  p ∈ Set.range ![199, 211, 223, 227, 229, 233, 239, 241, 251] ↔ Nat.Prime p ∧ 197 < p ∧ p ≤ 251 := by
  rw [← List.mem_ofFn']
  convert primes_range 197 251 (by omega)
  decide

def PB18792I5 : PrimesBelowBoundCertificateInterval O 197 251 18792 where
  m := 9
  g := ![3, 3, 2, 2, 1, 4, 3, 3, 3]
  P := ![199, 211, 223, 227, 229, 233, 239, 241, 251]
  hP := PB18792I5_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I199N0, I199N1, I199N2]
    · exact ![I211N0, I211N1, I211N2]
    · exact ![I223N0, I223N1]
    · exact ![I227N0, I227N1]
    · exact ![I229N0]
    · exact ![I233N0, I233N1, I233N2, I233N3]
    · exact ![I239N0, I239N1, I239N2]
    · exact ![I241N0, I241N1, I241N2]
    · exact ![I251N0, I251N1, I251N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · convert (containsPrimesAbove_of_KummerData K199) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K211) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K223) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K227) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K229) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K233) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K239) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K241) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K251) <;> rfl
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![199, 199, 7880599]
    · exact ![211, 211, 9393931]
    · exact ![49729, 11089567]
    · exact ![227, 2655237841]
    · exact ![629763392149]
    · exact ![233, 233, 233, 54289]
    · exact ![239, 239, 13651919]
    · exact ![241, 58081, 58081]
    · exact ![251, 63001, 63001]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact (card_quot_of_KummerData K199)
    · exact (card_quot_of_KummerData K211)
    · exact (card_quot_of_KummerData K223)
    · exact (card_quot_of_KummerData K227)
    · exact (card_quot_of_KummerData K229)
    · exact (card_quot_of_KummerData K233)
    · exact (card_quot_of_KummerData K239)
    · exact (card_quot_of_KummerData K241)
    · exact (card_quot_of_KummerData K251)
  β := ![I199N0, I199N1, I211N0, I211N1, I227N0, I233N0, I233N1, I233N2, I239N0, I239N1, I241N0, I251N0]
  Il := ![[I199N0, I199N1], [I211N0, I211N1], [], [I227N0], [], [I233N0, I233N1, I233N2], [I239N0, I239N1], [I241N0], [I251N0]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
