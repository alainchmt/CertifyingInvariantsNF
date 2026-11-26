
import IdealArithmetic.Examples.NF5_1_281250000_1_K.RI5_1_281250000_1_K
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 

instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0, 0, 0], ![398, -199, 0, 995, 0]] i)))

def P199P0 : CertificateIrreducibleZModOfList' 199 5 2 7 [98, 51, 0, 174, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [183, 151, 143, 44, 115], [121, 187, 110, 105, 91], [185, 95, 176, 67, 180], [108, 163, 168, 182, 12], [0, 1]]
 g := ![![[122, 28, 120, 180, 40], [120, 146, 148, 33, 139], [170, 10, 123, 185, 43], [56, 155, 189, 62], [75, 140, 0, 28], [0, 1], []], ![[89, 32, 11, 123, 169, 130, 146, 117], [88, 160, 95, 116, 196, 183, 152, 51], [93, 117, 167, 19, 99, 191, 52, 130], [139, 104, 98, 121], [82, 165], [104, 121, 74, 58], [106, 165, 165, 165, 147, 51, 72, 117]], ![[18, 43, 112, 117, 4, 195, 156, 145], [129, 99, 14, 96, 170, 24, 77, 144], [128, 168, 119, 173, 161, 144, 58, 128], [9, 16, 107, 169], [164, 121, 68, 29], [6, 137, 146, 16], [83, 22, 63, 195, 195, 156, 23, 157]], ![[139, 132, 102, 129, 171, 32, 53, 64], [97, 13, 19, 137, 85, 181, 140, 81], [53, 195, 149, 133, 114, 174, 173, 14], [91, 186, 108, 158], [169, 3, 124, 32], [80, 4, 190, 145], [173, 29, 167, 29, 173, 70, 125, 106]], ![[27, 126, 158, 64, 145, 39, 12, 149], [173, 69, 12, 161, 11, 62, 63, 55], [47, 15, 167, 129, 4, 163, 17, 197], [54, 85, 33, 43], [17, 194, 174, 131], [90, 130, 15, 122], [148, 60, 10, 114, 44, 14, 19, 136]]]
 h' := ![![[183, 151, 143, 44, 115], [180, 21, 141, 125, 144], [56, 32, 81, 171, 138], [54, 1, 120, 66, 21], [13, 166, 76, 172, 96], [0, 101, 148, 0, 25], [0, 0, 0, 1], [0, 1]], ![[121, 187, 110, 105, 91], [87, 119, 112, 54, 84], [57, 147, 17, 195, 107], [22, 15, 138, 175, 26], [149, 34, 80, 86, 188], [15, 56, 172, 168], [43, 66, 119, 24, 43], [183, 151, 143, 44, 115]], ![[185, 95, 176, 67, 180], [192, 62, 173, 7, 10], [132, 191, 133, 183, 142], [96, 42, 1, 7, 36], [111, 64, 123, 73, 13], [191, 150, 74, 113, 32], [88, 54, 11, 68, 4], [121, 187, 110, 105, 91]], ![[108, 163, 168, 182, 12], [39, 67, 134, 130, 192], [10, 20, 184, 26, 182], [109, 36, 169, 40, 30], [79, 116, 19, 82, 122], [129, 8, 83, 44, 119], [3, 17, 118, 70, 44], [185, 95, 176, 67, 180]], ![[0, 1], [70, 129, 37, 82, 167], [168, 8, 182, 22, 28], [95, 105, 169, 110, 86], [51, 18, 100, 184, 178], [181, 83, 120, 73, 23], [65, 62, 150, 36, 108], [108, 163, 168, 182, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [184, 71, 41, 118], [], [], []]
 b := ![[], [20, 189, 152, 178, 63], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A199 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 199 1 where
 D := ![[98, 51, 0, 174, 0, 1]]; D' := ![[98, 51, 0, 174, 0, 1]]
 heqm := by decide
 hProd := by decide
 s := ![7]
 n := ![5]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P199P0

def C1990 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A199.D 0) 199 where
  n := 5
  w := ![![199, 0, 0, 0, 0], ![398, -199, 0, 995, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K199 : KummerData 199 ![I199N0] ![312079600999] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A199
  C := by
    intro i
    match i with
    | 0 => exact C1990
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 199 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp211 : Fact (Nat.Prime 211) := {out := by norm_num}

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0, 0, 0], ![77, 1, 0, 0, 0]] i)))

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0, 0, 0], ![104, 53, 1, 0, 0]] i)))

def I211N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0, 0, 0], ![30, 81, 1, 0, 0]] i)))

def P211P0 : CertificateIrreducibleZModOfList' 211 1 2 7 [77, 1] where
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
 g := ![![[], [137], [], [], [107], [], [21, 134, 1]]]
 h' := ![![[0, 1], [1], [83], [100], [201], [188], [71], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P211P1 : CertificateIrreducibleZModOfList' 211 2 2 7 [104, 53, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [158, 210], [0, 1]]
 g := ![![[35, 58], [90, 49], [99], [19], [144, 45], [178], [158, 1]], ![[126, 153], [25, 162], [99], [19], [80, 166], [178], [105, 210]]]
 h' := ![![[158, 210], [135, 67], [4, 204], [159, 47], [5, 21], [99, 195], [26, 173], [0, 1]], ![[0, 1], [171, 144], [164, 7], [200, 164], [158, 190], [103, 16], [141, 38], [158, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [82]]
 b := ![[], [137, 41]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P211P2 : CertificateIrreducibleZModOfList' 211 2 2 7 [30, 81, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [130, 210], [0, 1]]
 g := ![![[66, 204], [174, 184], [185], [169], [67, 105], [100], [130, 1]], ![[0, 7], [40, 27], [185], [169], [2, 106], [100], [49, 210]]]
 h' := ![![[130, 210], [55, 170], [168, 124], [77, 94], [100, 13], [19, 59], [109, 201], [0, 1]], ![[0, 1], [0, 41], [41, 87], [59, 117], [102, 198], [93, 152], [75, 10], [130, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [76]]
 b := ![[], [62, 38]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A211 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 211 3 where
 D := ![[77, 1], [104, 53, 1], [30, 81, 1]]; D' := ![[77, 1], [104, 53, 1], [30, 81, 1]]
 heqm := by decide
 hProd := by decide
 s := ![7, 7, 7]
 n := ![1, 2, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P211P0
  | 1 => exact P211P1
  | 2 => exact P211P2

def C2110 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A211.D 0) 211 where
  n := 1
  w := ![![211, 0, 0, 0, 0], ![77, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C2111 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A211.D 1) 211 where
  n := 2
  w := ![![211, 0, 0, 0, 0], ![104, 53, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C2112 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A211.D 2) 211 where
  n := 2
  w := ![![211, 0, 0, 0, 0], ![30, 81, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K211 : KummerData 211 ![I211N0, I211N1, I211N2] ![211, 44521, 44521] where
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

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0, 0, 0], ![206, 1, 0, 0, 0]] i)))

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0, 0, 0], ![57, 28, 46, 85, 10]] i)))

def P223P0 : CertificateIrreducibleZModOfList' 223 1 2 7 [206, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [105], [60], [64], [171], [], [66, 17, 1]]]
 h' := ![![[0, 1], [1], [128], [196], [8], [49], [7], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P223P1 : CertificateIrreducibleZModOfList' 223 4 2 7 [57, 28, 41, 17, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [103, 47, 35, 122], [135, 80, 49, 60], [191, 95, 139, 41], [0, 1]]
 g := ![![[96, 33, 124, 144], [159, 137, 147, 36], [138, 118, 146, 124], [166, 26, 154, 220], [205, 42, 55, 218], [25, 206, 1], []], ![[67, 57, 130, 46, 115, 96], [170, 195, 5, 70, 149, 79], [96, 175, 23, 152, 33, 108], [66, 39, 147, 136, 155, 59], [71, 13, 88, 10, 108, 85], [111, 31, 201], [62, 44, 162, 35, 64, 182]], ![[155, 102, 15, 131, 107, 130], [150, 30, 129, 75, 217, 197], [145, 218, 139, 101, 65, 65], [19, 196, 120, 162, 75, 68], [108, 14, 159, 218, 134, 152], [193, 91, 49], [33, 46, 39, 25, 162, 136]], ![[47, 173, 43, 28, 47, 28], [218, 72, 159, 58, 186, 68], [150, 66, 165, 186, 85, 121], [116, 52, 84, 211, 68, 132], [66, 122, 128, 75, 171, 203], [137, 156, 143], [0, 98, 127, 22, 73, 14]]]
 h' := ![![[103, 47, 35, 122], [80, 157, 153, 211], [162, 187, 104, 217], [127, 7, 187, 74], [134, 104, 19, 79], [136, 46, 63, 21], [0, 0, 0, 1], [0, 1]], ![[135, 80, 49, 60], [104, 66, 112, 189], [99, 121, 109, 75], [174, 169, 38, 48], [18, 170, 1, 21], [70, 23, 178, 63], [61, 201, 187, 76], [103, 47, 35, 122]], ![[191, 95, 139, 41], [56, 51, 127, 100], [188, 63, 61, 26], [142, 35, 144, 81], [122, 153, 164, 4], [20, 192, 103, 114], [142, 100, 66, 7], [135, 80, 49, 60]], ![[0, 1], [176, 172, 54, 169], [81, 75, 172, 128], [4, 12, 77, 20], [90, 19, 39, 119], [165, 185, 102, 25], [13, 145, 193, 139], [191, 95, 139, 41]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [7, 88, 166], []]
 b := ![[], [], [40, 85, 136, 79], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A223 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 223 2 where
 D := ![[206, 1], [57, 28, 41, 17, 1]]; D' := ![[206, 1], [57, 28, 41, 17, 1]]
 heqm := by decide
 hProd := by decide
 s := ![7, 7]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P223P0
  | 1 => exact P223P1

def C2230 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A223.D 0) 223 where
  n := 1
  w := ![![223, 0, 0, 0, 0], ![206, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C2231 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A223.D 1) 223 where
  n := 4
  w := ![![223, 0, 0, 0, 0], ![57, 28, 46, 85, 10]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K223 : KummerData 223 ![I223N0, I223N1] ![223, 2472973441] where
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

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0, 0, 0], ![134, 208, 1, 0, 0]] i)))

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0, 0, 0], ![157, 202, 19, 5, 0]] i)))

def P227P0 : CertificateIrreducibleZModOfList' 227 2 2 7 [134, 208, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 226], [0, 1]]
 g := ![![[215, 144], [83, 139], [99], [78], [136], [], [19, 1]], ![[0, 83], [0, 88], [99], [78], [136], [], [38, 226]]]
 h' := ![![[19, 226], [1, 215], [127, 65], [0, 107], [163, 87], [0, 131], [178], [0, 1]], ![[0, 1], [0, 12], [0, 162], [217, 120], [0, 140], [219, 96], [178], [19, 226]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [192]]
 b := ![[], [223, 96]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P227P1 : CertificateIrreducibleZModOfList' 227 3 2 7 [157, 202, 19, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [101, 107, 13], [107, 119, 214], [0, 1]]
 g := ![![[89, 71, 172], [95, 41, 26], [206, 190], [53, 129], [39, 225], [93, 136, 134], [1]], ![[57, 89, 180, 201], [38, 157, 72, 208], [6, 192], [144, 97], [177, 75], [59, 212, 42, 152], [186, 180, 21, 154]], ![[43, 180, 151, 11], [224, 64, 155, 207], [163, 97], [177, 147], [23, 64], [129, 226, 102, 116], [147, 61, 153, 73]]]
 h' := ![![[101, 107, 13], [67, 57, 95], [184, 172, 88], [135, 87, 155], [114, 174, 122], [154, 174, 212], [70, 25, 208], [0, 1]], ![[107, 119, 214], [40, 186, 15], [74, 100, 223], [154, 223, 54], [210, 52, 209], [87, 173, 23], [29, 44, 107], [101, 107, 13]], ![[0, 1], [147, 211, 117], [52, 182, 143], [197, 144, 18], [92, 1, 123], [57, 107, 219], [226, 158, 139], [107, 119, 214]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [112, 174], []]
 b := ![[], [199, 135, 39], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A227 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 227 2 where
 D := ![[134, 208, 1], [157, 202, 19, 1]]; D' := ![[134, 208, 1], [157, 202, 19, 1]]
 heqm := by decide
 hProd := by decide
 s := ![7, 7]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P227P0
  | 1 => exact P227P1

def C2270 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A227.D 0) 227 where
  n := 2
  w := ![![227, 0, 0, 0, 0], ![134, 208, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C2271 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A227.D 1) 227 where
  n := 3
  w := ![![227, 0, 0, 0, 0], ![157, 202, 19, 5, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K227 : KummerData 227 ![I227N0, I227N1] ![51529, 11697083] where
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

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0, 0, 0], ![30, 1, 0, 0, 0]] i)))

def I229N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0, 0, 0], ![147, 1, 0, 0, 0]] i)))

def I229N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0, 0, 0], ![123, 101, 52, 5, 0]] i)))

def P229P0 : CertificateIrreducibleZModOfList' 229 1 2 7 [30, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [57], [], [], [26], [213, 199, 1]]]
 h' := ![![[0, 1], [228], [122], [61], [176], [136], [22], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P229P1 : CertificateIrreducibleZModOfList' 229 1 2 7 [147, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [81], [], [], [203], [83, 82, 1]]]
 h' := ![![[0, 1], [1], [1], [9], [3], [158], [165], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P229P2 : CertificateIrreducibleZModOfList' 229 3 2 7 [123, 101, 52, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [17, 36, 98], [160, 192, 131], [0, 1]]
 g := ![![[227, 176, 220], [134, 167], [164, 42, 132], [129, 61], [80, 151], [18, 197, 185], [1]], ![[103, 36, 41, 66], [102, 218], [129, 208, 55, 106], [72, 225], [85, 1], [107, 95, 149, 87], [134, 186, 216, 2]], ![[129, 55, 150, 160], [193, 82], [121, 78, 63, 101], [186, 44], [207, 80], [126, 129, 227, 50], [6, 107, 55, 227]]]
 h' := ![![[17, 36, 98], [177, 93, 92], [209, 16, 204], [92, 216, 210], [58, 92, 176], [76, 72, 36], [106, 128, 177], [0, 1]], ![[160, 192, 131], [140, 73, 214], [159, 194, 203], [11, 176, 116], [60, 203, 214], [179, 46, 228], [110, 67, 41], [17, 36, 98]], ![[0, 1], [226, 63, 152], [81, 19, 51], [27, 66, 132], [66, 163, 68], [197, 111, 194], [55, 34, 11], [160, 192, 131]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [75, 197], []]
 b := ![[], [104, 178, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A229 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 229 3 where
 D := ![[30, 1], [147, 1], [123, 101, 52, 1]]; D' := ![[30, 1], [147, 1], [123, 101, 52, 1]]
 heqm := by decide
 hProd := by decide
 s := ![7, 7, 7]
 n := ![1, 1, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P229P0
  | 1 => exact P229P1
  | 2 => exact P229P2

def C2290 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A229.D 0) 229 where
  n := 1
  w := ![![229, 0, 0, 0, 0], ![30, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C2291 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A229.D 1) 229 where
  n := 1
  w := ![![229, 0, 0, 0, 0], ![147, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C2292 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A229.D 2) 229 where
  n := 3
  w := ![![229, 0, 0, 0, 0], ![123, 101, 52, 5, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K229 : KummerData 229 ![I229N0, I229N1, I229N2] ![229, 229, 12008989] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A229
  C := by
    intro i
    match i with
    | 0 => exact C2290
    | 1 => exact C2291
    | 2 => exact C2292
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 229 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp233 : Fact (Nat.Prime 233) := {out := by norm_num}

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0, 0, 0], ![59, 25, 1, 0, 0]] i)))

def I233N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0, 0, 0], ![66, 75, 208, 5, 0]] i)))

def P233P0 : CertificateIrreducibleZModOfList' 233 2 2 7 [59, 25, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [208, 232], [0, 1]]
 g := ![![[111, 85], [182], [131], [7, 135], [23], [31, 214], [208, 1]], ![[83, 148], [182], [131], [127, 98], [23], [40, 19], [183, 232]]]
 h' := ![![[208, 232], [10, 205], [206, 132], [53, 197], [101, 169], [35, 217], [77, 100], [0, 1]], ![[0, 1], [11, 28], [168, 101], [21, 36], [70, 64], [202, 16], [140, 133], [208, 232]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [227]]
 b := ![[], [79, 230]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P233P1 : CertificateIrreducibleZModOfList' 233 3 2 7 [66, 75, 208, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [169, 220, 112], [89, 12, 121], [0, 1]]
 g := ![![[121, 26, 1], [201, 98], [47, 128], [171, 110, 123], [33, 205], [219, 225, 159], [1]], ![[114, 40, 192, 162], [41, 204], [184, 148], [219, 170, 120, 85], [211, 33], [100, 32, 186, 18], [156, 159, 165, 171]], ![[207, 34, 108, 105], [124, 76], [179, 178], [79, 22, 50, 224], [69, 112], [57, 210, 32, 141], [60, 86, 182, 62]]]
 h' := ![![[169, 220, 112], [198, 116, 232], [79, 171, 129], [131, 9, 19], [216, 192, 39], [225, 109, 122], [167, 158, 25], [0, 1]], ![[89, 12, 121], [105, 114, 165], [134, 103, 196], [66, 54, 71], [26, 185, 70], [111, 147, 158], [170, 35, 55], [169, 220, 112]], ![[0, 1], [153, 3, 69], [101, 192, 141], [126, 170, 143], [198, 89, 124], [201, 210, 186], [145, 40, 153], [89, 12, 121]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52, 81], []]
 b := ![[], [232, 101, 18], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A233 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 233 2 where
 D := ![[59, 25, 1], [66, 75, 208, 1]]; D' := ![[59, 25, 1], [66, 75, 208, 1]]
 heqm := by decide
 hProd := by decide
 s := ![7, 7]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P233P0
  | 1 => exact P233P1

def C2330 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A233.D 0) 233 where
  n := 2
  w := ![![233, 0, 0, 0, 0], ![59, 25, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C2331 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A233.D 1) 233 where
  n := 3
  w := ![![233, 0, 0, 0, 0], ![66, 75, 208, 5, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K233 : KummerData 233 ![I233N0, I233N1] ![54289, 12649337] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A233
  C := by
    intro i
    match i with
    | 0 => exact C2330
    | 1 => exact C2331
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 233 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp239 : Fact (Nat.Prime 239) := {out := by norm_num}

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0, 0, 0], ![478, -239, 0, 1195, 0]] i)))

def P239P0 : CertificateIrreducibleZModOfList' 239 5 2 7 [178, 11, 0, 214, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [182, 172, 139, 88, 198], [209, 216, 113, 45, 217], [135, 109, 169, 10, 83], [191, 219, 57, 96, 219], [0, 1]]
 g := ![![[50, 39, 111, 183, 163], [188, 147, 218, 44, 136], [138, 164, 181, 85, 8], [181, 52, 156, 117, 109], [101, 93], [25, 0, 1], []], ![[13, 224, 74, 70, 41, 224, 54, 116], [177, 139, 51, 124, 52, 91, 206, 66], [123, 60, 233, 191, 35, 46, 166, 180], [66, 106, 103, 152, 33, 15, 190, 24], [0, 156, 103, 34], [214, 70, 51, 145, 36, 204, 169, 8], [51, 138, 13, 43, 67, 58, 200, 150]], ![[209, 74, 130, 221, 22, 66, 206, 131], [125, 177, 93, 225, 156, 104, 137, 139], [143, 199, 150, 57, 116, 117, 132, 137], [69, 217, 72, 137, 28, 17, 76, 148], [190, 42, 83, 157], [55, 191, 209, 81, 175, 35, 214, 234], [223, 60, 134, 2, 196, 119, 93, 107]], ![[161, 215, 28, 148, 104, 81, 222, 136], [212, 183, 92, 171, 184, 50, 116, 62], [162, 221, 178, 4, 173, 170, 206, 161], [60, 187, 165, 211, 165, 1, 71, 133], [238, 158, 122, 29], [190, 56, 234, 78, 108, 195, 119, 10], [171, 210, 47, 174, 82, 106, 174, 99]], ![[54, 106, 188, 218, 76, 54, 157, 184], [108, 38, 151, 227, 176, 81, 140, 65], [64, 127, 233, 90, 163, 108, 104, 158], [113, 115, 162, 219, 201, 92, 230, 42], [137, 17, 82, 6], [187, 14, 125, 57, 217, 47, 51, 223], [6, 15, 179, 178, 40, 175, 2, 126]]]
 h' := ![![[182, 172, 139, 88, 198], [235, 148, 63, 163, 101], [53, 179, 22, 161, 61], [47, 113, 202, 66, 198], [102, 161, 142, 180, 78], [91, 203, 61, 136], [0, 0, 0, 1], [0, 1]], ![[209, 216, 113, 45, 217], [184, 10, 171, 166, 133], [95, 157, 133, 207, 124], [161, 32, 128, 123, 48], [116, 108, 39, 33, 127], [127, 42, 186, 61, 89], [36, 108, 222, 166, 213], [182, 172, 139, 88, 198]], ![[135, 109, 169, 10, 83], [66, 161, 47, 141, 55], [31, 201, 169, 25, 185], [153, 221, 26, 211, 59], [209, 106, 176, 228, 179], [197, 158, 182, 210, 184], [226, 52, 192, 128, 24], [209, 216, 113, 45, 217]], ![[191, 219, 57, 96, 219], [97, 200, 64, 122, 94], [62, 90, 25, 237, 65], [19, 6, 63, 81, 169], [40, 209, 88, 155, 4], [203, 78, 43, 80, 183], [24, 45, 193, 78, 133], [135, 109, 169, 10, 83]], ![[0, 1], [74, 198, 133, 125, 95], [122, 90, 129, 87, 43], [183, 106, 59, 236, 4], [114, 133, 33, 121, 90], [19, 236, 6, 230, 22], [192, 34, 110, 105, 108], [191, 219, 57, 96, 219]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [221, 21, 208, 48], [], [], []]
 b := ![[], [166, 145, 181, 160, 7], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A239 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 239 1 where
 D := ![[178, 11, 0, 214, 0, 1]]; D' := ![[178, 11, 0, 214, 0, 1]]
 heqm := by decide
 hProd := by decide
 s := ![7]
 n := ![5]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P239P0

def C2390 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A239.D 0) 239 where
  n := 5
  w := ![![239, 0, 0, 0, 0], ![478, -239, 0, 1195, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K239 : KummerData 239 ![I239N0] ![779811265199] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A239
  C := by
    intro i
    match i with
    | 0 => exact C2390
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 239 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp241 : Fact (Nat.Prime 241) := {out := by norm_num}

def I241N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0, 0, 0], ![40, 1, 0, 0, 0]] i)))

def I241N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0, 0, 0], ![56, 1, 0, 0, 0]] i)))

def I241N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0, 0, 0], ![101, 203, 145, 5, 0]] i)))

def P241P0 : CertificateIrreducibleZModOfList' 241 1 2 7 [40, 1] where
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
 g := ![![[], [], [], [], [143], [150], [154, 201, 1]]]
 h' := ![![[0, 1], [1], [1], [240], [64], [25], [106], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P241P1 : CertificateIrreducibleZModOfList' 241 1 2 7 [56, 1] where
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
 g := ![![[], [], [], [], [18], [27], [3, 185, 1]]]
 h' := ![![[0, 1], [240], [64], [8], [197], [175], [73], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P241P2 : CertificateIrreducibleZModOfList' 241 3 2 7 [101, 203, 145, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [23, 114, 75], [73, 126, 166], [0, 1]]
 g := ![![[236, 235, 216], [118, 30], [81, 150], [85, 194], [52, 39, 87], [222, 91, 58], [1]], ![[27, 91, 85, 32], [76, 87], [32, 41], [18, 151], [135, 207, 117, 196], [173, 71, 127, 236], [177, 125, 38, 125]], ![[236, 7, 23, 162], [113, 75], [86, 125], [172, 214], [198, 145, 81, 188], [218, 200, 31, 233], [231, 165, 198, 116]]]
 h' := ![![[23, 114, 75], [136, 6, 79], [239, 121, 130], [181, 45, 106], [50, 46, 215], [232, 47, 150], [140, 38, 96], [0, 1]], ![[73, 126, 166], [113, 238, 41], [42, 162, 150], [158, 99, 102], [17, 162, 174], [25, 103, 12], [74, 53, 4], [23, 114, 75]], ![[0, 1], [235, 238, 121], [70, 199, 202], [171, 97, 33], [51, 33, 93], [228, 91, 79], [89, 150, 141], [73, 126, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 84], []]
 b := ![[], [68, 9, 76], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A241 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 241 3 where
 D := ![[40, 1], [56, 1], [101, 203, 145, 1]]; D' := ![[40, 1], [56, 1], [101, 203, 145, 1]]
 heqm := by decide
 hProd := by decide
 s := ![7, 7, 7]
 n := ![1, 1, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P241P0
  | 1 => exact P241P1
  | 2 => exact P241P2

def C2410 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A241.D 0) 241 where
  n := 1
  w := ![![241, 0, 0, 0, 0], ![40, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C2411 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A241.D 1) 241 where
  n := 1
  w := ![![241, 0, 0, 0, 0], ![56, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C2412 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A241.D 2) 241 where
  n := 3
  w := ![![241, 0, 0, 0, 0], ![101, 203, 145, 5, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K241 : KummerData 241 ![I241N0, I241N1, I241N2] ![241, 241, 13997521] where
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

def I251N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![251, 0, 0, 0, 0], ![72, 1, 0, 0, 0]] i)))

def I251N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![251, 0, 0, 0, 0], ![129, 193, 1, 0, 0]] i)))

def I251N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![251, 0, 0, 0, 0], ![202, 237, 1, 0, 0]] i)))

def P251P0 : CertificateIrreducibleZModOfList' 251 1 2 7 [72, 1] where
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
 g := ![![[], [122], [], [249], [58], [121], [164, 179, 1]]]
 h' := ![![[0, 1], [1], [154], [144], [91], [73], [240], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P251P1 : CertificateIrreducibleZModOfList' 251 2 2 7 [129, 193, 1] where
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
 g := ![![[91, 23], [131, 219], [81], [168, 92], [238, 67], [114, 31], [58, 1]], ![[170, 228], [32, 32], [81], [233, 159], [108, 184], [155, 220], [116, 250]]]
 h' := ![![[58, 250], [169, 104], [210, 138], [165, 9], [171, 208], [103, 148], [48, 223], [0, 1]], ![[0, 1], [177, 147], [182, 113], [185, 242], [187, 43], [153, 103], [181, 28], [58, 250]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49]]
 b := ![[], [168, 150]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P251P2 : CertificateIrreducibleZModOfList' 251 2 2 7 [202, 237, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [14, 250], [0, 1]]
 g := ![![[72, 105], [51, 23], [28], [133, 114], [217, 85], [53, 36], [14, 1]], ![[36, 146], [122, 228], [28], [223, 137], [152, 166], [55, 215], [28, 250]]]
 h' := ![![[14, 250], [240, 132], [198, 147], [242, 167], [91, 214], [87, 218], [184, 245], [0, 1]], ![[0, 1], [80, 119], [248, 104], [70, 84], [75, 37], [127, 33], [100, 6], [14, 250]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [105]]
 b := ![[], [9, 178]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A251 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 251 3 where
 D := ![[72, 1], [129, 193, 1], [202, 237, 1]]; D' := ![[72, 1], [129, 193, 1], [202, 237, 1]]
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
  w := ![![251, 0, 0, 0, 0], ![72, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C2511 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A251.D 1) 251 where
  n := 2
  w := ![![251, 0, 0, 0, 0], ![129, 193, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C2512 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A251.D 2) 251 where
  n := 2
  w := ![![251, 0, 0, 0, 0], ![202, 237, 1, 0, 0]]
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


lemma PB1045I5_primes (p : ℕ) :
  p ∈ Set.range ![199, 211, 223, 227, 229, 233, 239, 241, 251] ↔ Nat.Prime p ∧ 197 < p ∧ p ≤ 251 := by
  rw [← List.mem_ofFn']
  convert primes_range 197 251 (by omega)
  decide

def PB1045I5 : PrimesBelowBoundCertificateInterval O 197 251 1045 where
  m := 9
  g := ![1, 3, 2, 2, 3, 2, 1, 3, 3]
  P := ![199, 211, 223, 227, 229, 233, 239, 241, 251]
  hP := PB1045I5_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I199N0]
    · exact ![I211N0, I211N1, I211N2]
    · exact ![I223N0, I223N1]
    · exact ![I227N0, I227N1]
    · exact ![I229N0, I229N1, I229N2]
    · exact ![I233N0, I233N1]
    · exact ![I239N0]
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
    · exact ![312079600999]
    · exact ![211, 44521, 44521]
    · exact ![223, 2472973441]
    · exact ![51529, 11697083]
    · exact ![229, 229, 12008989]
    · exact ![54289, 12649337]
    · exact ![779811265199]
    · exact ![241, 241, 13997521]
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
  β := ![I211N0, I223N0, I229N0, I229N1, I241N0, I241N1, I251N0]
  Il := ![[], [I211N0], [I223N0], [], [I229N0, I229N1], [], [], [I241N0, I241N1], [I251N0]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
