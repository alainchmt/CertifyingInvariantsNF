
import IdealArithmetic.Examples.NF5_1_281250000_1_K.RI5_1_281250000_1_K
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 

instance hp257 : Fact (Nat.Prime 257) := {out := by norm_num}

def I257N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![257, 0, 0, 0, 0], ![205, 196, 1, 0, 0]] i)))

def I257N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![257, 0, 0, 0, 0], ![243, 150, 61, 5, 0]] i)))

def P257P0 : CertificateIrreducibleZModOfList' 257 2 2 8 [205, 196, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [61, 256], [0, 1]]
 g := ![![[16, 84], [34], [221], [35], [2], [190], [123], [1]], ![[0, 173], [34], [221], [35], [2], [190], [123], [1]]]
 h' := ![![[61, 256], [201, 220], [80, 88], [47, 161], [138, 99], [88, 197], [105, 226], [52, 61], [0, 1]], ![[0, 1], [0, 37], [51, 169], [102, 96], [9, 158], [26, 60], [13, 31], [175, 196], [61, 256]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [250]]
 b := ![[], [171, 125]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P257P1 : CertificateIrreducibleZModOfList' 257 3 2 8 [243, 150, 61, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [221, 146, 83], [232, 110, 174], [0, 1]]
 g := ![![[181, 141, 122], [74, 211], [109, 117], [], [76, 143], [118, 215], [196, 1], []], ![[96, 227, 76, 109], [214, 196], [190, 13], [98, 169], [205, 143], [37, 36], [100, 21], [44, 207]], ![[54, 83, 238, 76], [78, 228], [220, 208], [164, 169], [48, 58], [205, 184], [82, 242], [210, 207]]]
 h' := ![![[221, 146, 83], [81, 11, 76], [79, 50, 168], [159, 242, 84], [38, 37], [60, 175, 20], [174, 169, 230], [0, 0, 1], [0, 1]], ![[232, 110, 174], [49, 228, 21], [44, 196, 14], [168, 169, 28], [248, 5, 244], [132, 69, 20], [34, 79, 6], [113, 178, 110], [221, 146, 83]], ![[0, 1], [125, 18, 160], [224, 11, 75], [75, 103, 145], [141, 215, 13], [165, 13, 217], [181, 9, 21], [224, 79, 146], [232, 110, 174]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [142, 19], []]
 b := ![[], [9, 28, 232], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A257 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 257 2 where
 D := ![[205, 196, 1], [243, 150, 61, 1]]; D' := ![[205, 196, 1], [243, 150, 61, 1]]
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
  w := ![![257, 0, 0, 0, 0], ![205, 196, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C2571 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A257.D 1) 257 where
  n := 3
  w := ![![257, 0, 0, 0, 0], ![243, 150, 61, 5, 0]]
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

def I263N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] i)))

def I263N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263, 0, 0, 0, 0], ![226, 24, 244, 1310, 10]] i)))

def P263P0 : CertificateIrreducibleZModOfList' 263 1 2 8 [1, 1] where
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
 g := ![![[], [1], [1], [], [], [], [], [262, 1]]]
 h' := ![![[0, 1], [262], [262], [1], [1], [1], [1], [1], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P263P1 : CertificateIrreducibleZModOfList' 263 4 2 8 [226, 24, 239, 262, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [26, 218, 231, 195], [10, 250, 213, 57], [228, 57, 82, 11], [0, 1]]
 g := ![![[86, 140], [214, 9, 28, 204], [262, 0, 224, 147], [1, 45, 33], [122, 101, 109], [75, 49, 1], [1], []], ![[6, 237, 259, 104, 97, 94], [60, 48, 153, 21, 98, 87], [109, 11, 199, 261, 152, 195], [205, 123, 136], [186, 154, 68], [119, 15, 50], [15, 83, 150], [67, 34, 153]], ![[30, 228, 238, 143, 71, 191], [116, 207, 35, 104, 237, 142], [186, 237, 246, 118, 36, 160], [208, 183, 39], [12, 227, 176], [189, 217, 166], [98, 51, 8], [10, 179, 93]], ![[157, 83, 78, 136, 207, 74], [209, 262, 262, 167, 140, 27], [118, 122, 10, 223, 101, 96], [107, 170, 18], [126, 14, 242], [147, 242, 83], [144, 50, 26], [183, 84, 121]]]
 h' := ![![[26, 218, 231, 195], [28, 248, 107], [226, 175, 47, 166], [64, 131, 177, 102], [194, 30, 258, 104], [199, 78, 120, 149], [37, 239, 24, 1], [0, 0, 1], [0, 1]], ![[10, 250, 213, 57], [57, 41, 16, 79], [149, 112, 192, 7], [32, 205, 207, 1], [52, 223, 200, 165], [43, 28, 59, 130], [30, 201, 202, 24], [262, 203, 239, 237], [26, 218, 231, 195]], ![[228, 57, 82, 11], [198, 223, 146, 64], [255, 254, 31, 229], [10, 219, 54, 208], [166, 46, 234, 61], [145, 13, 40, 142], [187, 189, 6, 70], [207, 74, 132, 43], [10, 250, 213, 57]], ![[0, 1], [60, 14, 257, 120], [25, 248, 256, 124], [114, 234, 88, 215], [253, 227, 97, 196], [204, 144, 44, 105], [258, 160, 31, 168], [106, 249, 154, 246], [228, 57, 82, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [215, 262, 216], []]
 b := ![[], [], [217, 126, 212, 190], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A263 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 263 2 where
 D := ![[1, 1], [226, 24, 239, 262, 1]]; D' := ![[1, 1], [226, 24, 239, 262, 1]]
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
  w := ![![263, 0, 0, 0, 0], ![1, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C2631 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A263.D 1) 263 where
  n := 4
  w := ![![263, 0, 0, 0, 0], ![226, 24, 244, 1310, 10]]
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

def I269N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![269, 0, 0, 0, 0], ![113, 1, 0, 0, 0]] i)))

def I269N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![269, 0, 0, 0, 0], ![224, 1, 0, 0, 0]] i)))

def I269N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![269, 0, 0, 0, 0], ![154, 0, 201, 5, 0]] i)))

def P269P0 : CertificateIrreducibleZModOfList' 269 1 2 8 [113, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [65], [37], [], [], [], [156, 1]]]
 h' := ![![[0, 1], [268], [187], [123], [87], [25], [5], [126], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P269P1 : CertificateIrreducibleZModOfList' 269 1 2 8 [224, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [263], [44], [], [], [], [45, 1]]]
 h' := ![![[0, 1], [1], [268], [97], [115], [121], [258], [142], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P269P2 : CertificateIrreducibleZModOfList' 269 3 2 8 [154, 0, 201, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [232, 39, 57], [105, 229, 212], [0, 1]]
 g := ![![[264, 141, 125], [195, 173], [157, 260, 246], [267, 236, 55], [168, 105], [29, 180], [68, 1], []], ![[141, 246, 194, 214], [64, 11], [106, 152, 210, 264], [71, 210, 120, 67], [173, 96], [222, 136], [144, 255], [225, 21]], ![[207, 12, 166, 64], [182, 218], [158, 264, 131, 164], [216, 240, 0, 265], [134, 49], [39, 49], [17, 176], [70, 21]]]
 h' := ![![[232, 39, 57], [46, 158, 177], [32, 217, 119], [39, 71, 28], [10, 82, 18], [199, 53, 188], [19, 115, 51], [0, 0, 1], [0, 1]], ![[105, 229, 212], [212, 267, 43], [121, 27, 77], [50, 72, 237], [209, 100, 188], [233, 137, 74], [127, 101, 211], [75, 67, 229], [232, 39, 57]], ![[0, 1], [14, 113, 49], [55, 25, 73], [97, 126, 4], [118, 87, 63], [176, 79, 7], [110, 53, 7], [245, 202, 39], [105, 229, 212]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66, 28], []]
 b := ![[], [122, 31, 193], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A269 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 269 3 where
 D := ![[113, 1], [224, 1], [154, 0, 201, 1]]; D' := ![[113, 1], [224, 1], [154, 0, 201, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8, 8, 8]
 n := ![1, 1, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P269P0
  | 1 => exact P269P1
  | 2 => exact P269P2

def C2690 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A269.D 0) 269 where
  n := 1
  w := ![![269, 0, 0, 0, 0], ![113, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C2691 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A269.D 1) 269 where
  n := 1
  w := ![![269, 0, 0, 0, 0], ![224, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C2692 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A269.D 2) 269 where
  n := 3
  w := ![![269, 0, 0, 0, 0], ![154, 0, 201, 5, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K269 : KummerData 269 ![I269N0, I269N1, I269N2] ![269, 269, 19465109] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A269
  C := by
    intro i
    match i with
    | 0 => exact C2690
    | 1 => exact C2691
    | 2 => exact C2692
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 269 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp271 : Fact (Nat.Prime 271) := {out := by norm_num}

def I271N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![271, 0, 0, 0, 0], ![111, 1, 0, 0, 0]] i)))

def I271N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![271, 0, 0, 0, 0], ![234, 1, 0, 0, 0]] i)))

def I271N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![271, 0, 0, 0, 0], ![162, 73, 197, 5, 0]] i)))

def P271P0 : CertificateIrreducibleZModOfList' 271 1 2 8 [111, 1] where
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
 g := ![![[], [83], [178], [77], [], [], [], [160, 1]]]
 h' := ![![[0, 1], [1], [25], [125], [211], [32], [158], [126], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P271P1 : CertificateIrreducibleZModOfList' 271 1 2 8 [234, 1] where
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
 g := ![![[], [22], [185], [129], [], [], [], [37, 1]]]
 h' := ![![[0, 1], [1], [70], [166], [20], [205], [196], [14], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P271P2 : CertificateIrreducibleZModOfList' 271 3 2 8 [162, 73, 197, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 123, 188], [63, 147, 83], [0, 1]]
 g := ![![[199, 121, 99], [170, 204, 212], [183, 136, 125], [149, 12, 233], [20, 241], [266, 18], [74, 1], []], ![[92, 195, 130, 149], [111, 73, 104, 234], [257, 102, 28, 172], [33, 81, 4, 111], [106, 242], [100, 211], [60, 200], [213, 114]], ![[10, 109, 242, 11], [173, 74, 27, 5], [10, 20, 122, 32], [184, 39, 42, 85], [149, 50], [61, 233], [189, 224], [47, 114]]]
 h' := ![![[11, 123, 188], [102, 137, 218], [164, 200, 235], [252, 205, 106], [254, 62, 49], [28, 163, 90], [207, 127, 254], [0, 0, 1], [0, 1]], ![[63, 147, 83], [184, 199, 79], [128, 46, 59], [208, 254, 193], [65, 201, 160], [94, 134, 243], [247, 217, 239], [32, 125, 147], [11, 123, 188]], ![[0, 1], [23, 206, 245], [83, 25, 248], [235, 83, 243], [79, 8, 62], [130, 245, 209], [255, 198, 49], [149, 146, 123], [63, 147, 83]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [166, 145], []]
 b := ![[], [19, 223, 165], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A271 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 271 3 where
 D := ![[111, 1], [234, 1], [162, 73, 197, 1]]; D' := ![[111, 1], [234, 1], [162, 73, 197, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8, 8, 8]
 n := ![1, 1, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P271P0
  | 1 => exact P271P1
  | 2 => exact P271P2

def C2710 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A271.D 0) 271 where
  n := 1
  w := ![![271, 0, 0, 0, 0], ![111, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C2711 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A271.D 1) 271 where
  n := 1
  w := ![![271, 0, 0, 0, 0], ![234, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C2712 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A271.D 2) 271 where
  n := 3
  w := ![![271, 0, 0, 0, 0], ![162, 73, 197, 5, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K271 : KummerData 271 ![I271N0, I271N1, I271N2] ![271, 271, 19902511] where
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

def I277N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![277, 0, 0, 0, 0], ![83, 1, 0, 0, 0]] i)))

def I277N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![277, 0, 0, 0, 0], ![230, 77, 221, 970, 10]] i)))

def P277P0 : CertificateIrreducibleZModOfList' 277 1 2 8 [83, 1] where
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
 g := ![![[], [], [10], [], [79], [], [], [194, 1]]]
 h' := ![![[0, 1], [1], [1], [248], [91], [165], [188], [241], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P277P1 : CertificateIrreducibleZModOfList' 277 4 2 8 [230, 77, 216, 194, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [122, 254, 156, 169], [107, 43, 272, 171], [131, 256, 126, 214], [0, 1]]
 g := ![![[91, 215, 272, 81], [137, 55, 211], [15, 238, 58, 30], [118, 119, 87], [131, 51, 201, 141], [51, 213, 241], [1], []], ![[140, 144, 7, 135, 101, 261], [142, 173, 76], [204, 73, 229, 75, 226, 146], [3, 274, 120], [129, 142, 225, 81, 149, 243], [5, 100, 169], [113, 273, 187], [239, 95, 30]], ![[251, 188, 233, 65, 12, 55], [271, 209, 70], [133, 268, 225, 59, 129, 230], [158, 100, 131], [74, 121, 247, 135, 73, 85], [268, 20, 237], [73, 227, 89], [243, 158, 156]], ![[190, 51, 145, 214, 152, 250], [50, 55, 161], [133, 158, 20, 96, 217, 69], [92, 266, 84], [185, 87, 206, 134, 257, 249], [171, 54, 276], [153, 60, 169], [3, 264, 91]]]
 h' := ![![[122, 254, 156, 169], [155, 211, 211, 9], [151, 50, 56, 225], [97, 46, 276, 108], [63, 149, 273, 126], [174, 231, 5, 124], [47, 200, 61, 83], [0, 0, 1], [0, 1]], ![[107, 43, 272, 171], [33, 205, 130, 125], [227, 258, 69, 82], [205, 112, 4, 132], [8, 238, 202, 216], [34, 166, 133, 90], [195, 179, 29, 13], [79, 117, 177, 43], [122, 254, 156, 169]], ![[131, 256, 126, 214], [85, 189, 222, 85], [190, 23, 219, 65], [137, 19, 151, 25], [81, 236, 168, 193], [188, 212, 165, 156], [67, 8, 142, 121], [156, 133, 242, 221], [107, 43, 272, 171]], ![[0, 1], [250, 226, 268, 58], [117, 223, 210, 182], [81, 100, 123, 12], [167, 208, 188, 19], [73, 222, 251, 184], [30, 167, 45, 60], [128, 27, 134, 13], [131, 256, 126, 214]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [15, 267, 118], []]
 b := ![[], [], [237, 73, 50, 137], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A277 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 277 2 where
 D := ![[83, 1], [230, 77, 216, 194, 1]]; D' := ![[83, 1], [230, 77, 216, 194, 1]]
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
  w := ![![277, 0, 0, 0, 0], ![83, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C2771 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A277.D 1) 277 where
  n := 4
  w := ![![277, 0, 0, 0, 0], ![230, 77, 221, 970, 10]]
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

def I281N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![281, 0, 0, 0, 0], ![68, 1, 0, 0, 0]] i)))

def I281N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![281, 0, 0, 0, 0], ![178, 1, 0, 0, 0]] i)))

def I281N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![281, 0, 0, 0, 0], ![66, 55, 35, 5, 0]] i)))

def P281P0 : CertificateIrreducibleZModOfList' 281 1 2 8 [68, 1] where
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
 g := ![![[], [], [], [195], [232], [], [], [213, 1]]]
 h' := ![![[0, 1], [1], [280], [228], [241], [90], [86], [128], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P281P1 : CertificateIrreducibleZModOfList' 281 1 2 8 [178, 1] where
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
 g := ![![[], [], [], [114], [63], [], [], [103, 1]]]
 h' := ![![[0, 1], [280], [228], [221], [26], [256], [265], [212], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P281P2 : CertificateIrreducibleZModOfList' 281 3 2 8 [66, 55, 35, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 197, 125], [207, 83, 156], [0, 1]]
 g := ![![[191, 212, 252], [71, 68], [122, 62], [11, 110, 20], [46, 176, 191], [23, 149], [246, 1], []], ![[51, 142, 125, 25], [112, 64], [175, 203], [144, 192, 0, 219], [105, 274, 208, 145], [199, 86], [115, 145], [26, 170]], ![[93, 228, 130, 20], [125, 265], [164, 40], [87, 135, 146, 118], [239, 227, 57, 181], [126, 261], [264, 31], [276, 170]]]
 h' := ![![[39, 197, 125], [99, 112, 231], [17, 27, 61], [117, 218, 129], [55, 87, 150], [78, 237, 219], [62, 173, 46], [0, 0, 1], [0, 1]], ![[207, 83, 156], [167, 69, 15], [134, 147, 8], [43, 191, 22], [50, 229, 2], [55, 251, 32], [87, 252, 153], [86, 187, 83], [39, 197, 125]], ![[0, 1], [214, 100, 35], [92, 107, 212], [111, 153, 130], [161, 246, 129], [232, 74, 30], [31, 137, 82], [186, 94, 197], [207, 83, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [187, 9], []]
 b := ![[], [15, 114, 200], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A281 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 281 3 where
 D := ![[68, 1], [178, 1], [66, 55, 35, 1]]; D' := ![[68, 1], [178, 1], [66, 55, 35, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8, 8, 8]
 n := ![1, 1, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P281P0
  | 1 => exact P281P1
  | 2 => exact P281P2

def C2810 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A281.D 0) 281 where
  n := 1
  w := ![![281, 0, 0, 0, 0], ![68, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C2811 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A281.D 1) 281 where
  n := 1
  w := ![![281, 0, 0, 0, 0], ![178, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C2812 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A281.D 2) 281 where
  n := 3
  w := ![![281, 0, 0, 0, 0], ![66, 55, 35, 5, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K281 : KummerData 281 ![I281N0, I281N1, I281N2] ![281, 281, 22188041] where
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

def I283N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![283, 0, 0, 0, 0], ![225, 1, 0, 0, 0]] i)))

def I283N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![283, 0, 0, 0, 0], ![93, 90, 231, 290, 10]] i)))

def P283P0 : CertificateIrreducibleZModOfList' 283 1 2 8 [225, 1] where
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
 g := ![![[], [161], [], [152], [42], [], [], [58, 1]]]
 h' := ![![[0, 1], [282], [151], [43], [172], [61], [175], [251], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P283P1 : CertificateIrreducibleZModOfList' 283 4 2 8 [93, 90, 226, 58, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [158, 28, 282, 53], [217, 278, 252, 209], [133, 259, 32, 21], [0, 1]]
 g := ![![[260, 34, 163, 100], [8, 216, 52, 93], [133, 168, 253], [140, 193, 159, 16], [107, 14, 58, 251], [185, 55, 251], [1], []], ![[226, 232, 188, 196, 238, 229], [30, 100, 190, 40, 146, 12], [211, 166, 117], [140, 230, 175, 123, 158, 128], [181, 246, 259, 137, 104, 39], [175, 220, 7], [8, 36, 269], [102, 263, 262]], ![[20, 223, 145, 64, 279, 102], [20, 94, 110, 38, 258, 255], [116, 140, 110], [149, 265, 12, 30, 103, 273], [29, 116, 228, 204, 62, 268], [204, 81, 4], [276, 203, 225], [130, 261, 99]], ![[114, 228, 215, 166, 196, 177], [68, 147, 274, 118, 65, 47], [138, 253, 215], [70, 51, 206, 12], [41, 229, 157, 123, 167, 128], [154, 143, 49], [12, 194, 165], [160, 104, 158]]]
 h' := ![![[158, 28, 282, 53], [105, 62, 1, 10], [87, 106, 92, 248], [281, 150, 99, 155], [237, 216, 242, 4], [217, 69, 126, 58], [190, 193, 57, 225], [0, 0, 1], [0, 1]], ![[217, 278, 252, 209], [201, 205, 124, 204], [168, 157, 55, 137], [84, 93, 4, 20], [240, 248, 193, 102], [96, 239, 52, 15], [33, 42, 270, 63], [196, 113, 130, 206], [158, 28, 282, 53]], ![[133, 259, 32, 21], [139, 138, 134, 11], [191, 144, 6, 132], [15, 51, 256, 26], [198, 268, 113, 177], [95, 197, 96, 52], [244, 217, 149, 2], [190, 62, 55, 15], [217, 278, 252, 209]], ![[0, 1], [22, 161, 24, 58], [13, 159, 130, 49], [31, 272, 207, 82], [14, 117, 18], [106, 61, 9, 158], [174, 114, 90, 276], [262, 108, 97, 62], [133, 259, 32, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [208, 282, 184], []]
 b := ![[], [], [143, 102, 49, 209], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A283 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 283 2 where
 D := ![[225, 1], [93, 90, 226, 58, 1]]; D' := ![[225, 1], [93, 90, 226, 58, 1]]
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
  w := ![![283, 0, 0, 0, 0], ![225, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C2831 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A283.D 1) 283 where
  n := 4
  w := ![![283, 0, 0, 0, 0], ![93, 90, 231, 290, 10]]
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

def I293N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![293, 0, 0, 0, 0], ![8, 1, 0, 0, 0]] i)))

def I293N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![293, 0, 0, 0, 0], ![109, 274, 44, 1425, 10]] i)))

def P293P0 : CertificateIrreducibleZModOfList' 293 1 2 8 [8, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [56], [], [], [36], [], [285, 1]]]
 h' := ![![[0, 1], [292], [138], [39], [25], [5], [287], [64], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P293P1 : CertificateIrreducibleZModOfList' 293 4 2 8 [109, 274, 39, 285, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 136, 61, 211], [39, 129, 265, 45], [224, 27, 260, 37], [0, 1]]
 g := ![![[169, 150, 251, 197], [282, 159, 161], [246, 261, 73, 292], [31, 234, 69], [17, 76, 6], [77, 191, 181, 64], [1], []], ![[3, 37, 6, 43, 274, 224], [62, 99, 178], [22, 105, 239, 246, 163, 107], [188, 110, 260], [289, 241, 191], [42, 136, 257, 290, 129, 137], [280, 169, 178], [44, 131, 278]], ![[17, 185, 77, 51, 142, 261], [274, 4, 186], [69, 230, 284, 114, 171, 183], [206, 154, 61], [161, 204, 172], [43, 84, 49, 236, 41, 249], [98, 6, 121], [81, 202, 267]], ![[277, 292, 171, 51, 239, 36], [57, 2, 289], [42, 165, 141, 182, 101, 6], [68, 140, 153], [260, 283, 121], [238, 250, 5, 34, 234, 54], [61, 248, 210], [196, 13, 197]]]
 h' := ![![[38, 136, 61, 211], [267, 60, 204, 256], [142, 128, 101, 109], [180, 67, 271, 138], [173, 101, 192, 77], [104, 143, 195, 251], [184, 19, 254, 8], [0, 0, 1], [0, 1]], ![[39, 129, 265, 45], [197, 23, 208, 97], [41, 239, 228, 44], [102, 169, 173, 100], [60, 74, 33, 201], [33, 165, 249, 271], [185, 42, 73, 219], [164, 116, 49, 44], [38, 136, 61, 211]], ![[224, 27, 260, 37], [14, 86, 26, 65], [229, 119, 256, 123], [207, 144, 238, 59], [10, 182, 13, 190], [255, 19, 0, 53], [155, 95, 46, 54], [17, 131, 97, 282], [39, 129, 265, 45]], ![[0, 1], [73, 124, 148, 168], [197, 100, 1, 17], [239, 206, 197, 289], [196, 229, 55, 118], [81, 259, 142, 11], [25, 137, 213, 12], [98, 46, 146, 260], [224, 27, 260, 37]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [77, 60, 189], []]
 b := ![[], [], [183, 28, 57, 113], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A293 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 293 2 where
 D := ![[8, 1], [109, 274, 39, 285, 1]]; D' := ![[8, 1], [109, 274, 39, 285, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8, 8]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P293P0
  | 1 => exact P293P1

def C2930 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A293.D 0) 293 where
  n := 1
  w := ![![293, 0, 0, 0, 0], ![8, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C2931 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A293.D 1) 293 where
  n := 4
  w := ![![293, 0, 0, 0, 0], ![109, 274, 44, 1425, 10]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K293 : KummerData 293 ![I293N0, I293N1] ![293, 7370050801] where
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

def I307N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![307, 0, 0, 0, 0], ![302, 217, 1, 0, 0]] i)))

def I307N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![307, 0, 0, 0, 0], ![60, 98, 90, 5, 0]] i)))

def P307P0 : CertificateIrreducibleZModOfList' 307 2 2 8 [302, 217, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [90, 306], [0, 1]]
 g := ![![[18, 184], [241, 144], [100], [134], [72, 6], [12, 133], [118], [1]], ![[0, 123], [0, 163], [100], [134], [305, 301], [9, 174], [118], [1]]]
 h' := ![![[90, 306], [284, 106], [159, 295], [102, 10], [53, 286], [60, 211], [1, 161], [5, 90], [0, 1]], ![[0, 1], [0, 201], [0, 12], [81, 297], [5, 21], [16, 96], [62, 146], [123, 217], [90, 306]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [129]]
 b := ![[], [14, 218]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P307P1 : CertificateIrreducibleZModOfList' 307 3 2 8 [60, 98, 90, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [234, 3, 172], [290, 303, 135], [0, 1]]
 g := ![![[211, 42, 209], [104, 20, 240], [35, 17], [151, 41], [115, 125, 274], [38, 32, 93], [217, 1], []], ![[134, 165, 91, 244], [115, 53, 28, 207], [149, 40], [19, 16], [18, 133, 163, 88], [210, 156, 187, 266], [167, 16], [162, 112]], ![[131, 287, 239, 81], [30, 113, 108, 42], [172, 169], [88, 24], [74, 253, 65, 64], [286, 158, 245, 196], [165, 9], [199, 112]]]
 h' := ![![[234, 3, 172], [207, 88, 142], [11, 115, 94], [283, 52, 18], [161, 233, 196], [176, 101, 261], [181, 164, 20], [0, 0, 1], [0, 1]], ![[290, 303, 135], [225, 214, 139], [66, 113, 63], [32, 301, 276], [229, 163, 303], [151, 103, 57], [164, 5, 191], [214, 298, 303], [234, 3, 172]], ![[0, 1], [227, 5, 26], [80, 79, 150], [283, 261, 13], [61, 218, 115], [225, 103, 296], [149, 138, 96], [15, 9, 3], [290, 303, 135]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [106, 76], []]
 b := ![[], [3, 167, 278], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A307 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 307 2 where
 D := ![[302, 217, 1], [60, 98, 90, 1]]; D' := ![[302, 217, 1], [60, 98, 90, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8, 8]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P307P0
  | 1 => exact P307P1

def C3070 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A307.D 0) 307 where
  n := 2
  w := ![![307, 0, 0, 0, 0], ![302, 217, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C3071 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A307.D 1) 307 where
  n := 3
  w := ![![307, 0, 0, 0, 0], ![60, 98, 90, 5, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K307 : KummerData 307 ![I307N0, I307N1] ![94249, 28934443] where
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


lemma PB1045I6_primes (p : ℕ) :
  p ∈ Set.range ![257, 263, 269, 271, 277, 281, 283, 293, 307] ↔ Nat.Prime p ∧ 251 < p ∧ p ≤ 307 := by
  rw [← List.mem_ofFn']
  convert primes_range 251 307 (by omega)
  decide

def PB1045I6 : PrimesBelowBoundCertificateInterval O 251 307 1045 where
  m := 9
  g := ![2, 2, 3, 3, 2, 3, 2, 2, 2]
  P := ![257, 263, 269, 271, 277, 281, 283, 293, 307]
  hP := PB1045I6_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I257N0, I257N1]
    · exact ![I263N0, I263N1]
    · exact ![I269N0, I269N1, I269N2]
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
    · exact ![269, 269, 19465109]
    · exact ![271, 271, 19902511]
    · exact ![277, 5887339441]
    · exact ![281, 281, 22188041]
    · exact ![283, 6414247921]
    · exact ![293, 7370050801]
    · exact ![94249, 28934443]
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
  β := ![I263N0, I269N0, I269N1, I271N0, I271N1, I277N0, I281N0, I281N1, I283N0, I293N0]
  Il := ![[], [I263N0], [I269N0, I269N1], [I271N0, I271N1], [I277N0], [I281N0, I281N1], [I283N0], [I293N0], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
