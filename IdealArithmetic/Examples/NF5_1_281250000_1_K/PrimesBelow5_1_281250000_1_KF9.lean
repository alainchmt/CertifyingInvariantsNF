
import IdealArithmetic.Examples.NF5_1_281250000_1_K.RI5_1_281250000_1_K
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 

instance hp421 : Fact (Nat.Prime 421) := {out := by norm_num}

def I421N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![421, 0, 0, 0, 0], ![421, 0, 0, 2105, 0]] i)))

def P421P0 : CertificateIrreducibleZModOfList' 421 5 2 8 [121, 250, 0, 396, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [346, 336, 120, 381, 188], [164, 48, 298, 147, 55], [402, 56, 202, 244, 221], [351, 401, 222, 70, 378], [0, 1]]
 g := ![![[105, 417, 390, 407, 75], [130, 222, 309, 394], [389, 57, 183, 207, 16], [15, 267, 198, 33], [317, 40, 377, 85], [373, 265, 178, 0, 204], [0, 1], []], ![[144, 111, 81, 359, 291, 347, 271, 250], [14, 83, 366, 26], [229, 347, 198, 256, 120, 254, 296, 264], [146, 402, 177, 21], [309, 34, 81, 225], [283, 402, 416, 302, 19, 365, 153, 47], [347, 238, 335, 27], [121, 48, 325, 331, 339, 37, 295, 29]], ![[363, 300, 197, 400, 412, 272, 33, 414], [182, 138, 121, 3], [112, 49, 43, 339, 286, 5, 27, 135], [288, 56, 70, 302], [30, 181, 73, 254], [376, 306, 420, 92, 404, 396, 294, 327], [274, 353, 3, 44], [44, 1, 158, 295, 314, 198, 297, 80]], ![[268, 165, 159, 43, 247, 382, 191, 62], [209, 220, 399, 192], [307, 347, 125, 269, 199, 160, 36, 391], [43, 381, 355, 395], [224, 197, 67, 146], [228, 376, 255, 267, 218, 24, 352, 242], [3, 281, 316, 35], [141, 23, 197, 10, 168, 172, 292, 263]], ![[227, 173, 272, 384, 171, 115, 14, 213], [374, 124, 52, 322], [99, 80, 114, 385, 176, 214, 393, 188], [384, 276, 112, 388], [219, 71, 102, 220], [269, 326, 157, 345, 16, 312, 357, 235], [367, 415, 71, 176], [67, 195, 116, 23, 205, 117, 128, 62]]]
 h' := ![![[346, 336, 120, 381, 188], [0, 411, 191, 190, 370], [83, 109, 233, 68, 123], [70, 3, 163, 289, 4], [193, 353, 146, 108, 36], [335, 143, 201, 95, 341], [0, 300, 171, 0, 25], [0, 0, 0, 1], [0, 1]], ![[164, 48, 298, 147, 55], [399, 48, 353, 41, 237], [82, 260, 292, 37, 187], [155, 133, 83, 112, 313], [113, 178, 381, 219, 159], [385, 72, 292, 292, 406], [45, 132, 289, 236, 211], [61, 120, 304, 260, 199], [346, 336, 120, 381, 188]], ![[402, 56, 202, 244, 221], [375, 66, 185, 410, 69], [103, 384, 55, 89, 74], [213, 4, 399, 15, 316], [99, 181, 303, 8, 57], [19, 291, 78, 230, 153], [80, 260, 128, 258, 32], [276, 70, 264, 16, 329], [164, 48, 298, 147, 55]], ![[351, 401, 222, 70, 378], [70, 315, 323, 369, 258], [283, 38, 420, 69, 250], [226, 388, 242, 322, 204], [142, 37, 118, 228, 371], [57, 95, 4, 93, 66], [93, 390, 43, 262, 74], [77, 302, 323, 95, 77], [402, 56, 202, 244, 221]], ![[0, 1], [166, 2, 211, 253, 329], [164, 51, 263, 158, 208], [416, 314, 376, 104, 5], [299, 93, 315, 279, 219], [191, 241, 267, 132, 297], [268, 181, 211, 86, 79], [7, 350, 372, 49, 237], [351, 401, 222, 70, 378]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [306, 285, 404, 285], [], [], []]
 b := ![[], [213, 242, 26, 326, 153], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A421 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 421 1 where
 D := ![[121, 250, 0, 396, 0, 1]]; D' := ![[121, 250, 0, 396, 0, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8]
 n := ![5]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P421P0

def C4210 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A421.D 0) 421 where
  n := 5
  w := ![![421, 0, 0, 0, 0], ![421, 0, 0, 2105, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K421 : KummerData 421 ![I421N0] ![13225450646101] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A421
  C := by
    intro i
    match i with
    | 0 => exact C4210
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 421 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp431 : Fact (Nat.Prime 431) := {out := by norm_num}

def I431N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![431, 0, 0, 0, 0], ![139, 1, 0, 0, 0]] i)))

def I431N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![431, 0, 0, 0, 0], ![326, 354, 1, 0, 0]] i)))

def I431N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![431, 0, 0, 0, 0], ![404, 369, 1, 0, 0]] i)))

def P431P0 : CertificateIrreducibleZModOfList' 431 1 2 8 [139, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [400], [242], [320], [], [160], [], [357, 292, 1]]]
 h' := ![![[0, 1], [430], [411], [344], [276], [172], [347], [373], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P431P1 : CertificateIrreducibleZModOfList' 431 2 2 8 [326, 354, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [77, 430], [0, 1]]
 g := ![![[403, 353], [353, 29], [18, 358], [301, 192], [125], [], [], [77, 1]], ![[0, 78], [0, 402], [0, 73], [0, 239], [125], [], [], [154, 430]]]
 h' := ![![[77, 430], [430, 28], [166, 93], [142, 334], [195, 143], [0, 388], [41], [327], [0, 1]], ![[0, 1], [0, 403], [0, 338], [0, 97], [0, 288], [137, 43], [41], [327], [77, 430]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [327]]
 b := ![[], [278, 379]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P431P2 : CertificateIrreducibleZModOfList' 431 2 2 8 [404, 369, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [62, 430], [0, 1]]
 g := ![![[130, 49], [63, 242], [147, 232], [191, 273], [388], [256, 298], [64], [62, 1]], ![[151, 382], [413, 189], [308, 199], [308, 158], [388], [199, 133], [64], [124, 430]]]
 h' := ![![[62, 430], [408, 7], [90, 87], [416, 374], [388, 370], [16, 41], [349, 27], [381, 423], [0, 1]], ![[0, 1], [411, 424], [312, 344], [330, 57], [54, 61], [403, 390], [299, 404], [316, 8], [62, 430]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [366]]
 b := ![[], [361, 183]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A431 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 431 3 where
 D := ![[139, 1], [326, 354, 1], [404, 369, 1]]; D' := ![[139, 1], [326, 354, 1], [404, 369, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8, 8, 8]
 n := ![1, 2, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P431P0
  | 1 => exact P431P1
  | 2 => exact P431P2

def C4310 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A431.D 0) 431 where
  n := 1
  w := ![![431, 0, 0, 0, 0], ![139, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C4311 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A431.D 1) 431 where
  n := 2
  w := ![![431, 0, 0, 0, 0], ![326, 354, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C4312 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A431.D 2) 431 where
  n := 2
  w := ![![431, 0, 0, 0, 0], ![404, 369, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K431 : KummerData 431 ![I431N0, I431N1, I431N2] ![431, 185761, 185761] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A431
  C := by
    intro i
    match i with
    | 0 => exact C4310
    | 1 => exact C4311
    | 2 => exact C4312
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 431 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp433 : Fact (Nat.Prime 433) := {out := by norm_num}

def I433N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![433, 0, 0, 0, 0], ![216, 195, 1, 0, 0]] i)))

def I433N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![433, 0, 0, 0, 0], ![167, 113, 238, 5, 0]] i)))

def P433P0 : CertificateIrreducibleZModOfList' 433 2 2 8 [216, 195, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [238, 432], [0, 1]]
 g := ![![[43, 431], [51], [53], [257], [306, 272], [171, 272], [425], [238, 1]], ![[0, 2], [51], [53], [257], [92, 161], [390, 161], [425], [43, 432]]]
 h' := ![![[238, 432], [401, 364], [67, 22], [372, 160], [153, 61], [302, 236], [301, 197], [119, 138], [0, 1]], ![[0, 1], [0, 69], [107, 411], [348, 273], [382, 372], [180, 197], [423, 236], [55, 295], [238, 432]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [180]]
 b := ![[], [115, 90]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P433P1 : CertificateIrreducibleZModOfList' 433 3 2 8 [167, 113, 238, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [267, 256, 248], [361, 176, 185], [0, 1]]
 g := ![![[71, 176, 9], [396, 271], [173, 198], [289, 143], [272, 367, 159], [383, 285, 99], [279, 354], [1]], ![[186, 2, 265, 84], [346, 316], [376, 269], [350, 128], [390, 63, 63, 185], [196, 84, 47, 238], [23, 198], [75, 156, 118, 134]], ![[401, 284, 408, 357], [409, 254], [111, 136], [177, 136], [75, 298, 280, 245], [379, 51, 216, 124], [324, 16], [259, 78, 261, 299]]]
 h' := ![![[267, 256, 248], [0, 242, 3], [336, 37, 245], [182, 59, 199], [41, 178, 409], [123, 353, 67], [348, 356, 146], [266, 320, 195], [0, 1]], ![[361, 176, 185], [50, 262, 357], [26, 173, 336], [116, 273, 294], [313, 3, 84], [85, 78, 179], [162, 237, 105], [381, 246, 234], [267, 256, 248]], ![[0, 1], [327, 362, 73], [251, 223, 285], [420, 101, 373], [231, 252, 373], [65, 2, 187], [310, 273, 182], [45, 300, 4], [361, 176, 185]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [86, 422], []]
 b := ![[], [423, 306, 344], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A433 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 433 2 where
 D := ![[216, 195, 1], [167, 113, 238, 1]]; D' := ![[216, 195, 1], [167, 113, 238, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8, 8]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P433P0
  | 1 => exact P433P1

def C4330 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A433.D 0) 433 where
  n := 2
  w := ![![433, 0, 0, 0, 0], ![216, 195, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C4331 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A433.D 1) 433 where
  n := 3
  w := ![![433, 0, 0, 0, 0], ![167, 113, 238, 5, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K433 : KummerData 433 ![I433N0, I433N1] ![187489, 81182737] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A433
  C := by
    intro i
    match i with
    | 0 => exact C4330
    | 1 => exact C4331
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 433 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp439 : Fact (Nat.Prime 439) := {out := by norm_num}

def I439N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![439, 0, 0, 0, 0], ![53, 1, 0, 0, 0]] i)))

def I439N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![439, 0, 0, 0, 0], ![404, 57, 1, 0, 0]] i)))

def I439N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![439, 0, 0, 0, 0], ![309, 329, 1, 0, 0]] i)))

def P439P0 : CertificateIrreducibleZModOfList' 439 1 2 8 [53, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [58], [14], [], [69], [18], [], [175, 386, 1]]]
 h' := ![![[0, 1], [438], [136], [392], [294], [363], [63], [383], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P439P1 : CertificateIrreducibleZModOfList' 439 2 2 8 [404, 57, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [382, 438], [0, 1]]
 g := ![![[36, 251], [214, 22], [40, 56], [286], [337, 251], [163, 7], [182], [382, 1]], ![[216, 188], [277, 417], [360, 383], [286], [78, 188], [203, 432], [182], [325, 438]]]
 h' := ![![[382, 438], [27, 290], [83, 30], [204, 94], [381, 116], [437, 290], [275, 274], [200, 211], [0, 1]], ![[0, 1], [179, 149], [129, 409], [114, 345], [354, 323], [150, 149], [22, 165], [26, 228], [382, 438]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50]]
 b := ![[], [54, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P439P2 : CertificateIrreducibleZModOfList' 439 2 2 8 [309, 329, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [110, 438], [0, 1]]
 g := ![![[271, 142], [335, 95], [368, 222], [103], [83, 402], [339, 16], [332], [110, 1]], ![[87, 297], [249, 344], [204, 217], [103], [403, 37], [343, 423], [332], [220, 438]]]
 h' := ![![[110, 438], [89, 153], [428, 360], [203, 77], [254, 295], [170, 29], [426, 4], [252, 377], [0, 1]], ![[0, 1], [237, 286], [79, 79], [332, 362], [218, 144], [287, 410], [427, 435], [17, 62], [110, 438]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [91]]
 b := ![[], [351, 265]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A439 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 439 3 where
 D := ![[53, 1], [404, 57, 1], [309, 329, 1]]; D' := ![[53, 1], [404, 57, 1], [309, 329, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8, 8, 8]
 n := ![1, 2, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P439P0
  | 1 => exact P439P1
  | 2 => exact P439P2

def C4390 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A439.D 0) 439 where
  n := 1
  w := ![![439, 0, 0, 0, 0], ![53, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C4391 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A439.D 1) 439 where
  n := 2
  w := ![![439, 0, 0, 0, 0], ![404, 57, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C4392 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A439.D 2) 439 where
  n := 2
  w := ![![439, 0, 0, 0, 0], ![309, 329, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K439 : KummerData 439 ![I439N0, I439N1, I439N2] ![439, 192721, 192721] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A439
  C := by
    intro i
    match i with
    | 0 => exact C4390
    | 1 => exact C4391
    | 2 => exact C4392
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 439 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp443 : Fact (Nat.Prime 443) := {out := by norm_num}

def I443N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![443, 0, 0, 0, 0], ![74, 19, 1, 0, 0]] i)))

def I443N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![443, 0, 0, 0, 0], ![415, 262, 424, 5, 0]] i)))

def P443P0 : CertificateIrreducibleZModOfList' 443 2 2 8 [74, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [424, 442], [0, 1]]
 g := ![![[114, 156], [121, 400], [138], [223, 184], [316, 432], [85, 36], [414], [424, 1]], ![[251, 287], [52, 43], [138], [271, 259], [82, 11], [287, 407], [414], [405, 442]]]
 h' := ![![[424, 442], [349, 158], [337, 20], [332, 32], [95, 339], [355, 163], [101, 6], [77, 287], [0, 1]], ![[0, 1], [5, 285], [400, 423], [167, 411], [299, 104], [359, 280], [430, 437], [383, 156], [424, 442]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [293]]
 b := ![[], [395, 368]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P443P1 : CertificateIrreducibleZModOfList' 443 3 2 8 [415, 262, 424, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [350, 227, 310], [112, 215, 133], [0, 1]]
 g := ![![[234, 329, 25], [332, 32, 339], [393, 183], [259, 232, 155], [100, 83, 365], [298, 410, 100], [4, 361], [1]], ![[365, 317, 65, 154], [440, 261, 165, 329], [319, 358], [189, 27, 377, 128], [19, 303, 432, 375], [280, 118, 65, 323], [230, 151], [308, 214, 79, 136]], ![[175, 378, 201, 163], [333, 302, 387, 201], [259, 331], [208, 8, 352, 196], [284, 253, 221, 301], [435, 334, 325, 325], [81, 270], [75, 144, 14, 307]]]
 h' := ![![[350, 227, 310], [436, 74, 5], [245, 389, 408], [164, 1, 230], [142, 59, 191], [370, 397, 113], [10, 147, 10], [28, 181, 19], [0, 1]], ![[112, 215, 133], [257, 251, 93], [431, 352, 100], [81, 139, 144], [326, 80, 436], [377, 297, 289], [188, 275, 319], [338, 4, 390], [350, 227, 310]], ![[0, 1], [320, 118, 345], [308, 145, 378], [431, 303, 69], [70, 304, 259], [119, 192, 41], [109, 21, 114], [60, 258, 34], [112, 215, 133]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51, 271], []]
 b := ![[], [380, 90, 52], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A443 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 443 2 where
 D := ![[74, 19, 1], [415, 262, 424, 1]]; D' := ![[74, 19, 1], [415, 262, 424, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8, 8]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P443P0
  | 1 => exact P443P1

def C4430 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A443.D 0) 443 where
  n := 2
  w := ![![443, 0, 0, 0, 0], ![74, 19, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C4431 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A443.D 1) 443 where
  n := 3
  w := ![![443, 0, 0, 0, 0], ![415, 262, 424, 5, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K443 : KummerData 443 ![I443N0, I443N1] ![196249, 86938307] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A443
  C := by
    intro i
    match i with
    | 0 => exact C4430
    | 1 => exact C4431
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 443 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp449 : Fact (Nat.Prime 449) := {out := by norm_num}

def I449N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![449, 0, 0, 0, 0], ![449, 0, 0, 2245, 0]] i)))

def P449P0 : CertificateIrreducibleZModOfList' 449 5 2 8 [149, 250, 0, 424, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [397, 116, 177, 170, 253], [281, 285, 303, 434, 284], [408, 405, 31, 27, 273], [261, 91, 387, 267, 88], [0, 1]]
 g := ![![[371, 341, 440, 382, 427], [324, 186, 132, 200], [168, 434, 320, 372], [347, 327, 287, 280], [168, 114, 28, 427], [51, 88], [25, 0, 1], []], ![[183, 266, 338, 380, 119, 324, 217, 50], [113, 50, 249, 400], [66, 331, 345, 357], [226, 301, 416, 409], [190, 411, 323, 288], [328, 282, 100, 439], [245, 99, 303, 119, 235, 183, 319, 361], [292, 349, 408, 24, 361, 391, 45, 194]], ![[303, 41, 285, 321, 322, 169, 64, 3], [326, 17, 71, 250], [253, 50, 36, 360], [190, 12, 443, 36], [347, 391, 200, 265], [202, 129, 411, 444], [409, 425, 342, 379, 154, 249, 18, 24], [179, 380, 441, 100, 167, 275, 196, 120]], ![[274, 132, 99, 153, 103, 124, 332, 440], [269, 330, 293, 186], [266, 275, 377, 196], [128, 215, 222, 57], [136, 170, 56, 242], [305, 309, 2, 379], [171, 277, 221, 308, 106, 241, 143, 251], [122, 335, 278, 350, 100, 313, 44, 431]], ![[97, 404, 439, 123, 238, 78, 169, 367], [165, 308, 120, 357], [203, 146, 256, 386], [311, 173, 38, 59], [158, 390, 18, 271], [419, 155, 142, 115], [260, 359, 441, 222, 216, 132, 350, 118], [19, 92, 206, 94, 322, 413, 9, 339]]]
 h' := ![![[397, 116, 177, 170, 253], [273, 279, 431, 358, 215], [147, 302, 376, 99, 300], [22, 431, 122, 115, 99], [156, 355, 292, 446, 27], [212, 33, 72, 353, 215], [316, 36, 300, 375], [0, 0, 0, 1], [0, 1]], ![[281, 285, 303, 434, 284], [323, 277, 285, 346, 333], [239, 420, 81, 5, 429], [252, 339, 392, 261, 220], [196, 12, 156, 315, 233], [332, 132, 233, 258, 360], [183, 403, 357, 358, 108], [423, 158, 438, 287, 326], [397, 116, 177, 170, 253]], ![[408, 405, 31, 27, 273], [189, 107, 247, 158, 20], [69, 421, 45, 1, 260], [299, 405, 62, 285, 312], [188, 2, 364, 225, 443], [433, 225, 405, 34, 135], [382, 309, 42, 130, 176], [77, 119, 413, 273, 302], [281, 285, 303, 434, 284]], ![[261, 91, 387, 267, 88], [274, 432, 293, 373, 54], [247, 222, 278, 58, 138], [255, 367, 80, 195, 435], [236, 28, 133, 239, 147], [276, 415, 366, 370, 119], [350, 115, 374, 138, 218], [7, 319, 22, 317, 202], [408, 405, 31, 27, 273]], ![[0, 1], [174, 252, 91, 112, 276], [441, 431, 118, 286, 220], [49, 254, 242, 42, 281], [251, 52, 402, 122, 48], [134, 93, 271, 332, 69], [83, 35, 274, 346, 396], [391, 302, 25, 20, 68], [261, 91, 387, 267, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 90, 435, 245], [], [], []]
 b := ![[], [187, 376, 56, 316, 338], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A449 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 449 1 where
 D := ![[149, 250, 0, 424, 0, 1]]; D' := ![[149, 250, 0, 424, 0, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8]
 n := ![5]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P449P0

def C4490 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A449.D 0) 449 where
  n := 5
  w := ![![449, 0, 0, 0, 0], ![449, 0, 0, 2245, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K449 : KummerData 449 ![I449N0] ![18248690477249] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A449
  C := by
    intro i
    match i with
    | 0 => exact C4490
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 449 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp457 : Fact (Nat.Prime 457) := {out := by norm_num}

def I457N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![457, 0, 0, 0, 0], ![53, 1, 0, 0, 0]] i)))

def I457N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![457, 0, 0, 0, 0], ![322, 59, 47, 2020, 10]] i)))

def P457P0 : CertificateIrreducibleZModOfList' 457 1 2 8 [53, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [116], [], [], [57], [67, 404, 1]]]
 h' := ![![[0, 1], [456], [348], [250], [408], [151], [178], [105], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P457P1 : CertificateIrreducibleZModOfList' 457 4 2 8 [322, 59, 42, 404, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [262, 88, 147, 313], [436, 281, 332, 213], [269, 87, 435, 388], [0, 1]]
 g := ![![[354, 343, 301, 67], [352, 83, 394], [198, 86, 294], [197, 100, 295, 225], [93, 269, 252], [343, 68, 326], [411, 25, 53, 1], []], ![[322, 414, 380, 282, 51, 286], [229, 257, 313], [227, 121, 261], [77, 365, 235, 35, 127, 292], [308, 227, 349], [94, 368, 157], [104, 352, 295, 67, 28, 107], [3, 109, 258, 249, 126, 54]], ![[355, 63, 147, 141, 369, 411], [410, 35, 242], [193, 308, 98], [427, 125, 50, 257, 350, 187], [265, 191, 55], [26, 93, 220], [193, 209, 222, 111, 257, 5], [207, 288, 195, 217, 51, 332]], ![[208, 68, 374, 113, 87, 368], [156, 164, 310], [1, 430, 205], [170, 409, 278, 199, 203, 387], [310, 72, 16], [208, 57, 17], [302, 206, 353, 36, 6, 33], [267, 88, 29, 428, 456, 74]]]
 h' := ![![[262, 88, 147, 313], [155, 276, 160, 404], [376, 38, 353, 401], [89, 396, 316, 311], [168, 402, 83, 442], [303, 262, 346, 131], [188, 148, 300, 375], [0, 0, 0, 1], [0, 1]], ![[436, 281, 332, 213], [321, 217, 447, 12], [5, 234, 88, 63], [117, 297, 171, 155], [207, 189, 239, 376], [118, 312, 2, 231], [173, 156, 179, 385], [355, 52, 264, 220], [262, 88, 147, 313]], ![[269, 87, 435, 388], [17, 173, 226, 397], [260, 377, 74, 34], [305, 62, 207, 103], [137, 246, 184, 28], [297, 328, 206, 91], [427, 262, 254, 275], [404, 383, 143, 439], [436, 281, 332, 213]], ![[0, 1], [234, 248, 81, 101], [14, 265, 399, 416], [172, 159, 220, 345], [151, 77, 408, 68], [227, 12, 360, 4], [350, 348, 181, 336], [50, 22, 50, 254], [269, 87, 435, 388]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [290, 180], []]
 b := ![[], [], [116, 225, 218], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A457 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 457 2 where
 D := ![[53, 1], [322, 59, 42, 404, 1]]; D' := ![[53, 1], [322, 59, 42, 404, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8, 8]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P457P0
  | 1 => exact P457P1

def C4570 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A457.D 0) 457 where
  n := 1
  w := ![![457, 0, 0, 0, 0], ![53, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C4571 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A457.D 1) 457 where
  n := 4
  w := ![![457, 0, 0, 0, 0], ![322, 59, 47, 2020, 10]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K457 : KummerData 457 ![I457N0, I457N1] ![457, 43617904801] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A457
  C := by
    intro i
    match i with
    | 0 => exact C4570
    | 1 => exact C4571
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 457 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp461 : Fact (Nat.Prime 461) := {out := by norm_num}

def I461N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![461, 0, 0, 0, 0], ![461, 0, 0, 2305, 0]] i)))

def P461P0 : CertificateIrreducibleZModOfList' 461 5 2 8 [161, 250, 0, 436, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [358, 103, 57, 407, 424], [439, 97, 231, 114, 28], [170, 20, 97, 342, 346], [416, 240, 76, 59, 124], [0, 1]]
 g := ![![[35, 258, 240, 111, 165], [34, 75, 180, 97], [363, 117, 97, 201, 266], [205, 15, 413, 79, 318], [70, 116, 188, 166], [32, 20], [25, 0, 1], []], ![[253, 205, 437, 83, 229, 372, 237, 409], [398, 163, 116, 109], [299, 280, 265, 150, 428, 69, 364, 116], [383, 143, 439, 2, 365, 438, 369, 257], [51, 115, 276, 198], [252, 316, 429, 405], [265, 249, 138, 281, 211, 39, 116, 415], [122, 24, 199, 362, 132, 360, 424, 57]], ![[128, 63, 226, 33, 136, 388, 436, 326], [105, 135, 304, 331], [28, 272, 159, 447, 307, 222, 118, 135], [153, 34, 169, 352, 372, 141, 249, 185], [112, 19, 314, 397], [125, 200, 61, 198], [226, 440, 48, 92, 74, 69, 109, 271], [12, 31, 199, 174, 455, 19, 287, 285]], ![[164, 202, 33, 353, 394, 392, 150, 455], [344, 31, 43, 455], [352, 453, 350, 177, 73, 224, 290, 1], [154, 453, 403, 198, 81, 100, 162, 102], [33, 270, 356, 380], [42, 123, 166, 163], [413, 269, 313, 290, 428, 453, 273, 455], [208, 165, 227, 426, 281, 202, 237, 425]], ![[118, 453, 254, 278, 216, 364, 179, 337], [39, 419, 70, 437], [0, 21, 231, 8, 307, 195, 355, 162], [113, 386, 378, 411, 445, 285, 311, 173], [140, 313, 46, 455], [222, 96, 167, 268], [203, 33, 245, 237, 194, 107, 41, 314], [171, 414, 45, 127, 149, 311, 269, 389]]]
 h' := ![![[358, 103, 57, 407, 424], [271, 113, 41, 459, 318], [104, 64, 159, 205, 349], [187, 219, 135, 217, 95], [64, 24, 24, 327, 170], [82, 187, 376, 452, 92], [124, 204, 300, 375], [0, 0, 0, 1], [0, 1]], ![[439, 97, 231, 114, 28], [237, 150, 165, 389, 257], [202, 64, 280, 85, 120], [22, 106, 74, 185, 341], [438, 359, 446, 98, 115], [93, 403, 353, 258, 290], [349, 418, 138, 87, 74], [24, 221, 318, 25, 65], [358, 103, 57, 407, 424]], ![[170, 20, 97, 342, 346], [294, 440, 366, 364, 188], [271, 97, 232, 102, 119], [108, 269, 145, 134, 196], [424, 155, 135, 112, 325], [457, 132, 31, 441, 384], [420, 349, 19, 47, 290], [328, 85, 95, 419, 417], [439, 97, 231, 114, 28]], ![[416, 240, 76, 59, 124], [151, 365, 147, 348, 207], [435, 229, 360, 198, 127], [10, 14, 315, 156, 459], [233, 157, 30, 341, 64], [68, 134, 47, 181, 29], [225, 460, 177, 49, 124], [288, 445, 227, 416, 207], [170, 20, 97, 342, 346]], ![[0, 1], [355, 315, 203, 284, 413], [203, 7, 352, 332, 207], [221, 314, 253, 230, 292], [449, 227, 287, 44, 248], [20, 66, 115, 51, 127], [211, 413, 288, 364, 434], [282, 171, 282, 61, 233], [416, 240, 76, 59, 124]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [456, 258, 187, 329], [], [], []]
 b := ![[], [301, 85, 19, 215, 283], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A461 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 461 1 where
 D := ![[161, 250, 0, 436, 0, 1]]; D' := ![[161, 250, 0, 436, 0, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8]
 n := ![5]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P461P0

def C4610 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A461.D 0) 461 where
  n := 5
  w := ![![461, 0, 0, 0, 0], ![461, 0, 0, 2305, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K461 : KummerData 461 ![I461N0] ![20821145878301] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A461
  C := by
    intro i
    match i with
    | 0 => exact C4610
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 461 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp463 : Fact (Nat.Prime 463) := {out := by norm_num}

def I463N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![463, 0, 0, 0, 0], ![212, 1, 0, 0, 0]] i)))

def I463N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![463, 0, 0, 0, 0], ![51, 156, 13, 1255, 10]] i)))

def P463P0 : CertificateIrreducibleZModOfList' 463 1 2 8 [212, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [190], [230], [441], [], [], [286], [33, 251, 1]]]
 h' := ![![[0, 1], [1], [318], [34], [21], [441], [21], [412], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P463P1 : CertificateIrreducibleZModOfList' 463 4 2 8 [51, 156, 8, 251, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [143, 245, 189, 10], [39, 399, 131, 169], [30, 281, 143, 284], [0, 1]]
 g := ![![[206, 213, 386, 228], [119, 218, 122, 209], [428, 375, 91, 367], [327, 127, 132, 15], [456, 351, 140], [44, 375, 336], [207, 25, 212, 1], []], ![[143, 36, 88, 122, 230, 291], [166, 199, 35, 91, 359, 372], [266, 105, 90, 225, 40, 432], [240, 100, 328, 300, 316, 408], [216, 56, 61], [14, 94, 418], [133, 419, 193, 209, 151, 442], [212, 414, 232, 123, 160, 74]], ![[283, 2, 401, 210, 373, 255], [154, 251, 173, 77, 216, 411], [68, 85, 204, 114, 382, 64], [339, 413, 189, 302, 130, 181], [204, 250, 79], [399, 7, 161], [210, 259, 11, 199, 29, 122], [104, 284, 222, 154, 227, 34]], ![[157, 97, 118, 45, 299, 51], [380, 295, 104, 416, 47, 257], [361, 42, 45, 25, 365, 245], [253, 82, 378, 101, 436, 343], [435, 153, 251], [381, 108, 43], [246, 137, 3, 158, 290, 296], [384, 258, 345, 424, 348, 305]]]
 h' := ![![[143, 245, 189, 10], [413, 272, 228, 368], [396, 306, 280, 270], [454, 119, 62, 191], [14, 283, 17, 101], [201, 31, 163, 62], [92, 232, 300, 375], [0, 0, 0, 1], [0, 1]], ![[39, 399, 131, 169], [248, 425, 4, 328], [42, 368, 339, 93], [393, 279, 68, 28], [335, 362, 67, 221], [166, 365, 54, 138], [152, 47, 433, 287], [199, 94, 326, 67], [143, 245, 189, 10]], ![[30, 281, 143, 284], [46, 145, 338, 189], [314, 417, 245, 326], [260, 194, 294, 35], [205, 146, 39, 49], [360, 165, 304, 81], [356, 425, 252, 376], [307, 434, 75, 18], [39, 399, 131, 169]], ![[0, 1], [228, 84, 356, 41], [431, 298, 62, 237], [155, 334, 39, 209], [118, 135, 340, 92], [81, 365, 405, 182], [23, 222, 404, 351], [8, 398, 62, 377], [30, 281, 143, 284]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [281, 449, 268], []]
 b := ![[], [], [333, 126, 69, 108], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A463 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 463 2 where
 D := ![[212, 1], [51, 156, 8, 251, 1]]; D' := ![[212, 1], [51, 156, 8, 251, 1]]
 heqm := by decide
 hProd := by decide
 s := ![8, 8]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P463P0
  | 1 => exact P463P1

def C4630 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A463.D 0) 463 where
  n := 1
  w := ![![463, 0, 0, 0, 0], ![212, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C4631 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A463.D 1) 463 where
  n := 4
  w := ![![463, 0, 0, 0, 0], ![51, 156, 13, 1255, 10]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K463 : KummerData 463 ![I463N0, I463N1] ![463, 45954068161] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A463
  C := by
    intro i
    match i with
    | 0 => exact C4630
    | 1 => exact C4631
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 463 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


lemma PB1045I9_primes (p : ℕ) :
  p ∈ Set.range ![421, 431, 433, 439, 443, 449, 457, 461, 463] ↔ Nat.Prime p ∧ 419 < p ∧ p ≤ 463 := by
  rw [← List.mem_ofFn']
  convert primes_range 419 463 (by omega)
  decide

def PB1045I9 : PrimesBelowBoundCertificateInterval O 419 463 1045 where
  m := 9
  g := ![1, 3, 2, 3, 2, 1, 2, 1, 2]
  P := ![421, 431, 433, 439, 443, 449, 457, 461, 463]
  hP := PB1045I9_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I421N0]
    · exact ![I431N0, I431N1, I431N2]
    · exact ![I433N0, I433N1]
    · exact ![I439N0, I439N1, I439N2]
    · exact ![I443N0, I443N1]
    · exact ![I449N0]
    · exact ![I457N0, I457N1]
    · exact ![I461N0]
    · exact ![I463N0, I463N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · convert (containsPrimesAbove_of_KummerData K421) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K431) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K433) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K439) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K443) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K449) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K457) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K461) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K463) <;> rfl
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![13225450646101]
    · exact ![431, 185761, 185761]
    · exact ![187489, 81182737]
    · exact ![439, 192721, 192721]
    · exact ![196249, 86938307]
    · exact ![18248690477249]
    · exact ![457, 43617904801]
    · exact ![20821145878301]
    · exact ![463, 45954068161]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact (card_quot_of_KummerData K421)
    · exact (card_quot_of_KummerData K431)
    · exact (card_quot_of_KummerData K433)
    · exact (card_quot_of_KummerData K439)
    · exact (card_quot_of_KummerData K443)
    · exact (card_quot_of_KummerData K449)
    · exact (card_quot_of_KummerData K457)
    · exact (card_quot_of_KummerData K461)
    · exact (card_quot_of_KummerData K463)
  β := ![I431N0, I439N0, I457N0, I463N0]
  Il := ![[], [I431N0], [], [I439N0], [], [], [I457N0], [], [I463N0]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
