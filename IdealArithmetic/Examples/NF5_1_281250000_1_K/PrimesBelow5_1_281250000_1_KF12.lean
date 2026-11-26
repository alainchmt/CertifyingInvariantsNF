
import IdealArithmetic.Examples.NF5_1_281250000_1_K.RI5_1_281250000_1_K
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 

instance hp599 : Fact (Nat.Prime 599) := {out := by norm_num}

def I599N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![599, 0, 0, 0, 0], ![577, 1, 0, 0, 0]] i)))

def I599N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![599, 0, 0, 0, 0], ![27, 56, 1, 0, 0]] i)))

def I599N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![599, 0, 0, 0, 0], ![539, 565, 1, 0, 0]] i)))

def P599P0 : CertificateIrreducibleZModOfList' 599 1 2 9 [577, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [245], [424], [], [106], [], [412], [], [22, 1]]]
 h' := ![![[0, 1], [598], [343], [502], [535], [251], [79], [47], [484], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P599P1 : CertificateIrreducibleZModOfList' 599 2 2 9 [27, 56, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [543, 598], [0, 1]]
 g := ![![[113, 355], [31, 161], [380, 64], [456], [330, 511], [9], [503, 410], [141], [1]], ![[0, 244], [0, 438], [390, 535], [456], [466, 88], [9], [305, 189], [141], [1]]]
 h' := ![![[543, 598], [361, 445], [522, 373], [501, 591], [75, 282], [436, 117], [196, 596], [516, 519], [572, 543], [0, 1]], ![[0, 1], [0, 154], [0, 226], [350, 8], [456, 317], [473, 482], [364, 3], [204, 80], [114, 56], [543, 598]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [254]]
 b := ![[], [561, 127]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P599P2 : CertificateIrreducibleZModOfList' 599 2 2 9 [539, 565, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 598], [0, 1]]
 g := ![![[340, 347], [78, 508], [469, 204], [361], [46, 221], [541], [27, 245], [557], [1]], ![[158, 252], [578, 91], [217, 395], [361], [372, 378], [541], [570, 354], [557], [1]]]
 h' := ![![[34, 598], [487, 356], [586, 477], [213, 349], [364, 19], [295, 497], [422, 191], [481, 256], [60, 34], [0, 1]], ![[0, 1], [12, 243], [32, 122], [99, 250], [411, 580], [421, 102], [327, 408], [200, 343], [18, 565], [34, 598]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [242]]
 b := ![[], [339, 121]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A599 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 599 3 where
 D := ![[577, 1], [27, 56, 1], [539, 565, 1]]; D' := ![[577, 1], [27, 56, 1], [539, 565, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9, 9]
 n := ![1, 2, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P599P0
  | 1 => exact P599P1
  | 2 => exact P599P2

def C5990 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A599.D 0) 599 where
  n := 1
  w := ![![599, 0, 0, 0, 0], ![577, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C5991 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A599.D 1) 599 where
  n := 2
  w := ![![599, 0, 0, 0, 0], ![27, 56, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C5992 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A599.D 2) 599 where
  n := 2
  w := ![![599, 0, 0, 0, 0], ![539, 565, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K599 : KummerData 599 ![I599N0, I599N1, I599N2] ![599, 358801, 358801] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A599
  C := by
    intro i
    match i with
    | 0 => exact C5990
    | 1 => exact C5991
    | 2 => exact C5992
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 599 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp601 : Fact (Nat.Prime 601) := {out := by norm_num}

def I601N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![601, 0, 0, 0, 0], ![601, 0, 0, 3005, 0]] i)))

def P601P0 : CertificateIrreducibleZModOfList' 601 5 2 9 [301, 250, 0, 576, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [226, 301, 574, 161, 73], [279, 595, 58, 58, 91], [416, 64, 111, 100, 282], [281, 241, 459, 282, 155], [0, 1]]
 g := ![![[149, 240, 201, 368, 588], [52, 256, 397, 300], [187, 581, 449, 281], [81, 75, 591, 471, 462], [281, 202, 259, 336, 294], [4, 145, 481, 451], [375, 0, 25, 0, 1], [], []], ![[342, 583, 146, 199, 292, 596, 326, 326], [167, 417, 266, 36], [571, 395, 14, 94], [265, 246, 357, 191, 335, 584, 524, 43], [174, 193, 295, 237, 34, 337, 176, 232], [312, 501, 505, 345], [379, 362, 72, 351, 512, 103, 176, 440], [295, 212, 377, 358], [266, 146, 67, 521]], ![[473, 527, 51, 50, 162, 111, 118, 99], [238, 110, 371, 148], [222, 273, 52, 235], [414, 366, 453, 172, 496, 116, 48, 538], [175, 441, 175, 537, 394, 484, 468, 247], [600, 232, 357, 585], [428, 41, 154, 381, 535, 320, 455, 568], [188, 215, 300, 196], [288, 378, 339, 468]], ![[76, 543, 410, 521, 59, 157, 113, 585], [316, 498, 570, 505], [258, 272, 303, 293], [250, 371, 455, 340, 33, 255, 382, 262], [574, 11, 531, 575, 279, 299, 503, 462], [583, 15, 130, 36], [462, 476, 85, 410, 496, 316, 108, 169], [83, 267, 332, 521], [53, 476, 507, 192]], ![[201, 251, 266, 411, 371, 411, 294, 415], [3, 41, 591, 493], [485, 8, 588, 385], [2, 291, 71, 390, 203, 119, 469, 285], [197, 431, 79, 278, 567, 60, 34, 428], [240, 120, 224, 47], [145, 82, 332, 263, 95, 179, 511, 420], [174, 398, 8, 585], [295, 271, 275, 586]]]
 h' := ![![[226, 301, 574, 161, 73], [392, 146, 583, 412, 193], [495, 442, 246, 391, 52], [260, 204, 195, 371, 455], [160, 247, 600, 563, 492], [146, 584, 86, 50, 388], [113, 6, 288, 120, 300], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[279, 595, 58, 58, 91], [330, 261, 121, 92, 503], [82, 142, 397, 78, 595], [527, 290, 280, 284, 36], [401, 85, 113, 310, 236], [549, 315, 431, 234, 347], [478, 212, 466, 375, 197], [484, 63, 24, 291, 275], [459, 364, 94, 181, 441], [226, 301, 574, 161, 73]], ![[416, 64, 111, 100, 282], [19, 74, 61, 116, 389], [464, 175, 413, 368, 488], [175, 569, 511, 220, 93], [284, 530, 199, 580, 137], [355, 146, 454, 569, 178], [263, 96, 475, 507, 500], [484, 470, 513, 219, 57], [168, 189, 535, 161, 587], [279, 595, 58, 58, 91]], ![[281, 241, 459, 282, 155], [315, 404, 102, 21, 447], [231, 309, 290, 412, 361], [31, 146, 67, 438, 377], [72, 463, 530, 416, 51], [376, 54, 452, 453, 190], [76, 297, 199, 490, 595], [526, 272, 321, 298, 359], [242, 94, 333, 134, 73], [416, 64, 111, 100, 282]], ![[0, 1], [174, 317, 335, 561, 271], [59, 134, 457, 554, 307], [1, 594, 149, 490, 241], [229, 478, 361, 535, 286], [237, 103, 380, 497, 99], [87, 591, 375, 311, 211], [559, 397, 344, 394, 510], [383, 555, 239, 125, 101], [281, 241, 459, 282, 155]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 569, 533, 576], [], [], []]
 b := ![[], [121, 83, 118, 131, 165], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A601 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 601 1 where
 D := ![[301, 250, 0, 576, 0, 1]]; D' := ![[301, 250, 0, 576, 0, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9]
 n := ![5]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P601P0

def C6010 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A601.D 0) 601 where
  n := 5
  w := ![![601, 0, 0, 0, 0], ![601, 0, 0, 3005, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K601 : KummerData 601 ![I601N0] ![78410163603001] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A601
  C := by
    intro i
    match i with
    | 0 => exact C6010
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 601 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp607 : Fact (Nat.Prime 607) := {out := by norm_num}

def I607N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![607, 0, 0, 0, 0], ![17, 590, 1, 0, 0]] i)))

def I607N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![607, 0, 0, 0, 0], ![268, 247, 17, 5, 0]] i)))

def P607P0 : CertificateIrreducibleZModOfList' 607 2 2 9 [17, 590, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 606], [0, 1]]
 g := ![![[606, 467], [428, 329], [412, 244], [285, 586], [321, 25], [498], [532, 112], [289], [1]], ![[47, 140], [558, 278], [311, 363], [535, 21], [139, 582], [498], [8, 495], [289], [1]]]
 h' := ![![[17, 606], [8, 566], [280, 549], [11, 382], [6, 357], [111, 5], [61, 264], [232, 86], [590, 17], [0, 1]], ![[0, 1], [525, 41], [508, 58], [435, 225], [5, 250], [196, 602], [300, 343], [480, 521], [272, 590], [17, 606]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [390]]
 b := ![[], [467, 195]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P607P1 : CertificateIrreducibleZModOfList' 607 3 2 9 [268, 247, 17, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [563, 412, 593], [27, 194, 14], [0, 1]]
 g := ![![[127, 287, 334], [267, 27, 61], [70, 587, 178], [205, 38, 310], [349, 97, 444], [327, 309], [151, 358, 550], [590, 1], []], ![[330, 248, 293, 141], [88, 416, 9, 419], [290, 359, 364, 414], [436, 598, 223, 319], [87, 131, 284, 95], [243, 91], [16, 518, 156, 367], [483, 2], [307, 196]], ![[308, 139, 591, 193], [317, 145, 503, 22], [294, 363, 9, 423], [346, 181, 265, 511], [39, 605, 383, 511], [141, 289], [32, 211, 349, 172], [315, 391], [279, 196]]]
 h' := ![![[563, 412, 593], [70, 476, 290], [57, 404, 416], [297, 369, 389], [553, 277, 106], [111, 86, 415], [201, 463, 360], [307, 289, 42], [0, 0, 1], [0, 1]], ![[27, 194, 14], [252, 403, 429], [471, 434, 387], [192, 72, 495], [68, 459, 297], [165, 39, 396], [403, 281, 230], [371, 80, 460], [391, 491, 194], [563, 412, 593]], ![[0, 1], [330, 335, 495], [366, 376, 411], [578, 166, 330], [93, 478, 204], [321, 482, 403], [273, 470, 17], [74, 238, 105], [11, 116, 412], [27, 194, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [430, 477], []]
 b := ![[], [398, 263, 511], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A607 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 607 2 where
 D := ![[17, 590, 1], [268, 247, 17, 1]]; D' := ![[17, 590, 1], [268, 247, 17, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P607P0
  | 1 => exact P607P1

def C6070 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A607.D 0) 607 where
  n := 2
  w := ![![607, 0, 0, 0, 0], ![17, 590, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C6071 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A607.D 1) 607 where
  n := 3
  w := ![![607, 0, 0, 0, 0], ![268, 247, 17, 5, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K607 : KummerData 607 ![I607N0, I607N1] ![368449, 223648543] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A607
  C := by
    intro i
    match i with
    | 0 => exact C6070
    | 1 => exact C6071
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 607 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp613 : Fact (Nat.Prime 613) := {out := by norm_num}

def I613N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![613, 0, 0, 0, 0], ![595, 528, 1, 0, 0]] i)))

def I613N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![613, 0, 0, 0, 0], ![221, 475, 85, 5, 0]] i)))

def P613P0 : CertificateIrreducibleZModOfList' 613 2 2 9 [595, 528, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [85, 612], [0, 1]]
 g := ![![[175, 169], [425], [477, 28], [566], [183], [101, 299], [275, 202], [482], [1]], ![[441, 444], [425], [405, 585], [566], [183], [383, 314], [281, 411], [482], [1]]]
 h' := ![![[85, 612], [310, 600], [4, 540], [564, 426], [57, 270], [592, 145], [46, 58], [418, 507], [18, 85], [0, 1]], ![[0, 1], [431, 13], [542, 73], [607, 187], [326, 343], [44, 468], [72, 555], [603, 106], [500, 528], [85, 612]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [478]]
 b := ![[], [570, 239]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P613P1 : CertificateIrreducibleZModOfList' 613 3 2 9 [221, 475, 85, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [450, 603, 407], [78, 9, 206], [0, 1]]
 g := ![![[586, 306, 606], [63, 418], [134, 269, 596], [195, 474], [373, 12], [4, 106, 158], [299, 161, 49], [528, 1], []], ![[200, 322, 315, 481], [224, 421], [190, 203, 267, 319], [236, 567], [488, 369], [577, 563, 196, 209], [499, 506, 328, 117], [473, 81], [274, 139]], ![[156, 294, 306, 32], [549, 329], [300, 42, 101, 366], [78, 333], [525, 523], [151, 550, 139, 92], [573, 149, 188, 452], [561, 100], [475, 139]]]
 h' := ![![[450, 603, 407], [109, 277, 514], [423, 484, 64], [566, 150, 511], [203, 23, 467], [342, 107, 588], [125, 487, 209], [395, 309, 7], [0, 0, 1], [0, 1]], ![[78, 9, 206], [78, 284, 282], [492, 3, 178], [591, 532, 58], [320, 503, 78], [72, 17, 414], [400, 534, 252], [243, 112, 161], [343, 545, 9], [450, 603, 407]], ![[0, 1], [246, 52, 430], [370, 126, 371], [586, 544, 44], [255, 87, 68], [152, 489, 224], [407, 205, 152], [430, 192, 445], [415, 68, 603], [78, 9, 206]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [381, 271], []]
 b := ![[], [494, 177, 40], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A613 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 613 2 where
 D := ![[595, 528, 1], [221, 475, 85, 1]]; D' := ![[595, 528, 1], [221, 475, 85, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P613P0
  | 1 => exact P613P1

def C6130 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A613.D 0) 613 where
  n := 2
  w := ![![613, 0, 0, 0, 0], ![595, 528, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C6131 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A613.D 1) 613 where
  n := 3
  w := ![![613, 0, 0, 0, 0], ![221, 475, 85, 5, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K613 : KummerData 613 ![I613N0, I613N1] ![375769, 230346397] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A613
  C := by
    intro i
    match i with
    | 0 => exact C6130
    | 1 => exact C6131
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 613 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp617 : Fact (Nat.Prime 617) := {out := by norm_num}

def I617N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![617, 0, 0, 0, 0], ![498, 5, 1, 0, 0]] i)))

def I617N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![617, 0, 0, 0, 0], ![44, 119, 612, 5, 0]] i)))

def P617P0 : CertificateIrreducibleZModOfList' 617 2 2 9 [498, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [612, 616], [0, 1]]
 g := ![![[534, 94], [77], [43], [143, 159], [338], [295, 137], [364, 391], [25], [1]], ![[64, 523], [77], [43], [582, 458], [338], [227, 480], [260, 226], [25], [1]]]
 h' := ![![[612, 616], [606, 347], [9, 452], [358, 443], [511, 339], [553, 471], [126, 141], [477, 536], [119, 612], [0, 1]], ![[0, 1], [105, 270], [217, 165], [611, 174], [50, 278], [49, 146], [38, 476], [265, 81], [144, 5], [612, 616]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [383]]
 b := ![[], [16, 500]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P617P1 : CertificateIrreducibleZModOfList' 617 3 2 9 [44, 119, 612, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [230, 64, 109], [392, 552, 508], [0, 1]]
 g := ![![[135, 413, 198], [230, 126], [317, 460], [406, 53, 376], [78, 99], [82, 430, 194], [105, 190, 198], [5, 1], []], ![[589, 491, 544, 57], [525, 72], [395, 28], [492, 592, 317, 10], [159, 502], [546, 368, 398, 466], [135, 331, 306, 411], [168, 523], [551, 158]], ![[267, 478, 353, 584], [227, 67], [21, 340], [521, 199, 88, 380], [482, 276], [54, 327, 334, 402], [301, 520, 598, 295], [358, 394], [152, 158]]]
 h' := ![![[230, 64, 109], [40, 184, 94], [467, 83, 176], [29, 554, 383], [468, 521, 77], [94, 223, 338], [316, 397, 478], [397, 595, 523], [0, 0, 1], [0, 1]], ![[392, 552, 508], [246, 427, 372], [528, 433, 75], [399, 78, 322], [103, 398, 573], [235, 520, 486], [478, 385, 480], [431, 69, 10], [274, 109, 552], [230, 64, 109]], ![[0, 1], [476, 6, 151], [353, 101, 366], [443, 602, 529], [611, 315, 584], [29, 491, 410], [279, 452, 276], [531, 570, 84], [130, 508, 64], [392, 552, 508]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29, 163], []]
 b := ![[], [142, 41, 157], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A617 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 617 2 where
 D := ![[498, 5, 1], [44, 119, 612, 1]]; D' := ![[498, 5, 1], [44, 119, 612, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P617P0
  | 1 => exact P617P1

def C6170 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A617.D 0) 617 where
  n := 2
  w := ![![617, 0, 0, 0, 0], ![498, 5, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C6171 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A617.D 1) 617 where
  n := 3
  w := ![![617, 0, 0, 0, 0], ![44, 119, 612, 5, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K617 : KummerData 617 ![I617N0, I617N1] ![380689, 234885113] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A617
  C := by
    intro i
    match i with
    | 0 => exact C6170
    | 1 => exact C6171
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 617 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp619 : Fact (Nat.Prime 619) := {out := by norm_num}

def I619N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![619, 0, 0, 0, 0], ![210, 1, 0, 0, 0]] i)))

def I619N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![619, 0, 0, 0, 0], ![568, 1, 0, 0, 0]] i)))

def I619N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![619, 0, 0, 0, 0], ![326, 64, 460, 5, 0]] i)))

def P619P0 : CertificateIrreducibleZModOfList' 619 1 2 9 [210, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [563], [], [120], [], [285], [500], [], [409, 1]]]
 h' := ![![[0, 1], [618], [472], [179], [109], [193], [230], [517], [151], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P619P1 : CertificateIrreducibleZModOfList' 619 1 2 9 [568, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [352], [], [611], [], [401], [216], [], [51, 1]]]
 h' := ![![[0, 1], [1], [572], [211], [576], [24], [493], [150], [125], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P619P2 : CertificateIrreducibleZModOfList' 619 3 2 9 [326, 64, 460, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [550, 81, 332], [228, 537, 287], [0, 1]]
 g := ![![[173, 378, 131], [448, 36, 195], [595, 157], [548, 145, 148], [9, 616], [285, 197, 579], [508, 122, 246], [159, 1], []], ![[91, 477, 159, 507], [358, 618, 516, 67], [99, 528], [278, 289, 280, 76], [2, 195], [125, 495, 301, 147], [490, 339, 593, 235], [21, 534], [419, 42]], ![[370, 188, 489, 290], [32, 282, 371, 20], [460, 470], [325, 586, 283, 371], [323, 477], [90, 605, 241, 536], [11, 494, 454, 496], [103, 371], [464, 42]]]
 h' := ![![[550, 81, 332], [36, 268, 582], [21, 240, 156], [243, 337, 311], [47, 472, 448], [559, 51, 114], [284, 385, 191], [162, 21, 457], [0, 0, 1], [0, 1]], ![[228, 537, 287], [215, 334, 398], [501, 329, 36], [533, 526, 341], [368, 78, 501], [493, 474, 156], [534, 21, 119], [159, 382, 448], [14, 310, 537], [550, 81, 332]], ![[0, 1], [73, 17, 258], [588, 50, 427], [582, 375, 586], [143, 69, 289], [302, 94, 349], [132, 213, 309], [500, 216, 333], [379, 309, 81], [228, 537, 287]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [454, 602], []]
 b := ![[], [279, 126, 606], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A619 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 619 3 where
 D := ![[210, 1], [568, 1], [326, 64, 460, 1]]; D' := ![[210, 1], [568, 1], [326, 64, 460, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9, 9]
 n := ![1, 1, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P619P0
  | 1 => exact P619P1
  | 2 => exact P619P2

def C6190 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A619.D 0) 619 where
  n := 1
  w := ![![619, 0, 0, 0, 0], ![210, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C6191 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A619.D 1) 619 where
  n := 1
  w := ![![619, 0, 0, 0, 0], ![568, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C6192 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A619.D 2) 619 where
  n := 3
  w := ![![619, 0, 0, 0, 0], ![326, 64, 460, 5, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K619 : KummerData 619 ![I619N0, I619N1, I619N2] ![619, 619, 237176659] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A619
  C := by
    intro i
    match i with
    | 0 => exact C6190
    | 1 => exact C6191
    | 2 => exact C6192
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 619 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp631 : Fact (Nat.Prime 631) := {out := by norm_num}

def I631N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![631, 0, 0, 0, 0], ![86, 1, 0, 0, 0]] i)))

def I631N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![631, 0, 0, 0, 0], ![454, 268, 1, 0, 0]] i)))

def I631N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![631, 0, 0, 0, 0], ![198, 277, 1, 0, 0]] i)))

def P631P0 : CertificateIrreducibleZModOfList' 631 1 2 9 [86, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [609], [339], [], [256], [279], [94], [], [545, 1]]]
 h' := ![![[0, 1], [630], [503], [344], [69], [615], [119], [57], [455], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P631P1 : CertificateIrreducibleZModOfList' 631 2 2 9 [454, 268, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [363, 630], [0, 1]]
 g := ![![[109, 568], [400, 441], [18, 505], [357], [253, 420], [290, 250], [84, 189], [521], [1]], ![[587, 63], [209, 190], [343, 126], [357], [11, 211], [176, 381], [543, 442], [521], [1]]]
 h' := ![![[363, 630], [128, 213], [31, 610], [489, 461], [611, 231], [219, 429], [355, 77], [501, 232], [177, 363], [0, 1]], ![[0, 1], [465, 418], [611, 21], [617, 170], [541, 400], [89, 202], [542, 554], [163, 399], [67, 268], [363, 630]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [612]]
 b := ![[], [620, 306]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P631P2 : CertificateIrreducibleZModOfList' 631 2 2 9 [198, 277, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [354, 630], [0, 1]]
 g := ![![[438, 594], [532, 612], [475, 458], [387], [555, 528], [9, 1], [176, 58], [378], [1]], ![[591, 37], [116, 19], [440, 173], [387], [60, 103], [363, 630], [516, 573], [378], [1]]]
 h' := ![![[354, 630], [41, 596], [600, 575], [107, 598], [535, 132], [111, 90], [488, 630], [327, 569], [433, 354], [0, 1]], ![[0, 1], [271, 35], [337, 56], [414, 33], [569, 499], [421, 541], [134, 1], [464, 62], [180, 277], [354, 630]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [378]]
 b := ![[], [621, 189]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A631 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 631 3 where
 D := ![[86, 1], [454, 268, 1], [198, 277, 1]]; D' := ![[86, 1], [454, 268, 1], [198, 277, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9, 9]
 n := ![1, 2, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P631P0
  | 1 => exact P631P1
  | 2 => exact P631P2

def C6310 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A631.D 0) 631 where
  n := 1
  w := ![![631, 0, 0, 0, 0], ![86, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C6311 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A631.D 1) 631 where
  n := 2
  w := ![![631, 0, 0, 0, 0], ![454, 268, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C6312 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A631.D 2) 631 where
  n := 2
  w := ![![631, 0, 0, 0, 0], ![198, 277, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K631 : KummerData 631 ![I631N0, I631N1, I631N2] ![631, 398161, 398161] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A631
  C := by
    intro i
    match i with
    | 0 => exact C6310
    | 1 => exact C6311
    | 2 => exact C6312
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 631 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp641 : Fact (Nat.Prime 641) := {out := by norm_num}

def I641N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![641, 0, 0, 0, 0], ![641, 0, 0, 3205, 0]] i)))

def P641P0 : CertificateIrreducibleZModOfList' 641 5 2 9 [341, 250, 0, 616, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [445, 343, 447, 551, 94], [388, 22, 542, 496, 371], [46, 553, 62, 183, 320], [403, 363, 231, 52, 497], [0, 1]]
 g := ![![[119, 282, 432, 204, 365], [142, 38, 216, 26], [333, 325, 176, 185], [452, 363, 409, 615], [74, 186, 5, 562], [240, 376, 545, 631], [0, 625], [1], []], ![[188, 32, 307, 555, 532, 292, 380, 95], [125, 517, 616, 148], [549, 542, 632, 233], [566, 247, 65, 154], [17, 402, 350, 433], [559, 89, 283, 7], [263, 520, 27, 515], [526, 159, 289, 636, 377, 312, 375, 514], [109, 228, 387, 503]], ![[137, 225, 606, 168, 77, 204, 364, 587], [153, 71, 76, 472], [91, 0, 185, 527], [160, 561, 376, 619], [14, 590, 293, 497], [45, 233, 524, 367], [352, 129, 102, 465], [533, 468, 479, 31, 566, 299, 40, 373], [50, 266, 98, 467]], ![[169, 435, 241, 346, 283, 310, 228, 551], [505, 276, 110, 465], [387, 426, 420, 112], [175, 99, 638, 18], [103, 378, 626, 178], [95, 360, 429, 258], [179, 346, 35, 64], [133, 432, 64, 160, 474, 183, 205, 636], [257, 582, 458, 481]], ![[7, 199, 199, 573, 387, 586, 519, 13], [159, 543, 333, 320], [264, 510, 194, 472], [472, 430, 351, 327], [52, 485, 247, 467], [637, 52, 563, 497], [575, 630, 410, 69], [381, 610, 448, 195, 80, 270, 38, 527], [190, 107, 408, 224]]]
 h' := ![![[445, 343, 447, 551, 94], [485, 490, 389, 125, 529], [352, 197, 588, 461, 384], [33, 127, 283, 152, 203], [220, 553, 43, 140, 164], [503, 377, 87, 539, 531], [260, 322, 477, 257, 561], [300, 391, 0, 25], [0, 0, 1], [0, 1]], ![[388, 22, 542, 496, 371], [42, 579, 107, 468, 43], [19, 349, 295, 550, 539], [569, 276, 275, 200, 399], [475, 553, 515, 562, 385], [547, 67, 161, 568, 182], [102, 212, 482, 529, 76], [389, 578, 97, 141, 607], [606, 280, 243, 95, 401], [445, 343, 447, 551, 94]], ![[46, 553, 62, 183, 320], [530, 299, 229, 403, 496], [122, 625, 213, 536, 79], [541, 444, 291, 203, 422], [129, 215, 306, 459, 485], [387, 249, 71, 331, 75], [567, 269, 568, 465, 370], [139, 176, 556, 440, 392], [166, 401, 17, 615, 455], [388, 22, 542, 496, 371]], ![[403, 363, 231, 52, 497], [82, 13, 362, 187, 504], [428, 387, 358, 443, 249], [197, 93, 494, 71, 337], [30, 631, 605, 177, 440], [121, 639, 250, 113, 224], [452, 579, 468, 211, 200], [348, 114, 548, 118, 633], [373, 335, 220, 484, 500], [46, 553, 62, 183, 320]], ![[0, 1], [428, 542, 195, 99, 351], [603, 365, 469, 574, 31], [266, 342, 580, 15, 562], [449, 612, 454, 585, 449], [242, 591, 72, 372, 270], [564, 541, 569, 461, 75], [324, 23, 81, 558, 291], [187, 266, 160, 88, 567], [403, 363, 231, 52, 497]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [187, 365, 494, 469], [], [], []]
 b := ![[], [31, 545, 113, 150, 561], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A641 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 641 1 where
 D := ![[341, 250, 0, 616, 0, 1]]; D' := ![[341, 250, 0, 616, 0, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9]
 n := ![5]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P641P0

def C6410 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A641.D 0) 641 where
  n := 5
  w := ![![641, 0, 0, 0, 0], ![641, 0, 0, 3205, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K641 : KummerData 641 ![I641N0] ![108215668739201] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A641
  C := by
    intro i
    match i with
    | 0 => exact C6410
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 641 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp643 : Fact (Nat.Prime 643) := {out := by norm_num}

def I643N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![643, 0, 0, 0, 0], ![188, 1, 0, 0, 0]] i)))

def I643N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![643, 0, 0, 0, 0], ![289, 1, 0, 0, 0]] i)))

def I643N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![643, 0, 0, 0, 0], ![631, 1, 0, 0, 0]] i)))

def I643N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![643, 0, 0, 0, 0], ![412, 178, 1, 0, 0]] i)))

def P643P0 : CertificateIrreducibleZModOfList' 643 1 2 9 [188, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [407], [], [], [], [], [], [441], [455, 1]]]
 h' := ![![[0, 1], [1], [97], [146], [185], [570], [235], [39], [622], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P643P1 : CertificateIrreducibleZModOfList' 643 1 2 9 [289, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [89], [], [], [], [], [], [260], [354, 1]]]
 h' := ![![[0, 1], [642], [416], [421], [118], [297], [565], [91], [574], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P643P2 : CertificateIrreducibleZModOfList' 643 1 2 9 [631, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [375], [], [], [], [], [], [160], [12, 1]]]
 h' := ![![[0, 1], [642], [595], [134], [443], [131], [81], [634], [144], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P643P3 : CertificateIrreducibleZModOfList' 643 2 2 9 [412, 178, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [465, 642], [0, 1]]
 g := ![![[478, 124], [184, 330], [63], [479], [492], [185], [433], [69, 177], [1]], ![[268, 519], [600, 313], [63], [479], [492], [185], [433], [70, 466], [1]]]
 h' := ![![[465, 642], [66, 278], [162, 293], [236, 132], [208, 196], [65, 507], [207, 73], [507, 305], [231, 465], [0, 1]], ![[0, 1], [93, 365], [91, 350], [531, 511], [42, 447], [482, 136], [73, 570], [229, 338], [408, 178], [465, 642]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [146]]
 b := ![[], [67, 73]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A643 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 643 4 where
 D := ![[188, 1], [289, 1], [631, 1], [412, 178, 1]]; D' := ![[188, 1], [289, 1], [631, 1], [412, 178, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9, 9, 9]
 n := ![1, 1, 1, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P643P0
  | 1 => exact P643P1
  | 2 => exact P643P2
  | 3 => exact P643P3

def C6430 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A643.D 0) 643 where
  n := 1
  w := ![![643, 0, 0, 0, 0], ![188, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C6431 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A643.D 1) 643 where
  n := 1
  w := ![![643, 0, 0, 0, 0], ![289, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C6432 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A643.D 2) 643 where
  n := 1
  w := ![![643, 0, 0, 0, 0], ![631, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C6433 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A643.D 3) 643 where
  n := 2
  w := ![![643, 0, 0, 0, 0], ![412, 178, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K643 : KummerData 643 ![I643N0, I643N1, I643N2, I643N3] ![643, 643, 643, 413449] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A643
  C := by
    intro i
    match i with
    | 0 => exact C6430
    | 1 => exact C6431
    | 2 => exact C6432
    | 3 => exact C6433
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 643 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


lemma PB1045I12_primes (p : ℕ) :
  p ∈ Set.range ![599, 601, 607, 613, 617, 619, 631, 641, 643] ↔ Nat.Prime p ∧ 593 < p ∧ p ≤ 643 := by
  rw [← List.mem_ofFn']
  convert primes_range 593 643 (by omega)
  decide

def PB1045I12 : PrimesBelowBoundCertificateInterval O 593 643 1045 where
  m := 9
  g := ![3, 1, 2, 2, 2, 3, 3, 1, 4]
  P := ![599, 601, 607, 613, 617, 619, 631, 641, 643]
  hP := PB1045I12_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I599N0, I599N1, I599N2]
    · exact ![I601N0]
    · exact ![I607N0, I607N1]
    · exact ![I613N0, I613N1]
    · exact ![I617N0, I617N1]
    · exact ![I619N0, I619N1, I619N2]
    · exact ![I631N0, I631N1, I631N2]
    · exact ![I641N0]
    · exact ![I643N0, I643N1, I643N2, I643N3]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · convert (containsPrimesAbove_of_KummerData K599) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K601) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K607) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K613) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K617) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K619) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K631) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K641) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K643) <;> rfl
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![599, 358801, 358801]
    · exact ![78410163603001]
    · exact ![368449, 223648543]
    · exact ![375769, 230346397]
    · exact ![380689, 234885113]
    · exact ![619, 619, 237176659]
    · exact ![631, 398161, 398161]
    · exact ![108215668739201]
    · exact ![643, 643, 643, 413449]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact (card_quot_of_KummerData K599)
    · exact (card_quot_of_KummerData K601)
    · exact (card_quot_of_KummerData K607)
    · exact (card_quot_of_KummerData K613)
    · exact (card_quot_of_KummerData K617)
    · exact (card_quot_of_KummerData K619)
    · exact (card_quot_of_KummerData K631)
    · exact (card_quot_of_KummerData K641)
    · exact (card_quot_of_KummerData K643)
  β := ![I599N0, I619N0, I619N1, I631N0, I643N0, I643N1, I643N2]
  Il := ![[I599N0], [], [], [], [], [I619N0, I619N1], [I631N0], [], [I643N0, I643N1, I643N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
