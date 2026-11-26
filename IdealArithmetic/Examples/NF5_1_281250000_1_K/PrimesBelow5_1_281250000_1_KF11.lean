
import IdealArithmetic.Examples.NF5_1_281250000_1_K.RI5_1_281250000_1_K
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 

instance hp541 : Fact (Nat.Prime 541) := {out := by norm_num}

def I541N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![541, 0, 0, 0, 0], ![541, 0, 0, 2705, 0]] i)))

def P541P0 : CertificateIrreducibleZModOfList' 541 5 2 9 [241, 250, 0, 516, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [470, 227, 390, 84, 129], [494, 454, 280, 61, 302], [78, 264, 506, 277, 92], [40, 136, 447, 119, 18], [0, 1]]
 g := ![![[236, 289, 456, 78, 353], [25, 448, 412, 431], [440, 44, 502, 167, 125], [465, 159, 481, 291, 84], [326, 4, 90, 293, 172], [117, 125, 485, 506], [0, 25, 0, 1], [], []], ![[68, 226, 521, 137, 23, 369, 228, 429], [469, 299, 306, 214], [275, 167, 500, 250, 59, 35, 320, 514], [123, 26, 57, 385, 328, 333, 285, 303], [331, 305, 511, 479, 540, 89, 168, 81], [279, 299, 450, 229], [252, 140, 444, 368], [132, 307, 19, 515], [456, 13, 32, 411]], ![[439, 7, 150, 400, 54, 262, 282, 181], [358, 49, 431, 496], [199, 118, 347, 249, 411, 417, 512, 414], [79, 218, 67, 507, 221, 507, 152, 183], [217, 88, 379, 309, 39, 280, 417, 348], [5, 353, 231, 211], [512, 217, 25, 194], [228, 436, 286, 256], [324, 47, 56, 316]], ![[474, 378, 172, 440, 286, 377, 439, 12], [372, 390, 189, 101], [375, 360, 115, 109, 83, 343, 314, 121], [40, 360, 478, 279, 147, 399, 261, 16], [75, 36, 319, 489, 99, 52, 399, 303], [426, 115, 339, 522], [185, 360, 425, 429], [325, 353, 185, 23], [117, 28, 114, 349]], ![[89, 189, 535, 155, 377, 115, 473, 52], [157, 231, 278, 516], [420, 51, 485, 415, 470, 488, 271, 250], [290, 240, 403, 47, 78, 299, 316, 385], [181, 174, 440, 429, 501, 233, 328, 250], [14, 11, 480, 7], [258, 500, 13, 103], [223, 224, 154, 48], [359, 483, 497, 324]]]
 h' := ![![[470, 227, 390, 84, 129], [483, 180, 220, 15, 219], [537, 172, 522, 518, 485], [463, 191, 57, 92, 439], [420, 206, 335, 536, 25], [476, 135, 165, 364, 71], [0, 467, 242, 300, 375], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[494, 454, 280, 61, 302], [277, 449, 193, 26, 380], [49, 501, 38, 131, 505], [102, 488, 269, 490, 393], [457, 14, 165, 421, 134], [381, 470, 113, 256, 462], [87, 143, 395, 52, 202], [170, 312, 45, 9, 205], [99, 490, 335, 233, 245], [470, 227, 390, 84, 129]], ![[78, 264, 506, 277, 92], [325, 455, 501, 135, 404], [235, 304, 482, 319, 261], [161, 175, 183, 304, 290], [529, 354, 107, 442, 274], [387, 475, 183, 494, 80], [394, 128, 401, 468, 54], [65, 77, 392, 248, 300], [406, 247, 365, 363, 525], [494, 454, 280, 61, 302]], ![[40, 136, 447, 119, 18], [8, 197, 110, 268, 521], [159, 131, 369, 153, 112], [172, 153, 433, 138, 467], [55, 413, 239, 79, 322], [261, 251, 461, 335, 503], [254, 450, 218, 58, 418], [416, 137, 525, 387, 169], [68, 317, 7, 526, 84], [78, 264, 506, 277, 92]], ![[0, 1], [529, 342, 58, 97, 99], [280, 515, 212, 502, 260], [407, 75, 140, 58, 34], [376, 95, 236, 145, 327], [366, 292, 160, 174, 507], [161, 435, 367, 204, 33], [140, 15, 120, 438, 407], [18, 28, 374, 501, 228], [40, 136, 447, 119, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [242, 299, 443, 396], [], [], []]
 b := ![[], [349, 532, 536, 88, 85], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A541 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 541 1 where
 D := ![[241, 250, 0, 516, 0, 1]]; D' := ![[241, 250, 0, 516, 0, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9]
 n := ![5]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P541P0

def C5410 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A541.D 0) 541 where
  n := 5
  w := ![![541, 0, 0, 0, 0], ![541, 0, 0, 2705, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K541 : KummerData 541 ![I541N0] ![46343232758701] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A541
  C := by
    intro i
    match i with
    | 0 => exact C5410
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 541 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp547 : Fact (Nat.Prime 547) := {out := by norm_num}

def I547N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![547, 0, 0, 0, 0], ![371, 1, 0, 0, 0]] i)))

def I547N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![547, 0, 0, 0, 0], ![39, 350, 324, 880, 10]] i)))

def P547P0 : CertificateIrreducibleZModOfList' 547 1 2 9 [371, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [115], [], [], [], [82], [], [], [176, 1]]]
 h' := ![![[0, 1], [1], [122], [183], [340], [210], [489], [184], [344], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P547P1 : CertificateIrreducibleZModOfList' 547 4 2 9 [39, 350, 319, 176, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [545, 502, 452, 538], [126, 266, 179, 163], [247, 325, 463, 393], [0, 1]]
 g := ![![[519, 330, 314, 73], [324, 388, 428, 313], [126, 292, 209], [316, 430, 142], [260, 386, 52], [435, 355, 515, 318], [414, 326, 344], [1], []], ![[276, 515, 422, 11, 78, 95], [55, 77, 206, 159, 145, 386], [457, 470, 114], [343, 107, 117], [286, 452, 137], [298, 51, 472, 459, 250, 5], [65, 492, 535], [6, 420, 442], [263, 35, 81]], ![[100, 456, 412, 262, 65, 7], [99, 224, 180, 535, 359, 426], [182, 31, 213], [187, 256, 195], [193, 12, 69], [498, 209, 464, 519, 26, 366], [530, 399, 183], [379, 233, 415], [393, 531, 313]], ![[228, 304, 1, 247, 371, 339], [23, 444, 92, 34, 488, 473], [49, 307, 204], [495, 372, 209], [80, 240, 158], [49, 272, 477, 230, 218, 153], [426, 127, 4], [487, 270, 44], [201, 304, 195]]]
 h' := ![![[545, 502, 452, 538], [492, 149, 40, 397], [314, 181, 375, 163], [98, 231, 361, 265], [317, 511, 87, 297], [539, 143, 31, 295], [144, 419, 482, 487], [508, 197, 228, 371], [0, 0, 1], [0, 1]], ![[126, 266, 179, 163], [542, 215, 530, 227], [148, 437, 124, 475], [415, 531, 497, 462], [169, 149, 154, 378], [80, 494, 51, 273], [358, 476, 61, 536], [221, 440, 5, 385], [140, 302, 465, 457], [545, 502, 452, 538]], ![[247, 325, 463, 393], [458, 439, 514, 300], [263, 209, 372, 450], [171, 200, 393, 498], [30, 513, 368, 154], [409, 47, 375, 200], [180, 15, 526, 327], [539, 424, 385, 340], [2, 122, 300, 433], [126, 266, 179, 163]], ![[0, 1], [541, 291, 10, 170], [400, 267, 223, 6], [505, 132, 390, 416], [71, 468, 485, 265], [377, 410, 90, 326], [520, 184, 25, 291], [439, 33, 476, 545], [111, 123, 328, 204], [247, 325, 463, 393]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [493, 152, 305], []]
 b := ![[], [], [351, 55, 408, 327], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A547 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 547 2 where
 D := ![[371, 1], [39, 350, 319, 176, 1]]; D' := ![[371, 1], [39, 350, 319, 176, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P547P0
  | 1 => exact P547P1

def C5470 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A547.D 0) 547 where
  n := 1
  w := ![![547, 0, 0, 0, 0], ![371, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C5471 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A547.D 1) 547 where
  n := 4
  w := ![![547, 0, 0, 0, 0], ![39, 350, 324, 880, 10]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K547 : KummerData 547 ![I547N0, I547N1] ![547, 89526025681] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A547
  C := by
    intro i
    match i with
    | 0 => exact C5470
    | 1 => exact C5471
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 547 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp557 : Fact (Nat.Prime 557) := {out := by norm_num}

def I557N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![557, 0, 0, 0, 0], ![283, 1, 0, 0, 0]] i)))

def I557N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![557, 0, 0, 0, 0], ![119, 91, 418, 1370, 10]] i)))

def P557P0 : CertificateIrreducibleZModOfList' 557 1 2 9 [283, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [150], [277], [], [16], [], [], [274, 1]]]
 h' := ![![[0, 1], [556], [439], [146], [171], [485], [553], [236], [438], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P557P1 : CertificateIrreducibleZModOfList' 557 4 2 9 [119, 91, 413, 274, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [470, 124, 299, 192], [382, 306, 468, 474], [545, 126, 347, 448], [0, 1]]
 g := ![![[202, 237, 211, 7], [133, 398, 64], [456, 311, 353, 444], [159, 295, 503, 203], [5, 469, 376], [290, 60, 516, 330], [494, 482, 438], [1], []], ![[473, 83, 329, 173, 339, 336], [348, 221, 550], [194, 361, 503, 84], [434, 182, 549, 172, 467, 126], [22, 179, 514], [64, 428, 94, 281, 180, 120], [42, 284, 361], [499, 512, 167], [93, 533, 102]], ![[445, 412, 162, 381, 225, 284], [336, 120, 81], [164, 368, 461, 402, 362, 96], [398, 182, 291, 66, 473, 538], [403, 13, 233], [120, 313, 246, 27, 486, 386], [43, 433, 43], [67, 35, 448], [326, 379, 205]], ![[166, 359, 546, 157, 542, 388], [280, 121, 528], [148, 170, 307, 235, 62, 260], [536, 55, 238, 358, 436, 521], [312, 12, 225], [224, 455, 254, 148, 462, 122], [28, 476, 227], [156, 264, 144], [543, 377, 184]]]
 h' := ![![[470, 124, 299, 192], [408, 211, 72, 243], [322, 321, 355, 8], [17, 360, 406, 70], [538, 333, 124, 260], [24, 216, 13, 360], [492, 111, 405, 38], [438, 466, 144, 283], [0, 0, 1], [0, 1]], ![[382, 306, 468, 474], [506, 51, 227, 400], [355, 361, 459, 290], [163, 8, 200], [541, 105, 108, 135], [389, 116, 122, 78], [460, 38, 307, 428], [46, 264, 497, 538], [401, 110, 208, 296], [470, 124, 299, 192]], ![[545, 126, 347, 448], [287, 74, 152, 41], [296, 488, 60, 548], [16, 155, 546, 23], [396, 299, 404, 489], [131, 383, 149, 104], [411, 175, 539, 204], [444, 131, 249, 265], [186, 272, 332, 273], [382, 306, 468, 474]], ![[0, 1], [392, 221, 106, 430], [378, 501, 240, 268], [315, 34, 519, 464], [36, 377, 478, 230], [435, 399, 273, 15], [463, 233, 420, 444], [200, 253, 224, 28], [139, 175, 16, 545], [545, 126, 347, 448]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [417, 516, 43], []]
 b := ![[], [], [535, 488, 135, 175], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A557 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 557 2 where
 D := ![[283, 1], [119, 91, 413, 274, 1]]; D' := ![[283, 1], [119, 91, 413, 274, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P557P0
  | 1 => exact P557P1

def C5570 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A557.D 0) 557 where
  n := 1
  w := ![![557, 0, 0, 0, 0], ![283, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C5571 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A557.D 1) 557 where
  n := 4
  w := ![![557, 0, 0, 0, 0], ![119, 91, 418, 1370, 10]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K557 : KummerData 557 ![I557N0, I557N1] ![557, 96254442001] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A557
  C := by
    intro i
    match i with
    | 0 => exact C5570
    | 1 => exact C5571
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 557 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp563 : Fact (Nat.Prime 563) := {out := by norm_num}

def I563N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![563, 0, 0, 0, 0], ![206, 1, 0, 0, 0]] i)))

def I563N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![563, 0, 0, 0, 0], ![296, 1, 0, 0, 0]] i)))

def I563N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![563, 0, 0, 0, 0], ![436, 1, 0, 0, 0]] i)))

def I563N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![563, 0, 0, 0, 0], ![376, 188, 1, 0, 0]] i)))

def P563P0 : CertificateIrreducibleZModOfList' 563 1 2 9 [206, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [522], [], [], [25], [205], [], [], [357, 1]]]
 h' := ![![[0, 1], [1], [236], [133], [480], [558], [247], [44], [211], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P563P1 : CertificateIrreducibleZModOfList' 563 1 2 9 [296, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [466], [], [], [485], [476], [], [], [267, 1]]]
 h' := ![![[0, 1], [562], [62], [25], [5], [417], [208], [467], [351], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P563P2 : CertificateIrreducibleZModOfList' 563 1 2 9 [436, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [133], [], [], [75], [44], [], [], [127, 1]]]
 h' := ![![[0, 1], [1], [480], [427], [517], [521], [211], [357], [365], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P563P3 : CertificateIrreducibleZModOfList' 563 2 2 9 [376, 188, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [375, 562], [0, 1]]
 g := ![![[282, 208], [35, 434], [399], [44], [458, 424], [386, 343], [133], [438], [1]], ![[25, 355], [78, 129], [399], [44], [129, 139], [84, 220], [133], [438], [1]]]
 h' := ![![[375, 562], [352, 467], [247, 506], [179, 472], [70, 352], [118, 125], [181, 61], [334, 480], [187, 375], [0, 1]], ![[0, 1], [384, 96], [266, 57], [397, 91], [328, 211], [264, 438], [536, 502], [174, 83], [62, 188], [375, 562]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [75]]
 b := ![[], [147, 319]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A563 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 563 4 where
 D := ![[206, 1], [296, 1], [436, 1], [376, 188, 1]]; D' := ![[206, 1], [296, 1], [436, 1], [376, 188, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9, 9, 9]
 n := ![1, 1, 1, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P563P0
  | 1 => exact P563P1
  | 2 => exact P563P2
  | 3 => exact P563P3

def C5630 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A563.D 0) 563 where
  n := 1
  w := ![![563, 0, 0, 0, 0], ![206, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C5631 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A563.D 1) 563 where
  n := 1
  w := ![![563, 0, 0, 0, 0], ![296, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C5632 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A563.D 2) 563 where
  n := 1
  w := ![![563, 0, 0, 0, 0], ![436, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C5633 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A563.D 3) 563 where
  n := 2
  w := ![![563, 0, 0, 0, 0], ![376, 188, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K563 : KummerData 563 ![I563N0, I563N1, I563N2, I563N3] ![563, 563, 563, 316969] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A563
  C := by
    intro i
    match i with
    | 0 => exact C5630
    | 1 => exact C5631
    | 2 => exact C5632
    | 3 => exact C5633
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 563 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp569 : Fact (Nat.Prime 569) := {out := by norm_num}

def I569N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![569, 0, 0, 0, 0], ![551, 1, 0, 0, 0]] i)))

def I569N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![569, 0, 0, 0, 0], ![461, 292, 1, 0, 0]] i)))

def I569N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![569, 0, 0, 0, 0], ![186, 295, 1, 0, 0]] i)))

def P569P0 : CertificateIrreducibleZModOfList' 569 1 2 9 [551, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [411], [172], [90], [], [], [18, 1]]]
 h' := ![![[0, 1], [1], [1], [1], [251], [482], [447], [280], [324], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P569P1 : CertificateIrreducibleZModOfList' 569 2 2 9 [461, 292, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [277, 568], [0, 1]]
 g := ![![[482, 489], [504], [196], [193, 219], [483, 367], [491, 32], [395], [483], [1]], ![[513, 80], [504], [196], [542, 350], [291, 202], [251, 537], [395], [483], [1]]]
 h' := ![![[277, 568], [97, 498], [552, 75], [360, 14], [385, 254], [111, 103], [312, 334], [100, 163], [108, 277], [0, 1]], ![[0, 1], [345, 71], [274, 494], [255, 555], [187, 315], [192, 466], [83, 235], [300, 406], [22, 292], [277, 568]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [296]]
 b := ![[], [555, 148]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P569P2 : CertificateIrreducibleZModOfList' 569 2 2 9 [186, 295, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [274, 568], [0, 1]]
 g := ![![[23, 517], [364], [392], [201, 87], [454, 397], [209, 387], [508], [537], [1]], ![[0, 52], [364], [392], [141, 482], [553, 172], [413, 182], [508], [537], [1]]]
 h' := ![![[274, 568], [327, 275], [263, 262], [168, 538], [337, 35], [387, 85], [545, 154], [149, 259], [383, 274], [0, 1]], ![[0, 1], [0, 294], [357, 307], [209, 31], [254, 534], [348, 484], [66, 415], [559, 310], [351, 295], [274, 568]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44]]
 b := ![[], [400, 22]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A569 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 569 3 where
 D := ![[551, 1], [461, 292, 1], [186, 295, 1]]; D' := ![[551, 1], [461, 292, 1], [186, 295, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9, 9]
 n := ![1, 2, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P569P0
  | 1 => exact P569P1
  | 2 => exact P569P2

def C5690 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A569.D 0) 569 where
  n := 1
  w := ![![569, 0, 0, 0, 0], ![551, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C5691 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A569.D 1) 569 where
  n := 2
  w := ![![569, 0, 0, 0, 0], ![461, 292, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C5692 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A569.D 2) 569 where
  n := 2
  w := ![![569, 0, 0, 0, 0], ![186, 295, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K569 : KummerData 569 ![I569N0, I569N1, I569N2] ![569, 323761, 323761] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A569
  C := by
    intro i
    match i with
    | 0 => exact C5690
    | 1 => exact C5691
    | 2 => exact C5692
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 569 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp571 : Fact (Nat.Prime 571) := {out := by norm_num}

def I571N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![571, 0, 0, 0, 0], ![37, 1, 0, 0, 0]] i)))

def I571N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![571, 0, 0, 0, 0], ![91, 1, 0, 0, 0]] i)))

def I571N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![571, 0, 0, 0, 0], ![218, 430, 443, 5, 0]] i)))

def P571P0 : CertificateIrreducibleZModOfList' 571 1 2 9 [37, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [463], [], [362], [57], [84], [], [], [534, 1]]]
 h' := ![![[0, 1], [570], [172], [310], [175], [318], [478], [139], [227], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P571P1 : CertificateIrreducibleZModOfList' 571 1 2 9 [91, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [320], [], [82], [403], [126], [], [], [480, 1]]]
 h' := ![![[0, 1], [1], [379], [532], [442], [525], [469], [145], [287], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P571P2 : CertificateIrreducibleZModOfList' 571 3 2 9 [218, 430, 443, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [185, 248, 265], [514, 322, 306], [0, 1]]
 g := ![![[468, 446, 561], [359, 315, 530], [177, 148], [542, 308, 61], [31, 316, 554], [463, 429, 196], [443, 14], [128, 1], []], ![[451, 407, 317, 338], [41, 248, 229, 570], [131, 549], [9, 547, 453, 537], [438, 365, 383, 397], [231, 123, 463, 90], [144, 13], [422, 333], [228, 563]], ![[330, 501, 515, 13], [478, 254, 296, 9], [81, 236], [362, 189, 350, 24], [64, 429, 419, 31], [399, 252, 103, 45], [245, 439], [251, 407], [187, 563]]]
 h' := ![![[185, 248, 265], [536, 354, 246], [210, 293, 447], [41, 413, 166], [94, 565, 54], [133, 216, 360], [411, 534, 557], [75, 129, 537], [0, 0, 1], [0, 1]], ![[514, 322, 306], [526, 307, 9], [435, 176, 31], [489, 388, 162], [204, 240, 381], [72, 565, 147], [144, 83, 533], [353, 70, 397], [509, 32, 322], [185, 248, 265]], ![[0, 1], [234, 481, 316], [239, 102, 93], [557, 341, 243], [426, 337, 136], [126, 361, 64], [154, 525, 52], [109, 372, 208], [169, 539, 248], [514, 322, 306]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [115, 440], []]
 b := ![[], [525, 288, 300], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A571 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 571 3 where
 D := ![[37, 1], [91, 1], [218, 430, 443, 1]]; D' := ![[37, 1], [91, 1], [218, 430, 443, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9, 9]
 n := ![1, 1, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P571P0
  | 1 => exact P571P1
  | 2 => exact P571P2

def C5710 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A571.D 0) 571 where
  n := 1
  w := ![![571, 0, 0, 0, 0], ![37, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C5711 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A571.D 1) 571 where
  n := 1
  w := ![![571, 0, 0, 0, 0], ![91, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C5712 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A571.D 2) 571 where
  n := 3
  w := ![![571, 0, 0, 0, 0], ![218, 430, 443, 5, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K571 : KummerData 571 ![I571N0, I571N1, I571N2] ![571, 571, 186169411] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A571
  C := by
    intro i
    match i with
    | 0 => exact C5710
    | 1 => exact C5711
    | 2 => exact C5712
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 571 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp577 : Fact (Nat.Prime 577) := {out := by norm_num}

def I577N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![577, 0, 0, 0, 0], ![24, 1, 0, 0, 0]] i)))

def I577N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![577, 0, 0, 0, 0], ![276, 47, 556, 2765, 10]] i)))

def P577P0 : CertificateIrreducibleZModOfList' 577 1 2 9 [24, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [], [], [], [1], [], [553, 1]]]
 h' := ![![[0, 1], [1], [1], [1], [1], [576], [553], [1], [576], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P577P1 : CertificateIrreducibleZModOfList' 577 4 2 9 [276, 47, 551, 553, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 539, 400, 333], [54, 376, 321, 417], [530, 238, 433, 404], [0, 1]]
 g := ![![[186, 231, 280, 393], [34, 199, 193], [45, 208, 136], [351, 284, 506], [431, 381, 479], [323, 441, 259], [68, 74, 70, 576], [1], []], ![[183, 333, 113, 152, 108, 199], [246, 27, 524], [359, 467, 515], [292, 207, 430], [142, 173, 114], [105, 80, 187], [113, 179, 560, 107, 303, 444], [110, 309, 169], [431, 38, 105]], ![[248, 165, 364, 533, 467, 174], [469, 181, 107], [425, 171, 121], [126, 247, 273], [284, 238, 428], [313, 384, 566], [21, 94, 43, 342, 443, 369], [230, 468, 456], [379, 458, 212]], ![[201, 527, 166, 81, 324, 525], [539, 422, 379], [229, 142, 66], [397, 331, 35], [271, 547, 335], [111, 442, 501], [101, 288, 418, 548, 566, 278], [22, 338, 108], [215, 133, 502]]]
 h' := ![![[17, 539, 400, 333], [256, 248, 527, 230], [312, 459, 562, 167], [275, 407, 345, 504], [37, 352, 220, 314], [383, 64, 516, 58], [273, 49, 298, 516], [301, 530, 26, 24], [0, 0, 1], [0, 1]], ![[54, 376, 321, 417], [562, 221, 309, 512], [98, 525, 411, 189], [365, 398, 141, 365], [97, 516, 179, 473], [80, 365, 399, 132], [218, 391, 438, 377], [164, 63, 349, 485], [195, 275, 100, 13], [17, 539, 400, 333]], ![[530, 238, 433, 404], [156, 186, 167, 348], [217, 48, 387, 354], [92, 381, 479, 11], [367, 173, 452, 106], [415, 28, 248, 131], [145, 279, 168, 208], [22, 558, 28, 154], [441, 247, 269, 313], [54, 376, 321, 417]], ![[0, 1], [240, 499, 151, 64], [517, 122, 371, 444], [56, 545, 189, 274], [239, 113, 303, 261], [572, 120, 568, 256], [407, 435, 250, 53], [339, 3, 174, 491], [569, 55, 207, 251], [530, 238, 433, 404]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [209, 516, 426], []]
 b := ![[], [], [11, 545, 313, 82], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A577 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 577 2 where
 D := ![[24, 1], [276, 47, 551, 553, 1]]; D' := ![[24, 1], [276, 47, 551, 553, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P577P0
  | 1 => exact P577P1

def C5770 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A577.D 0) 577 where
  n := 1
  w := ![![577, 0, 0, 0, 0], ![24, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C5771 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A577.D 1) 577 where
  n := 4
  w := ![![577, 0, 0, 0, 0], ![276, 47, 556, 2765, 10]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K577 : KummerData 577 ![I577N0, I577N1] ![577, 110841719041] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A577
  C := by
    intro i
    match i with
    | 0 => exact C5770
    | 1 => exact C5771
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 577 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp587 : Fact (Nat.Prime 587) := {out := by norm_num}

def I587N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![587, 0, 0, 0, 0], ![22, 1, 0, 0, 0]] i)))

def I587N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![587, 0, 0, 0, 0], ![243, 1, 0, 0, 0]] i)))

def I587N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![587, 0, 0, 0, 0], ![294, 1, 0, 0, 0]] i)))

def I587N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![587, 0, 0, 0, 0], ![270, 28, 1, 0, 0]] i)))

def P587P0 : CertificateIrreducibleZModOfList' 587 1 2 9 [22, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [507], [], [563], [], [], [88], [], [565, 1]]]
 h' := ![![[0, 1], [586], [546], [528], [222], [101], [412], [43], [484], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P587P1 : CertificateIrreducibleZModOfList' 587 1 2 9 [243, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [401], [], [470], [], [], [149], [], [344, 1]]]
 h' := ![![[0, 1], [586], [455], [255], [192], [336], [187], [292], [349], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P587P2 : CertificateIrreducibleZModOfList' 587 1 2 9 [294, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [585], [], [453], [], [], [360], [], [293, 1]]]
 h' := ![![[0, 1], [1], [380], [67], [311], [115], [407], [477], [147], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P587P3 : CertificateIrreducibleZModOfList' 587 2 2 9 [270, 28, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [559, 586], [0, 1]]
 g := ![![[361, 537], [303, 493], [243], [573, 411], [264], [495], [17, 332], [197], [1]], ![[0, 50], [0, 94], [243], [218, 176], [264], [495], [113, 255], [197], [1]]]
 h' := ![![[559, 586], [370, 139], [367, 76], [258, 209], [494, 96], [269, 542], [106, 151], [339, 212], [317, 559], [0, 1]], ![[0, 1], [0, 448], [0, 511], [276, 378], [154, 491], [355, 45], [574, 436], [273, 375], [514, 28], [559, 586]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [119]]
 b := ![[], [246, 353]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A587 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 587 4 where
 D := ![[22, 1], [243, 1], [294, 1], [270, 28, 1]]; D' := ![[22, 1], [243, 1], [294, 1], [270, 28, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9, 9, 9]
 n := ![1, 1, 1, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P587P0
  | 1 => exact P587P1
  | 2 => exact P587P2
  | 3 => exact P587P3

def C5870 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A587.D 0) 587 where
  n := 1
  w := ![![587, 0, 0, 0, 0], ![22, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C5871 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A587.D 1) 587 where
  n := 1
  w := ![![587, 0, 0, 0, 0], ![243, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C5872 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A587.D 2) 587 where
  n := 1
  w := ![![587, 0, 0, 0, 0], ![294, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C5873 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A587.D 3) 587 where
  n := 2
  w := ![![587, 0, 0, 0, 0], ![270, 28, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K587 : KummerData 587 ![I587N0, I587N1, I587N2, I587N3] ![587, 587, 587, 344569] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A587
  C := by
    intro i
    match i with
    | 0 => exact C5870
    | 1 => exact C5871
    | 2 => exact C5872
    | 3 => exact C5873
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 587 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp593 : Fact (Nat.Prime 593) := {out := by norm_num}

def I593N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![593, 0, 0, 0, 0], ![206, 358, 1, 0, 0]] i)))

def I593N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![593, 0, 0, 0, 0], ![557, 438, 235, 5, 0]] i)))

def P593P0 : CertificateIrreducibleZModOfList' 593 2 2 9 [206, 358, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [235, 592], [0, 1]]
 g := ![![[209, 336], [200], [519], [162], [128, 495], [361], [309, 572], [76], [1]], ![[300, 257], [200], [519], [162], [225, 98], [361], [118, 21], [76], [1]]]
 h' := ![![[235, 592], [227, 157], [223, 359], [108, 332], [317, 92], [51, 41], [390, 574], [95, 502], [387, 235], [0, 1]], ![[0, 1], [356, 436], [382, 234], [445, 261], [589, 501], [198, 552], [76, 19], [58, 91], [463, 358], [235, 592]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [352]]
 b := ![[], [75, 176]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P593P1 : CertificateIrreducibleZModOfList' 593 3 2 9 [557, 438, 235, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [133, 161, 144], [225, 431, 449], [0, 1]]
 g := ![![[119, 269, 338], [212, 378], [69, 535], [16, 58], [482, 508, 436], [416, 286], [387, 168, 584], [358, 1], []], ![[539, 110, 516, 336], [0, 184], [95, 123], [127, 358], [337, 544, 454, 368], [551, 533], [105, 89, 36, 19], [581, 152], [428, 574]], ![[410, 205, 298, 49], [532, 450], [237, 439], [159, 422], [271, 428, 171, 128], [371, 561], [322, 405, 88, 397], [508, 422], [123, 574]]]
 h' := ![![[133, 161, 144], [33, 77, 67], [36, 204, 413], [288, 285, 306], [155, 122, 158], [15, 554, 170], [293, 268, 62], [435, 377, 231], [0, 0, 1], [0, 1]], ![[225, 431, 449], [465, 430, 234], [301, 366, 422], [76, 169, 363], [29, 157, 274], [271, 477, 52], [591, 530, 84], [29, 559, 262], [482, 556, 431], [133, 161, 144]], ![[0, 1], [252, 86, 292], [358, 23, 351], [50, 139, 517], [577, 314, 161], [419, 155, 371], [85, 388, 447], [226, 250, 100], [497, 37, 161], [225, 431, 449]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [125, 205], []]
 b := ![[], [502, 110, 118], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A593 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 593 2 where
 D := ![[206, 358, 1], [557, 438, 235, 1]]; D' := ![[206, 358, 1], [557, 438, 235, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P593P0
  | 1 => exact P593P1

def C5930 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A593.D 0) 593 where
  n := 2
  w := ![![593, 0, 0, 0, 0], ![206, 358, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C5931 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A593.D 1) 593 where
  n := 3
  w := ![![593, 0, 0, 0, 0], ![557, 438, 235, 5, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K593 : KummerData 593 ![I593N0, I593N1] ![351649, 208527857] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A593
  C := by
    intro i
    match i with
    | 0 => exact C5930
    | 1 => exact C5931
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 593 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


lemma PB1045I11_primes (p : ℕ) :
  p ∈ Set.range ![541, 547, 557, 563, 569, 571, 577, 587, 593] ↔ Nat.Prime p ∧ 523 < p ∧ p ≤ 593 := by
  rw [← List.mem_ofFn']
  convert primes_range 523 593 (by omega)
  decide

def PB1045I11 : PrimesBelowBoundCertificateInterval O 523 593 1045 where
  m := 9
  g := ![1, 2, 2, 4, 3, 3, 2, 4, 2]
  P := ![541, 547, 557, 563, 569, 571, 577, 587, 593]
  hP := PB1045I11_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I541N0]
    · exact ![I547N0, I547N1]
    · exact ![I557N0, I557N1]
    · exact ![I563N0, I563N1, I563N2, I563N3]
    · exact ![I569N0, I569N1, I569N2]
    · exact ![I571N0, I571N1, I571N2]
    · exact ![I577N0, I577N1]
    · exact ![I587N0, I587N1, I587N2, I587N3]
    · exact ![I593N0, I593N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · convert (containsPrimesAbove_of_KummerData K541) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K547) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K557) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K563) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K569) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K571) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K577) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K587) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K593) <;> rfl
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![46343232758701]
    · exact ![547, 89526025681]
    · exact ![557, 96254442001]
    · exact ![563, 563, 563, 316969]
    · exact ![569, 323761, 323761]
    · exact ![571, 571, 186169411]
    · exact ![577, 110841719041]
    · exact ![587, 587, 587, 344569]
    · exact ![351649, 208527857]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact (card_quot_of_KummerData K541)
    · exact (card_quot_of_KummerData K547)
    · exact (card_quot_of_KummerData K557)
    · exact (card_quot_of_KummerData K563)
    · exact (card_quot_of_KummerData K569)
    · exact (card_quot_of_KummerData K571)
    · exact (card_quot_of_KummerData K577)
    · exact (card_quot_of_KummerData K587)
    · exact (card_quot_of_KummerData K593)
  β := ![I547N0, I557N0, I563N0, I563N1, I563N2, I569N0, I571N0, I571N1, I577N0, I587N0, I587N1, I587N2]
  Il := ![[], [I547N0], [I557N0], [I563N0, I563N1, I563N2], [I569N0], [I571N0, I571N1], [I577N0], [I587N0, I587N1, I587N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
