
import IdealArithmetic.Examples.NF5_1_91125000000_1_K.RI5_1_91125000000_1_K
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 

instance hp647 : Fact (Nat.Prime 647) := {out := by norm_num}

def I647N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![647, 0, 0, 0, 0], ![426, 565, 1, 0, 0]] i)))

def I647N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![647, 0, 0, 0, 0], ![36, 476, 82, 2, 0]] i)))

def P647P0 : CertificateIrreducibleZModOfList' 647 2 2 9 [426, 565, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [82, 646], [0, 1]]
 g := ![![[258, 484], [611, 467], [310, 388], [25], [174], [636], [252], [136, 254], [1]], ![[479, 163], [85, 180], [423, 259], [25], [174], [636], [252], [260, 393], [1]]]
 h' := ![![[82, 646], [455, 625], [575, 383], [195, 397], [417, 5], [458, 327], [435, 197], [294, 314], [221, 82], [0, 1]], ![[0, 1], [592, 22], [278, 264], [399, 250], [180, 642], [98, 320], [414, 450], [162, 333], [475, 565], [82, 646]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [365]]
 b := ![[], [605, 506]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P647P1 : CertificateIrreducibleZModOfList' 647 3 2 9 [36, 475, 82, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 5, 576], [537, 641, 71], [0, 1]]
 g := ![![[143, 467, 508], [426, 195, 418], [588, 512, 8], [431, 25], [405, 272], [272, 121], [582, 295], [426, 565, 1], []], ![[152, 529, 442, 382], [216, 379, 621, 450], [461, 162, 373, 411], [490, 324], [259, 468], [637, 517], [372, 165], [199, 229, 516, 32], [8, 512]], ![[309, 79, 211, 250], [144, 70, 546, 188], [180, 358, 281, 270], [222, 529], [610, 49], [60, 52], [546, 536], [258, 99, 212, 481], [513, 512]]]
 h' := ![![[28, 5, 576], [192, 103, 283], [183, 599, 79], [639, 567, 575], [559, 593, 642], [500, 151, 313], [384, 581, 11], [192, 525, 100], [0, 0, 1], [0, 1]], ![[537, 641, 71], [457, 593, 47], [497, 159, 346], [213, 170, 289], [449, 147, 629], [167, 272, 341], [110, 176, 91], [439, 108, 298], [496, 46, 641], [28, 5, 576]], ![[0, 1], [259, 598, 317], [581, 536, 222], [154, 557, 430], [166, 554, 23], [288, 224, 640], [355, 537, 545], [520, 14, 249], [102, 601, 5], [537, 641, 71]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [199, 254], []]
 b := ![[], [137, 599, 523], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A647 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 647 2 where
 D := ![[426, 565, 1], [36, 475, 82, 1]]; D' := ![[426, 565, 1], [36, 475, 82, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P647P0
  | 1 => exact P647P1

def C6470 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A647.D 0) 647 where
  n := 2
  w := ![![647, 0, 0, 0, 0], ![426, 565, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C6471 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A647.D 1) 647 where
  n := 3
  w := ![![647, 0, 0, 0, 0], ![36, 476, 82, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K647 : KummerData 647 ![I647N0, I647N1] ![418609, 270840023] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A647
  C := by
    intro i
    match i with
    | 0 => exact C6470
    | 1 => exact C6471
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 647 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp653 : Fact (Nat.Prime 653) := {out := by norm_num}

def I653N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![653, 0, 0, 0, 0], ![33, 1, 0, 0, 0]] i)))

def I653N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![653, 0, 0, 0, 0], ![884, 3253, 11331, -1798, 22728]] i)))

def P653P0 : CertificateIrreducibleZModOfList' 653 1 2 9 [33, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [519], [488], [], [], [], [73], [620, 1]]]
 h' := ![![[0, 1], [652], [504], [221], [496], [329], [70], [203], [436], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P653P1 : CertificateIrreducibleZModOfList' 653 4 2 9 [236, 531, 436, 620, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [484, 510, 246, 281], [413, 396, 618, 270], [442, 399, 442, 102], [0, 1]]
 g := ![![[496, 62, 330, 421], [317, 606, 375], [499, 543, 607, 121], [631, 341, 167, 291], [102, 452, 362], [17, 388, 609], [205], [33, 1], []], ![[127, 589, 608, 393, 97, 372], [196, 151, 44], [304, 553, 226, 425, 227, 300], [561, 260, 183, 380, 622, 582], [333, 486, 131], [169, 358, 100], [331, 589, 600], [407, 600, 621, 554, 607, 245], [198, 59, 601]], ![[500, 307, 150, 415, 321, 317], [195, 55, 40], [559, 421, 299, 587, 370, 50], [496, 64, 213, 198, 490, 56], [199, 81, 340], [530, 331, 406], [515, 593, 117], [486, 551, 570, 507, 479, 450], [143, 85, 417]], ![[138, 475, 291, 97, 259, 301], [41, 462, 554], [114, 163, 176, 606, 11, 537], [79, 629, 495, 260, 56, 177], [99, 424, 160], [432, 637, 81], [453, 244, 577], [383, 234, 303, 298, 289, 30], [364, 561, 609]]]
 h' := ![![[484, 510, 246, 281], [178, 149, 39, 454], [429, 360, 40, 612], [621, 233, 332, 642], [98, 428, 124, 141], [650, 549, 423, 113], [287, 315, 598, 102], [48, 525, 100], [0, 0, 1], [0, 1]], ![[413, 396, 618, 270], [123, 335, 37, 149], [4, 283, 487, 474], [86, 334, 368, 539], [476, 477, 619, 110], [63, 545, 430, 625], [296, 432, 343, 643], [77, 516, 329, 337], [117, 449, 390, 461], [484, 510, 246, 281]], ![[442, 399, 442, 102], [579, 178, 146, 451], [397, 133, 183, 373], [507, 285, 652, 536], [142, 406, 240, 316], [233, 214, 444, 475], [364, 487, 333, 552], [521, 223, 441, 211], [344, 594, 371, 302], [413, 396, 618, 270]], ![[0, 1], [68, 644, 431, 252], [408, 530, 596, 500], [407, 454, 607, 242], [567, 648, 323, 86], [370, 651, 9, 93], [161, 72, 32, 9], [44, 42, 436, 105], [409, 263, 544, 543], [442, 399, 442, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [466, 77, 604], []]
 b := ![[], [], [363, 205, 456, 525], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A653 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 653 2 where
 D := ![[33, 1], [236, 531, 436, 620, 1]]; D' := ![[33, 1], [236, 531, 436, 620, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P653P0
  | 1 => exact P653P1

def C6530 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A653.D 0) 653 where
  n := 1
  w := ![![653, 0, 0, 0, 0], ![33, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C6531 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A653.D 1) 653 where
  n := 4
  w := ![![653, 0, 0, 0, 0], ![884, 3253, 11331, -1798, 22728]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K653 : KummerData 653 ![I653N0, I653N1] ![653, 181824635281] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A653
  C := by
    intro i
    match i with
    | 0 => exact C6530
    | 1 => exact C6531
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 653 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp659 : Fact (Nat.Prime 659) := {out := by norm_num}

def I659N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![659, 0, 0, 0, 0], ![219, 1, 0, 0, 0]] i)))

def I659N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![659, 0, 0, 0, 0], ![176, 441, 1, 0, 0]] i)))

def I659N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![659, 0, 0, 0, 0], ![119, 658, 1, 0, 0]] i)))

def P659P0 : CertificateIrreducibleZModOfList' 659 1 2 9 [219, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [328], [], [], [351], [], [], [228], [440, 1]]]
 h' := ![![[0, 1], [658], [186], [59], [234], [203], [39], [152], [513], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P659P1 : CertificateIrreducibleZModOfList' 659 2 2 9 [176, 441, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [218, 658], [0, 1]]
 g := ![![[171, 498], [215, 295], [484], [347], [480, 637], [487], [630], [460, 76], [1]], ![[0, 161], [602, 364], [484], [347], [297, 22], [487], [630], [553, 583], [1]]]
 h' := ![![[218, 658], [382, 361], [46, 256], [124, 22], [531, 316], [183, 623], [15, 370], [97, 578], [483, 218], [0, 1]], ![[0, 1], [0, 298], [498, 403], [307, 637], [224, 343], [243, 36], [277, 289], [232, 81], [559, 441], [218, 658]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [340]]
 b := ![[], [581, 170]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P659P2 : CertificateIrreducibleZModOfList' 659 2 2 9 [119, 658, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 658], [0, 1]]
 g := ![![[587, 115], [249, 562], [513], [447], [263, 45], [391], [497], [422, 1], [1]], ![[43, 544], [152, 97], [513], [447], [308, 614], [391], [497], [423, 658], [1]]]
 h' := ![![[1, 658], [24, 559], [421, 362], [381, 440], [335, 239], [425, 115], [330, 383], [525, 625], [540, 1], [0, 1]], ![[0, 1], [583, 100], [124, 297], [162, 219], [574, 420], [540, 544], [54, 276], [491, 34], [541, 658], [1, 658]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [616]]
 b := ![[], [505, 308]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A659 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 659 3 where
 D := ![[219, 1], [176, 441, 1], [119, 658, 1]]; D' := ![[219, 1], [176, 441, 1], [119, 658, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9, 9]
 n := ![1, 2, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P659P0
  | 1 => exact P659P1
  | 2 => exact P659P2

def C6590 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A659.D 0) 659 where
  n := 1
  w := ![![659, 0, 0, 0, 0], ![219, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C6591 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A659.D 1) 659 where
  n := 2
  w := ![![659, 0, 0, 0, 0], ![176, 441, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C6592 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A659.D 2) 659 where
  n := 2
  w := ![![659, 0, 0, 0, 0], ![119, 658, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K659 : KummerData 659 ![I659N0, I659N1, I659N2] ![659, 434281, 434281] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A659
  C := by
    intro i
    match i with
    | 0 => exact C6590
    | 1 => exact C6591
    | 2 => exact C6592
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 659 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp661 : Fact (Nat.Prime 661) := {out := by norm_num}

def I661N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![661, 0, 0, 0, 0], ![15864, 661, 661, 0, 0]] i)))

def P661P0 : CertificateIrreducibleZModOfList' 661 5 2 9 [144, 136, 561, 0, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [69, 486, 286, 136, 89], [410, 15, 467, 455, 296], [373, 447, 532, 422, 337], [470, 373, 37, 309, 600], [0, 1]]
 g := ![![[151, 330, 239, 56, 610], [544, 486, 469, 87], [505, 657, 550, 203, 557], [575, 238, 593, 192], [180, 201, 504, 210, 93], [19, 517, 356, 615], [], [1], []], ![[203, 157, 642, 433, 625, 622, 503, 499], [163, 298, 362, 272], [353, 216, 51, 572, 470, 58, 429, 270], [201, 122, 214, 334], [328, 572, 45, 548, 145, 22, 275, 577], [66, 327, 452, 38], [622, 341, 559, 537], [92, 19, 324, 393, 515, 84, 381, 8], [594, 660, 412, 650]], ![[138, 281, 632, 334, 76, 623, 471, 635], [381, 141, 585, 503], [85, 575, 626, 380, 212, 423, 184, 484], [623, 357, 482, 165], [473, 265, 331, 405, 87, 592, 112, 557], [509, 36, 142, 386], [372, 11, 112, 220], [641, 370, 228, 384, 184, 214, 563, 91], [279, 298, 333, 364]], ![[302, 283, 172, 365, 207, 518, 531, 97], [39, 573, 645, 457], [486, 315, 421, 605, 551, 436, 243, 634], [431, 402, 538, 492], [243, 48, 52, 304, 282, 118, 437, 256], [35, 172, 507, 132], [170, 5, 536, 382], [562, 432, 639, 642, 623, 405, 585, 586], [310, 581, 198, 538]], ![[501, 554, 648, 478, 180, 207, 603, 419], [423, 482, 507, 49], [612, 374, 629, 300, 337, 164, 577, 209], [353, 497, 380, 243], [544, 374, 273, 462, 62, 459, 10, 171], [20, 143, 181, 455], [451, 612, 95, 29], [541, 427, 660, 450, 537, 67, 323, 18], [452, 410, 640, 416]]]
 h' := ![![[69, 486, 286, 136, 89], [423, 395, 238, 157, 257], [651, 152, 24, 62, 233], [537, 622, 483, 655, 589], [520, 49, 576, 585, 157], [443, 490, 522, 454, 421], [245, 169, 272, 562, 85], [517, 525, 100], [0, 0, 1], [0, 1]], ![[410, 15, 467, 455, 296], [132, 249, 424, 647, 13], [544, 266, 59, 138, 54], [182, 106, 181, 340, 265], [45, 647, 575, 97, 519], [22, 314, 209, 298, 65], [54, 216, 52, 222, 400], [307, 498, 468, 189, 304], [528, 309, 235, 286, 600], [69, 486, 286, 136, 89]], ![[373, 447, 532, 422, 337], [242, 483, 66, 525, 581], [567, 426, 62, 378, 528], [550, 223, 494, 319, 563], [411, 149, 293, 195, 608], [512, 217, 62, 653, 501], [114, 336, 141, 187, 216], [348, 235, 322, 503, 418], [351, 188, 17, 604, 182], [410, 15, 467, 455, 296]], ![[470, 373, 37, 309, 600], [548, 118, 130, 517, 402], [350, 509, 589, 72, 514], [382, 78, 368, 172, 320], [392, 2, 168, 7, 605], [614, 510, 214, 66, 273], [250, 380, 64, 10, 455], [591, 488, 246, 40, 205], [627, 84, 607, 495, 348], [373, 447, 532, 422, 337]], ![[0, 1], [602, 77, 464, 137, 69], [73, 630, 588, 11, 654], [64, 293, 457, 497, 246], [106, 475, 371, 438, 94], [340, 452, 315, 512, 62], [637, 221, 132, 341, 166], [161, 237, 186, 590, 395], [477, 80, 462, 598, 192], [470, 373, 37, 309, 600]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [370, 361, 622, 654], [], [], []]
 b := ![[], [569, 486, 617, 432, 364], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A661 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 661 1 where
 D := ![[144, 136, 561, 0, 0, 1]]; D' := ![[144, 136, 561, 0, 0, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9]
 n := ![5]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P661P0

def C6610 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A661.D 0) 661 where
  n := 5
  w := ![![661, 0, 0, 0, 0], ![15864, 661, 661, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K661 : KummerData 661 ![I661N0] ![126184873719301] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A661
  C := by
    intro i
    match i with
    | 0 => exact C6610
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 661 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp673 : Fact (Nat.Prime 673) := {out := by norm_num}

def I673N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![673, 0, 0, 0, 0], ![244, 1, 0, 0, 0]] i)))

def I673N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![673, 0, 0, 0, 0], ![727, 3025, 11207, -2180, 22728]] i)))

def P673P0 : CertificateIrreducibleZModOfList' 673 1 2 9 [244, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [], [], [92], [], [432], [429, 1]]]
 h' := ![![[0, 1], [672], [615], [326], [589], [434], [74], [253], [312], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P673P1 : CertificateIrreducibleZModOfList' 673 4 2 9 [79, 494, 312, 429, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [272, 252, 430, 447], [496, 15, 174, 26], [149, 405, 69, 200], [0, 1]]
 g := ![![[644, 50, 458, 448], [36, 21, 25], [500, 154, 600], [317, 361, 453], [540, 87, 337], [484, 638, 416, 363], [578], [244, 1], []], ![[361, 663, 616, 665, 32, 401], [76, 267, 232], [291, 595, 257], [158, 194, 1], [75, 408, 432], [49, 330, 5, 621, 51, 629], [134, 595, 615], [397, 200, 239, 182, 464, 605], [109, 67, 601]], ![[522, 509, 608, 326, 235, 575], [667, 369, 299], [254, 122, 489], [402, 635, 646], [175, 412, 98], [557, 364, 494, 116, 143, 223], [470, 538, 285], [99, 135, 53, 0, 584, 529], [370, 358, 3]], ![[659, 39, 372, 38, 231, 326], [538, 207, 473], [366, 520, 439], [279, 404, 254], [280, 417, 563], [348, 294, 86, 74, 208, 650], [138, 557, 562], [169, 497, 112, 237, 379, 336], [219, 161, 293]]]
 h' := ![![[272, 252, 430, 447], [365, 55, 161, 197], [333, 195, 406, 668], [296, 55, 512, 450], [558, 260, 186, 527], [125, 43, 95, 478], [305, 495, 140, 387], [241, 525, 100], [0, 0, 1], [0, 1]], ![[496, 15, 174, 26], [610, 88, 352, 199], [616, 211, 249, 545], [604, 206, 92, 105], [205, 527, 25, 672], [526, 447, 453, 361], [441, 218, 189, 519], [143, 606, 131, 326], [92, 554, 456, 436], [272, 252, 430, 447]], ![[149, 405, 69, 200], [50, 54, 99, 569], [275, 394, 363, 205], [305, 39, 342, 544], [361, 490, 399, 187], [495, 171, 45, 38], [94, 43, 495, 319], [114, 222, 200, 625], [80, 334, 98, 38], [496, 15, 174, 26]], ![[0, 1], [598, 476, 61, 381], [554, 546, 328, 601], [650, 373, 400, 247], [311, 69, 63, 633], [521, 12, 80, 469], [44, 590, 522, 121], [454, 666, 242, 395], [189, 458, 118, 199], [149, 405, 69, 200]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [26, 164, 275], []]
 b := ![[], [], [350, 432, 457, 533], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A673 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 673 2 where
 D := ![[244, 1], [79, 494, 312, 429, 1]]; D' := ![[244, 1], [79, 494, 312, 429, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P673P0
  | 1 => exact P673P1

def C6730 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A673.D 0) 673 where
  n := 1
  w := ![![673, 0, 0, 0, 0], ![244, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C6731 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A673.D 1) 673 where
  n := 4
  w := ![![673, 0, 0, 0, 0], ![727, 3025, 11207, -2180, 22728]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K673 : KummerData 673 ![I673N0, I673N1] ![673, 205144679041] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A673
  C := by
    intro i
    match i with
    | 0 => exact C6730
    | 1 => exact C6731
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 673 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp677 : Fact (Nat.Prime 677) := {out := by norm_num}

def I677N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![677, 0, 0, 0, 0], ![361, 1, 0, 0, 0]] i)))

def I677N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![677, 0, 0, 0, 0], ![436, 1, 0, 0, 0]] i)))

def I677N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![677, 0, 0, 0, 0], ![656, 1, 0, 0, 0]] i)))

def I677N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![677, 0, 0, 0, 0], ![480, 578, 1, 0, 0]] i)))

def P677P0 : CertificateIrreducibleZModOfList' 677 1 2 9 [361, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [15], [], [], [615], [], [510], [316, 1]]]
 h' := ![![[0, 1], [1], [1], [640], [327], [41], [479], [34], [337], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P677P1 : CertificateIrreducibleZModOfList' 677 1 2 9 [436, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [90], [], [], [210], [], [248], [241, 1]]]
 h' := ![![[0, 1], [676], [26], [38], [145], [512], [306], [192], [536], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P677P2 : CertificateIrreducibleZModOfList' 677 1 2 9 [656, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [548], [], [], [317], [], [182], [21, 1]]]
 h' := ![![[0, 1], [1], [676], [35], [583], [564], [55], [437], [441], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P677P3 : CertificateIrreducibleZModOfList' 677 2 2 9 [480, 578, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [99, 676], [0, 1]]
 g := ![![[461, 589], [388], [630, 380], [316], [115], [24, 458], [461], [575, 323], [1]], ![[550, 88], [388], [338, 297], [316], [115], [7, 219], [461], [56, 354], [1]]]
 h' := ![![[99, 676], [506, 474], [219, 442], [310, 257], [435, 183], [666, 263], [42, 476], [216, 270], [197, 99], [0, 1]], ![[0, 1], [42, 203], [649, 235], [27, 420], [273, 494], [300, 414], [453, 201], [543, 407], [520, 578], [99, 676]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [521]]
 b := ![[], [476, 599]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A677 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 677 4 where
 D := ![[361, 1], [436, 1], [656, 1], [480, 578, 1]]; D' := ![[361, 1], [436, 1], [656, 1], [480, 578, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9, 9, 9]
 n := ![1, 1, 1, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P677P0
  | 1 => exact P677P1
  | 2 => exact P677P2
  | 3 => exact P677P3

def C6770 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A677.D 0) 677 where
  n := 1
  w := ![![677, 0, 0, 0, 0], ![361, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C6771 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A677.D 1) 677 where
  n := 1
  w := ![![677, 0, 0, 0, 0], ![436, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C6772 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A677.D 2) 677 where
  n := 1
  w := ![![677, 0, 0, 0, 0], ![656, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C6773 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A677.D 3) 677 where
  n := 2
  w := ![![677, 0, 0, 0, 0], ![480, 578, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K677 : KummerData 677 ![I677N0, I677N1, I677N2, I677N3] ![677, 677, 677, 458329] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A677
  C := by
    intro i
    match i with
    | 0 => exact C6770
    | 1 => exact C6771
    | 2 => exact C6772
    | 3 => exact C6773
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 677 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp683 : Fact (Nat.Prime 683) := {out := by norm_num}

def I683N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![683, 0, 0, 0, 0], ![116, 1, 0, 0, 0]] i)))

def I683N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![683, 0, 0, 0, 0], ![748, 3011, 11374, -1904, 22728]] i)))

def P683P0 : CertificateIrreducibleZModOfList' 683 1 2 9 [116, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [53], [], [155], [], [246], [], [636], [567, 1]]]
 h' := ![![[0, 1], [682], [108], [461], [644], [150], [144], [671], [479], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P683P1 : CertificateIrreducibleZModOfList' 683 4 2 9 [100, 342, 479, 567, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [542, 330, 435, 149], [669, 275, 483, 369], [271, 77, 448, 165], [0, 1]]
 g := ![![[500, 599, 83, 535], [507, 409, 130, 229], [209, 162, 529], [30, 567, 633, 246], [469, 117, 347], [458, 576, 170, 226], [438], [116, 1], []], ![[650, 565, 611, 203, 47, 491], [617, 598, 208, 527, 522, 522], [460, 652, 282], [187, 229, 130, 516, 213, 218], [151, 117, 19], [677, 468, 278, 230, 137, 142], [551, 514, 62], [55, 562, 117, 220, 44, 628], [174, 266, 345]], ![[513, 510, 682, 504, 110, 275], [252, 503, 658, 296, 122, 245], [674, 670, 391], [137, 188, 41, 467, 201, 326], [355, 300, 27], [129, 364, 290, 212, 280, 515], [78, 470, 438], [238, 508, 228, 225, 187, 305], [329, 229, 244]], ![[152, 373, 1, 396, 121, 143], [344, 408, 230, 18, 407, 61], [48, 342, 639], [529, 612, 391, 400, 379, 169], [56, 645, 625], [376, 240, 435, 655, 494, 501], [167, 441, 389], [347, 201, 131, 622, 157, 119], [34, 220, 588]]]
 h' := ![![[542, 330, 435, 149], [525, 613, 43, 145], [382, 552, 341, 480], [415, 419, 184, 23], [382, 581, 104, 539], [644, 632, 292, 433], [33, 403, 406, 84], [11, 525, 100], [0, 0, 1], [0, 1]], ![[669, 275, 483, 369], [409, 366, 341, 41], [159, 547, 253, 45], [641, 670, 370, 492], [487, 228, 573, 456], [486, 643, 569, 114], [317, 60, 20, 200], [604, 107, 423, 399], [432, 461, 70, 55], [542, 330, 435, 149]], ![[271, 77, 448, 165], [92, 625, 416, 159], [501, 674, 97, 194], [388, 298, 217, 67], [46, 513, 103, 107], [419, 469, 98, 111], [197, 201, 651, 189], [661, 44, 42, 100], [80, 312, 545, 625], [669, 275, 483, 369]], ![[0, 1], [260, 445, 566, 338], [354, 276, 675, 647], [447, 662, 595, 101], [393, 44, 586, 264], [23, 305, 407, 25], [436, 19, 289, 210], [157, 7, 118, 184], [375, 593, 67, 3], [271, 77, 448, 165]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [380, 665, 552], []]
 b := ![[], [], [31, 199, 247, 576], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A683 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 683 2 where
 D := ![[116, 1], [100, 342, 479, 567, 1]]; D' := ![[116, 1], [100, 342, 479, 567, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P683P0
  | 1 => exact P683P1

def C6830 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A683.D 0) 683 where
  n := 1
  w := ![![683, 0, 0, 0, 0], ![116, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C6831 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A683.D 1) 683 where
  n := 4
  w := ![![683, 0, 0, 0, 0], ![748, 3011, 11374, -1904, 22728]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K683 : KummerData 683 ![I683N0, I683N1] ![683, 217611987121] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A683
  C := by
    intro i
    match i with
    | 0 => exact C6830
    | 1 => exact C6831
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 683 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp691 : Fact (Nat.Prime 691) := {out := by norm_num}

def I691N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![691, 0, 0, 0, 0], ![15893, 691, 691, 0, 0]] i)))

def P691P0 : CertificateIrreducibleZModOfList' 691 5 2 9 [173, 166, 591, 0, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [683, 135, 355, 654, 387], [229, 466, 513, 671, 231], [157, 73, 639, 299, 462], [313, 16, 566, 449, 302], [0, 1]]
 g := ![![[32, 331, 206, 644, 520], [277, 514, 136, 385, 583], [417, 224, 10, 597], [386, 331, 581, 633], [176, 55, 148, 175, 441], [599, 522, 31, 557, 553], [], [1], []], ![[682, 621, 235, 394, 253, 165, 108, 197], [38, 474, 485, 303, 212, 680, 283, 166], [237, 648, 319, 89], [352, 494, 153, 326], [441, 411, 33, 262, 339, 612, 447, 636], [94, 260, 386, 112, 276, 605, 682, 234], [125, 428, 614, 123], [499, 449, 523, 690, 327, 288, 642, 255], [303, 430, 384, 513]], ![[40, 528, 220, 29, 514, 464, 663, 624], [603, 574, 104, 483, 425, 219, 650, 24], [79, 324, 632, 641], [315, 250, 227, 601], [252, 660, 310, 168, 378, 226, 319, 93], [393, 440, 330, 322, 8, 27, 197, 193], [587, 645, 133, 569], [551, 644, 492, 67, 81, 565, 122, 168], [108, 393, 434, 154]], ![[370, 1, 513, 285, 419, 543, 637, 27], [202, 613, 254, 404, 464, 540, 306, 682], [212, 234, 416, 529], [102, 383, 125, 483], [488, 455, 115, 383, 415, 229, 247, 493], [546, 312, 391, 208, 127, 205, 565, 65], [528, 276, 618, 1], [165, 160, 109, 265, 488, 419, 316, 129], [525, 584, 567, 616]], ![[557, 580, 222, 349, 403, 109, 441, 73], [524, 301, 427, 389, 686, 613, 339, 487], [152, 337, 406, 508], [34, 229, 182, 366], [402, 537, 252, 175, 611, 585, 393, 364], [459, 598, 64, 150, 191, 289, 541, 457], [546, 29, 19, 252], [339, 137, 457, 519, 40, 206, 243, 648], [264, 339, 324, 683]]]
 h' := ![![[683, 135, 355, 654, 387], [449, 60, 102, 387, 449], [520, 215, 462, 182, 413], [112, 338, 294, 244, 388], [647, 494, 52, 572, 465], [23, 644, 286, 580, 21], [216, 83, 557, 659, 326], [518, 525, 100], [0, 0, 1], [0, 1]], ![[229, 466, 513, 671, 231], [415, 631, 363, 651, 158], [483, 325, 412, 243, 689], [403, 112, 635, 94, 542], [128, 298, 676, 286, 591], [489, 355, 601, 625, 484], [196, 420, 628, 662, 194], [671, 280, 209, 122, 382], [161, 296, 391, 78, 204], [683, 135, 355, 654, 387]], ![[157, 73, 639, 299, 462], [584, 413, 158, 186, 354], [69, 220, 642, 347, 685], [525, 661, 653, 211, 627], [386, 36, 643, 530, 289], [101, 81, 341, 641, 634], [315, 650, 541, 474, 367], [674, 113, 191, 604, 170], [589, 367, 584, 498, 551], [229, 466, 513, 671, 231]], ![[313, 16, 566, 449, 302], [653, 431, 471, 34, 341], [236, 640, 396, 639, 276], [17, 578, 341, 670, 23], [150, 604, 629, 184, 543], [429, 156, 664, 476, 308], [184, 627, 580, 588, 481], [130, 276, 269, 382, 690], [160, 580, 559, 666, 69], [157, 73, 639, 299, 462]], ![[0, 1], [532, 538, 288, 124, 80], [16, 673, 161, 662, 10], [259, 384, 150, 163, 493], [200, 641, 73, 501, 185], [199, 146, 181, 442, 626], [62, 293, 458, 381, 14], [597, 188, 613, 274, 140], [472, 139, 538, 140, 558], [313, 16, 566, 449, 302]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [620, 356, 524, 243], [], [], []]
 b := ![[], [192, 631, 172, 557, 144], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A691 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 691 1 where
 D := ![[173, 166, 591, 0, 0, 1]]; D' := ![[173, 166, 591, 0, 0, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9]
 n := ![5]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P691P0

def C6910 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A691.D 0) 691 where
  n := 5
  w := ![![691, 0, 0, 0, 0], ![15893, 691, 691, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K691 : KummerData 691 ![I691N0] ![157539780804451] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A691
  C := by
    intro i
    match i with
    | 0 => exact C6910
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 691 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp701 : Fact (Nat.Prime 701) := {out := by norm_num}

def I701N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![701, 0, 0, 0, 0], ![155, 1, 0, 0, 0]] i)))

def I701N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![701, 0, 0, 0, 0], ![85, 17, 1, 0, 0]] i)))

def I701N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![701, 0, 0, 0, 0], ![226, 529, 1, 0, 0]] i)))

def P701P0 : CertificateIrreducibleZModOfList' 701 1 2 9 [155, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [199], [362], [54], [590], [], [29], [546, 1]]]
 h' := ![![[0, 1], [1], [700], [671], [42], [381], [102], [412], [191], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P701P1 : CertificateIrreducibleZModOfList' 701 2 2 9 [85, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [684, 700], [0, 1]]
 g := ![![[561, 33], [548], [147, 502], [531, 76], [413, 623], [670, 124], [356], [80, 289], [1]], ![[0, 668], [548], [25, 199], [641, 625], [337, 78], [665, 577], [356], [74, 412], [1]]]
 h' := ![![[684, 700], [94, 88], [123, 232], [430, 156], [646, 130], [532, 656], [521, 261], [210, 227], [616, 684], [0, 1]], ![[0, 1], [0, 613], [385, 469], [582, 545], [539, 571], [596, 45], [290, 440], [557, 474], [204, 17], [684, 700]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [220]]
 b := ![[], [234, 110]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P701P2 : CertificateIrreducibleZModOfList' 701 2 2 9 [226, 529, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [172, 700], [0, 1]]
 g := ![![[632, 518], [659], [61, 68], [158, 589], [506, 45], [625, 671], [43], [657, 142], [1]], ![[0, 183], [659], [541, 633], [522, 112], [535, 656], [372, 30], [43], [546, 559], [1]]]
 h' := ![![[172, 700], [457, 572], [234, 478], [43, 150], [608, 280], [352, 159], [172, 512], [130, 200], [475, 172], [0, 1]], ![[0, 1], [0, 129], [433, 223], [607, 551], [399, 421], [361, 542], [611, 189], [181, 501], [617, 529], [172, 700]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [92]]
 b := ![[], [250, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A701 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 701 3 where
 D := ![[155, 1], [85, 17, 1], [226, 529, 1]]; D' := ![[155, 1], [85, 17, 1], [226, 529, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9, 9]
 n := ![1, 2, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P701P0
  | 1 => exact P701P1
  | 2 => exact P701P2

def C7010 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A701.D 0) 701 where
  n := 1
  w := ![![701, 0, 0, 0, 0], ![155, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C7011 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A701.D 1) 701 where
  n := 2
  w := ![![701, 0, 0, 0, 0], ![85, 17, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C7012 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A701.D 2) 701 where
  n := 2
  w := ![![701, 0, 0, 0, 0], ![226, 529, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K701 : KummerData 701 ![I701N0, I701N1, I701N2] ![701, 491401, 491401] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A701
  C := by
    intro i
    match i with
    | 0 => exact C7010
    | 1 => exact C7011
    | 2 => exact C7012
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 701 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


lemma PB18792I13_primes (p : ℕ) :
  p ∈ Set.range ![647, 653, 659, 661, 673, 677, 683, 691, 701] ↔ Nat.Prime p ∧ 643 < p ∧ p ≤ 701 := by
  rw [← List.mem_ofFn']
  convert primes_range 643 701 (by omega)
  decide

def PB18792I13 : PrimesBelowBoundCertificateInterval O 643 701 18792 where
  m := 9
  g := ![2, 2, 3, 1, 2, 4, 2, 1, 3]
  P := ![647, 653, 659, 661, 673, 677, 683, 691, 701]
  hP := PB18792I13_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I647N0, I647N1]
    · exact ![I653N0, I653N1]
    · exact ![I659N0, I659N1, I659N2]
    · exact ![I661N0]
    · exact ![I673N0, I673N1]
    · exact ![I677N0, I677N1, I677N2, I677N3]
    · exact ![I683N0, I683N1]
    · exact ![I691N0]
    · exact ![I701N0, I701N1, I701N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · convert (containsPrimesAbove_of_KummerData K647) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K653) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K659) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K661) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K673) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K677) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K683) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K691) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K701) <;> rfl
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![418609, 270840023]
    · exact ![653, 181824635281]
    · exact ![659, 434281, 434281]
    · exact ![126184873719301]
    · exact ![673, 205144679041]
    · exact ![677, 677, 677, 458329]
    · exact ![683, 217611987121]
    · exact ![157539780804451]
    · exact ![701, 491401, 491401]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact (card_quot_of_KummerData K647)
    · exact (card_quot_of_KummerData K653)
    · exact (card_quot_of_KummerData K659)
    · exact (card_quot_of_KummerData K661)
    · exact (card_quot_of_KummerData K673)
    · exact (card_quot_of_KummerData K677)
    · exact (card_quot_of_KummerData K683)
    · exact (card_quot_of_KummerData K691)
    · exact (card_quot_of_KummerData K701)
  β := ![I653N0, I659N0, I673N0, I677N0, I677N1, I677N2, I683N0, I701N0]
  Il := ![[], [I653N0], [I659N0], [], [I673N0], [I677N0, I677N1, I677N2], [I683N0], [], [I701N0]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
