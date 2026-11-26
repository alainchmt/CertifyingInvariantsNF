
import IdealArithmetic.Examples.NF5_1_281250000_1_K.RI5_1_281250000_1_K
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 

instance hp647 : Fact (Nat.Prime 647) := {out := by norm_num}

def I647N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![647, 0, 0, 0, 0], ![401, 312, 1, 0, 0]] i)))

def I647N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![647, 0, 0, 0, 0], ![17, 515, 335, 5, 0]] i)))

def P647P0 : CertificateIrreducibleZModOfList' 647 2 2 9 [401, 312, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [335, 646], [0, 1]]
 g := ![![[267, 293], [464, 321], [295, 64], [590], [102], [450], [344], [628, 294], [1]], ![[78, 354], [597, 326], [384, 583], [590], [102], [450], [344], [127, 353], [1]]]
 h' := ![![[335, 646], [272, 429], [106, 145], [579, 8], [487, 282], [469, 117], [188, 107], [502, 310], [246, 335], [0, 1]], ![[0, 1], [353, 218], [156, 502], [24, 639], [495, 365], [197, 530], [448, 540], [185, 337], [540, 312], [335, 646]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [162]]
 b := ![[], [343, 81]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P647P1 : CertificateIrreducibleZModOfList' 647 3 2 9 [17, 515, 335, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [76, 353, 575], [236, 293, 72], [0, 1]]
 g := ![![[300, 24, 54], [353, 227, 67], [335, 594, 185], [96, 509], [7, 425], [276, 150], [244, 2], [426, 312, 1], []], ![[117, 131, 535, 611], [126, 93, 510, 187], [642, 320, 166, 611], [547, 108], [80, 36], [427, 576], [379, 512], [142, 448, 617, 310], [189, 8]], ![[222, 267, 514, 339], [330, 554, 70, 13], [537, 145, 118, 107], [196, 574], [297, 627], [3, 196], [143, 578], [544, 210, 166, 546], [45, 8]]]
 h' := ![![[76, 353, 575], [469, 244, 411], [128, 495, 300], [407, 227, 239], [252, 393, 613], [577, 516, 553], [478, 137, 38], [522, 462, 36], [0, 0, 1], [0, 1]], ![[236, 293, 72], [327, 67, 629], [486, 644, 500], [38, 460, 629], [561, 587, 562], [88, 149, 6], [235, 244, 623], [443, 88, 576], [622, 181, 293], [76, 353, 575]], ![[0, 1], [46, 336, 254], [51, 155, 494], [510, 607, 426], [67, 314, 119], [263, 629, 88], [616, 266, 633], [495, 97, 35], [583, 466, 353], [236, 293, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [493, 144], []]
 b := ![[], [60, 444, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A647 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 647 2 where
 D := ![[401, 312, 1], [17, 515, 335, 1]]; D' := ![[401, 312, 1], [17, 515, 335, 1]]
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
  w := ![![647, 0, 0, 0, 0], ![401, 312, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C6471 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A647.D 1) 647 where
  n := 3
  w := ![![647, 0, 0, 0, 0], ![17, 515, 335, 5, 0]]
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

def I653N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![653, 0, 0, 0, 0], ![43, 87, 1, 0, 0]] i)))

def I653N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![653, 0, 0, 0, 0], ![236, 318, 566, 5, 0]] i)))

def P653P0 : CertificateIrreducibleZModOfList' 653 2 2 9 [43, 87, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [566, 652], [0, 1]]
 g := ![![[245, 420], [622], [406, 36], [141, 122], [188], [531], [123], [20, 386], [1]], ![[273, 233], [622], [539, 617], [628, 531], [188], [531], [123], [394, 267], [1]]]
 h' := ![![[566, 652], [571, 146], [173, 338], [467, 647], [630, 405], [15, 624], [339, 384], [446, 489], [610, 566], [0, 1]], ![[0, 1], [276, 507], [152, 315], [336, 6], [4, 248], [579, 29], [234, 269], [348, 164], [343, 87], [566, 652]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [476]]
 b := ![[], [558, 238]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P653P1 : CertificateIrreducibleZModOfList' 653 3 2 9 [236, 318, 566, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [111, 621, 110], [629, 31, 543], [0, 1]]
 g := ![![[362, 315, 195], [50, 236], [444, 187, 647], [159, 278, 590], [186, 145], [614, 349], [149, 293], [68, 87, 1], []], ![[153, 416, 479, 10], [124, 375], [560, 285, 328, 209], [582, 638, 397, 638], [19, 318], [503, 532], [369, 375], [199, 270, 326, 577], [207, 346]], ![[602, 20, 406, 484], [222, 54], [29, 103, 70, 446], [455, 317, 62, 90], [329, 503], [242, 110], [411, 587], [218, 455, 502, 329], [427, 346]]]
 h' := ![![[111, 621, 110], [297, 644, 272], [349, 517, 397], [350, 380, 385], [524, 167, 289], [4, 346, 485], [426, 478, 210], [277, 289, 216], [0, 0, 1], [0, 1]], ![[629, 31, 543], [220, 219, 259], [595, 38, 612], [617, 363, 189], [369, 174, 556], [197, 14, 202], [525, 558, 320], [515, 473, 612], [37, 175, 31], [111, 621, 110]], ![[0, 1], [156, 443, 122], [31, 98, 297], [234, 563, 79], [422, 312, 461], [83, 293, 619], [514, 270, 123], [567, 544, 478], [366, 478, 621], [629, 31, 543]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [203, 328], []]
 b := ![[], [292, 208, 92], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A653 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 653 2 where
 D := ![[43, 87, 1], [236, 318, 566, 1]]; D' := ![[43, 87, 1], [236, 318, 566, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P653P0
  | 1 => exact P653P1

def C6530 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A653.D 0) 653 where
  n := 2
  w := ![![653, 0, 0, 0, 0], ![43, 87, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C6531 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A653.D 1) 653 where
  n := 3
  w := ![![653, 0, 0, 0, 0], ![236, 318, 566, 5, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K653 : KummerData 653 ![I653N0, I653N1] ![426409, 278445077] where
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

def I659N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![659, 0, 0, 0, 0], ![46, 1, 0, 0, 0]] i)))

def I659N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![659, 0, 0, 0, 0], ![571, 1, 0, 0, 0]] i)))

def I659N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![659, 0, 0, 0, 0], ![536, 515, 42, 5, 0]] i)))

def P659P0 : CertificateIrreducibleZModOfList' 659 1 2 9 [46, 1] where
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
 g := ![![[], [616], [], [], [635], [], [], [210], [613, 1]]]
 h' := ![![[0, 1], [1], [185], [325], [445], [85], [541], [225], [139], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P659P1 : CertificateIrreducibleZModOfList' 659 1 2 9 [571, 1] where
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
 g := ![![[], [322], [], [], [76], [], [], [536], [88, 1]]]
 h' := ![![[0, 1], [658], [540], [378], [98], [441], [638], [379], [495], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P659P2 : CertificateIrreducibleZModOfList' 659 3 2 9 [536, 515, 42, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [310, 185, 117], [307, 473, 542], [0, 1]]
 g := ![![[474, 159, 290], [267, 186, 297], [577, 154], [393, 575], [378, 394, 226], [653, 376], [119, 652], [590, 617, 1], []], ![[606, 319, 600, 635], [363, 216, 376, 165], [404, 569], [86, 211], [262, 602, 339, 256], [649, 627], [406, 630], [370, 103, 650, 154], [165, 509]], ![[529, 58, 612, 214], [37, 631, 627, 118], [467, 624], [26, 11], [483, 36, 369, 2], [15, 624], [416, 545], [609, 142, 137, 418], [399, 509]]]
 h' := ![![[310, 185, 117], [550, 204, 132], [329, 567, 318], [269, 234, 422], [364, 565, 560], [545, 501, 415], [608, 33, 359], [80, 55, 268], [0, 0, 1], [0, 1]], ![[307, 473, 542], [81, 455, 634], [362, 604, 601], [444, 525, 288], [389, 524, 167], [215, 650, 538], [227, 321, 351], [91, 475, 81], [411, 72, 473], [310, 185, 117]], ![[0, 1], [374, 0, 552], [332, 147, 399], [169, 559, 608], [157, 229, 591], [414, 167, 365], [168, 305, 608], [66, 129, 310], [323, 587, 185], [307, 473, 542]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [562, 628], []]
 b := ![[], [578, 401, 648], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A659 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 659 3 where
 D := ![[46, 1], [571, 1], [536, 515, 42, 1]]; D' := ![[46, 1], [571, 1], [536, 515, 42, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9, 9]
 n := ![1, 1, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P659P0
  | 1 => exact P659P1
  | 2 => exact P659P2

def C6590 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A659.D 0) 659 where
  n := 1
  w := ![![659, 0, 0, 0, 0], ![46, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C6591 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A659.D 1) 659 where
  n := 1
  w := ![![659, 0, 0, 0, 0], ![571, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C6592 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A659.D 2) 659 where
  n := 3
  w := ![![659, 0, 0, 0, 0], ![536, 515, 42, 5, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K659 : KummerData 659 ![I659N0, I659N1, I659N2] ![659, 659, 286191179] where
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

def I661N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![661, 0, 0, 0, 0], ![602, 1, 0, 0, 0]] i)))

def I661N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![661, 0, 0, 0, 0], ![515, 356, 1, 0, 0]] i)))

def I661N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![661, 0, 0, 0, 0], ![269, 364, 1, 0, 0]] i)))

def P661P0 : CertificateIrreducibleZModOfList' 661 1 2 9 [602, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [56], [], [220], [], [], [570], [59, 1]]]
 h' := ![![[0, 1], [1], [660], [93], [421], [418], [612], [580], [176], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P661P1 : CertificateIrreducibleZModOfList' 661 2 2 9 [515, 356, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [305, 660], [0, 1]]
 g := ![![[70, 87], [378], [614, 205], [435], [34, 580], [298], [568], [347, 485], [1]], ![[165, 574], [378], [344, 456], [435], [447, 81], [298], [568], [208, 176], [1]]]
 h' := ![![[305, 660], [373, 233], [409, 526], [592, 463], [337, 355], [559, 368], [4, 87], [426, 322], [146, 305], [0, 1]], ![[0, 1], [50, 428], [216, 135], [353, 198], [208, 306], [429, 293], [99, 574], [147, 339], [631, 356], [305, 660]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [162]]
 b := ![[], [537, 81]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P661P2 : CertificateIrreducibleZModOfList' 661 2 2 9 [269, 364, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [297, 660], [0, 1]]
 g := ![![[424, 375], [166], [57, 239], [588], [31, 165], [557], [172], [175, 296], [1]], ![[90, 286], [166], [313, 422], [588], [122, 496], [557], [172], [174, 365], [1]]]
 h' := ![![[297, 660], [8, 130], [531, 362], [206, 30], [254, 221], [411, 53], [247, 72], [517, 425], [392, 297], [0, 1]], ![[0, 1], [280, 531], [302, 299], [523, 631], [452, 440], [288, 608], [479, 589], [491, 236], [27, 364], [297, 660]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [200]]
 b := ![[], [353, 100]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A661 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 661 3 where
 D := ![[602, 1], [515, 356, 1], [269, 364, 1]]; D' := ![[602, 1], [515, 356, 1], [269, 364, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9, 9]
 n := ![1, 2, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P661P0
  | 1 => exact P661P1
  | 2 => exact P661P2

def C6610 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A661.D 0) 661 where
  n := 1
  w := ![![661, 0, 0, 0, 0], ![602, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C6611 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A661.D 1) 661 where
  n := 2
  w := ![![661, 0, 0, 0, 0], ![515, 356, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C6612 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A661.D 2) 661 where
  n := 2
  w := ![![661, 0, 0, 0, 0], ![269, 364, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K661 : KummerData 661 ![I661N0, I661N1, I661N2] ![661, 436921, 436921] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A661
  C := by
    intro i
    match i with
    | 0 => exact C6610
    | 1 => exact C6611
    | 2 => exact C6612
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 661 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp673 : Fact (Nat.Prime 673) := {out := by norm_num}

def I673N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![673, 0, 0, 0, 0], ![17, 1, 0, 0, 0]] i)))

def I673N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![673, 0, 0, 0, 0], ![497, 223, 269, 3280, 10]] i)))

def P673P0 : CertificateIrreducibleZModOfList' 673 1 2 9 [17, 1] where
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
 g := ![![[], [], [], [], [], [212], [], [69], [656, 1]]]
 h' := ![![[0, 1], [672], [615], [326], [589], [434], [317], [173], [289], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P673P1 : CertificateIrreducibleZModOfList' 673 4 2 9 [497, 223, 264, 656, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [512, 40, 269, 5], [55, 144, 224, 62], [123, 488, 180, 606], [0, 1]]
 g := ![![[370, 201, 485, 187], [354, 219, 312], [424, 200, 655], [218, 439, 305], [261, 234, 477], [79, 579, 120, 222], [433, 530, 625], [17, 1], []], ![[144, 654, 563, 137, 660, 427], [370, 360, 81], [100, 154, 618], [114, 222, 29], [190, 103, 178], [137, 518, 615, 47, 104, 94], [306, 374, 13], [110, 147, 443, 194, 220, 264], [668, 423, 25]], ![[188, 514, 617, 213, 393, 253], [85, 166, 96], [155, 224, 323], [456, 265, 343], [400, 350, 8], [479, 103, 378, 564, 485, 409], [159, 647, 146], [668, 667, 347, 90, 487, 639], [339, 250, 479]], ![[565, 505, 139, 254, 599, 433], [313, 209, 333], [647, 526, 604], [113, 27, 220], [654, 428, 192], [453, 465, 474, 251, 108, 413], [17, 191, 647], [429, 84, 665, 345, 191, 82], [309, 372, 451]]]
 h' := ![![[512, 40, 269, 5], [8, 55, 497, 608], [473, 338, 500, 429], [35, 372, 504, 560], [119, 311, 357, 508], [444, 18, 176, 534], [650, 165, 568, 152], [300, 423, 0, 25], [0, 0, 1], [0, 1]], ![[55, 144, 224, 62], [88, 167, 30, 281], [398, 551, 280, 9], [167, 86, 117, 600], [200, 417, 657, 366], [179, 67, 420, 454], [251, 526, 55, 642], [613, 312, 544, 242], [140, 94, 7, 163], [512, 40, 269, 5]], ![[123, 488, 180, 606], [659, 525, 399, 313], [337, 359, 224, 180], [546, 129, 140, 123], [409, 478, 226, 80], [1, 579, 672, 566], [3, 340, 421, 296], [625, 624, 290, 548], [100, 395, 586, 517], [55, 144, 224, 62]], ![[0, 1], [207, 599, 420, 144], [508, 98, 342, 55], [399, 86, 585, 63], [119, 140, 106, 392], [635, 9, 78, 465], [403, 315, 302, 256], [462, 660, 512, 531], [194, 184, 79, 666], [123, 488, 180, 606]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [643, 394, 654], []]
 b := ![[], [], [369, 7, 36, 98], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A673 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 673 2 where
 D := ![[17, 1], [497, 223, 264, 656, 1]]; D' := ![[17, 1], [497, 223, 264, 656, 1]]
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
  w := ![![673, 0, 0, 0, 0], ![17, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C6731 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A673.D 1) 673 where
  n := 4
  w := ![![673, 0, 0, 0, 0], ![497, 223, 269, 3280, 10]]
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

def I677N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![677, 0, 0, 0, 0], ![199, 1, 0, 0, 0]] i)))

def I677N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![677, 0, 0, 0, 0], ![519, 594, 315, 2390, 10]] i)))

def P677P0 : CertificateIrreducibleZModOfList' 677 1 2 9 [199, 1] where
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
 g := ![![[], [], [330], [], [], [85], [], [520], [478, 1]]]
 h' := ![![[0, 1], [1], [676], [522], [100], [10], [46], [101], [335], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P677P1 : CertificateIrreducibleZModOfList' 677 4 2 9 [519, 594, 310, 478, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [626, 348, 276, 35], [156, 420, 517, 50], [94, 585, 561, 592], [0, 1]]
 g := ![![[501, 246, 148, 136], [453, 559, 571], [169, 46, 59, 663], [473, 105, 149], [9, 378, 580], [373, 637, 614, 628], [417, 484, 625], [199, 1], []], ![[99, 139, 369, 146, 490, 504], [651, 207, 598], [412, 71, 517, 176, 440, 96], [555, 76, 40], [422, 369, 641], [135, 235, 85, 161, 441, 327], [669, 205, 636], [324, 408, 73, 488, 351, 353], [497, 419, 548]], ![[78, 533, 481, 463, 22, 285], [114, 625, 493], [143, 17, 596, 316, 631, 566], [210, 504, 144], [416, 550, 527], [317, 487, 304, 518, 415, 181], [293, 389, 582], [4, 256, 149, 370, 295, 238], [47, 153, 469]], ![[205, 442, 467, 160, 356, 106], [322, 620, 208], [49, 8, 209, 397, 642, 354], [318, 273, 199], [178, 251, 106], [204, 375, 433, 135, 211, 394], [582, 603, 555], [26, 160, 81, 609, 615, 560], [239, 591, 455]]]
 h' := ![![[626, 348, 276, 35], [526, 132, 117, 128], [299, 144, 187, 219], [600, 100, 132, 398], [616, 518, 323, 560], [35, 101, 37, 330], [176, 349, 390, 495], [300, 427, 0, 25], [0, 0, 1], [0, 1]], ![[156, 420, 517, 50], [582, 38, 229, 286], [182, 277, 482, 348], [286, 427, 652, 584], [274, 90, 601, 426], [558, 369, 412, 521], [141, 465, 331, 555], [472, 352, 135, 377], [564, 195, 667, 600], [626, 348, 276, 35]], ![[94, 585, 561, 592], [264, 91, 107, 479], [142, 251, 483, 164], [313, 18, 111, 330], [192, 657, 496, 665], [563, 307, 218, 225], [187, 398, 500, 327], [403, 330, 50, 44], [620, 20, 350, 525], [156, 420, 517, 50]], ![[0, 1], [637, 416, 224, 461], [436, 5, 202, 623], [92, 132, 459, 42], [135, 89, 611, 380], [72, 577, 10, 278], [639, 142, 133, 654], [224, 245, 492, 231], [562, 462, 336, 229], [94, 585, 561, 592]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [371, 367, 523], []]
 b := ![[], [], [85, 254, 508, 653], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A677 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 677 2 where
 D := ![[199, 1], [519, 594, 310, 478, 1]]; D' := ![[199, 1], [519, 594, 310, 478, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P677P0
  | 1 => exact P677P1

def C6770 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A677.D 0) 677 where
  n := 1
  w := ![![677, 0, 0, 0, 0], ![199, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C6771 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A677.D 1) 677 where
  n := 4
  w := ![![677, 0, 0, 0, 0], ![519, 594, 315, 2390, 10]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K677 : KummerData 677 ![I677N0, I677N1] ![677, 210065472241] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A677
  C := by
    intro i
    match i with
    | 0 => exact C6770
    | 1 => exact C6771
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 677 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp683 : Fact (Nat.Prime 683) := {out := by norm_num}

def I683N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![683, 0, 0, 0, 0], ![154, 278, 1, 0, 0]] i)))

def I683N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![683, 0, 0, 0, 0], ![548, 609, 405, 5, 0]] i)))

def P683P0 : CertificateIrreducibleZModOfList' 683 2 2 9 [154, 278, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [405, 682], [0, 1]]
 g := ![![[330, 311], [7, 4], [87], [239, 169], [241], [90, 526], [270], [428, 105], [1]], ![[613, 372], [261, 679], [87], [384, 514], [241], [24, 157], [270], [607, 578], [1]]]
 h' := ![![[405, 682], [288, 440], [574, 681], [76, 231], [154, 670], [483, 507], [260, 615], [339, 574], [529, 405], [0, 1]], ![[0, 1], [225, 243], [447, 2], [60, 452], [353, 13], [235, 176], [40, 68], [589, 109], [634, 278], [405, 682]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [270]]
 b := ![[], [324, 135]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P683P1 : CertificateIrreducibleZModOfList' 683 3 2 9 [548, 609, 405, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [130, 148, 61], [148, 534, 622], [0, 1]]
 g := ![![[431, 282, 76], [113, 608, 337], [672, 62], [658, 614, 414], [0, 548], [320, 40, 571], [291, 57], [179, 278, 1], []], ![[171, 15, 632, 249], [659, 40, 624, 477], [348, 552], [664, 306, 66, 613], [83, 264], [616, 383, 272, 436], [157, 282], [56, 260, 418, 555], [674, 306]], ![[609, 663, 240, 54], [586, 261, 581, 383], [663, 332], [113, 576, 161, 366], [350, 659], [134, 517, 380, 624], [435, 260], [143, 560, 256, 487], [113, 306]]]
 h' := ![![[130, 148, 61], [229, 534, 455], [115, 250, 587], [40, 438, 399], [555, 167, 602], [171, 585, 610], [337, 649, 104], [260, 234, 120], [0, 0, 1], [0, 1]], ![[148, 534, 622], [674, 294, 295], [86, 540, 185], [277, 106, 51], [304, 356, 400], [111, 601, 118], [251, 544, 188], [480, 296, 492], [659, 579, 534], [130, 148, 61]], ![[0, 1], [396, 538, 616], [278, 576, 594], [539, 139, 233], [102, 160, 364], [279, 180, 638], [208, 173, 391], [515, 153, 71], [277, 104, 148], [148, 534, 622]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [471, 679], []]
 b := ![[], [321, 274, 224], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A683 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 683 2 where
 D := ![[154, 278, 1], [548, 609, 405, 1]]; D' := ![[154, 278, 1], [548, 609, 405, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P683P0
  | 1 => exact P683P1

def C6830 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A683.D 0) 683 where
  n := 2
  w := ![![683, 0, 0, 0, 0], ![154, 278, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C6831 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A683.D 1) 683 where
  n := 3
  w := ![![683, 0, 0, 0, 0], ![548, 609, 405, 5, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K683 : KummerData 683 ![I683N0, I683N1] ![466489, 318611987] where
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

def I691N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![691, 0, 0, 0, 0], ![59, 1, 0, 0, 0]] i)))

def I691N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![691, 0, 0, 0, 0], ![74, 1, 0, 0, 0]] i)))

def I691N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![691, 0, 0, 0, 0], ![254, 1, 0, 0, 0]] i)))

def I691N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![691, 0, 0, 0, 0], ![334, 1, 0, 0, 0]] i)))

def I691N4 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![691, 0, 0, 0, 0], ![661, 1, 0, 0, 0]] i)))

def P691P0 : CertificateIrreducibleZModOfList' 691 1 2 9 [59, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [82], [], [], [343], [34], [], [676], [632, 1]]]
 h' := ![![[0, 1], [690], [321], [508], [493], [67], [322], [194], [26], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P691P1 : CertificateIrreducibleZModOfList' 691 1 2 9 [74, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [28], [], [], [263], [266], [], [631], [617, 1]]]
 h' := ![![[0, 1], [1], [414], [558], [577], [355], [61], [294], [639], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P691P2 : CertificateIrreducibleZModOfList' 691 1 2 9 [254, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [253], [], [], [1], [253], [], [437], [437, 1]]]
 h' := ![![[0, 1], [1], [437], [253], [437], [1], [437], [253], [253], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P691P3 : CertificateIrreducibleZModOfList' 691 1 2 9 [334, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [631], [], [], [100], [600], [], [431], [357, 1]]]
 h' := ![![[0, 1], [1], [639], [617], [459], [681], [633], [465], [305], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P691P4 : CertificateIrreducibleZModOfList' 691 1 2 9 [661, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [668], [], [], [604], [266], [], [148], [30, 1]]]
 h' := ![![[0, 1], [1], [223], [222], [154], [379], [61], [294], [209], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A691 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 691 5 where
 D := ![[59, 1], [74, 1], [254, 1], [334, 1], [661, 1]]; D' := ![[59, 1], [74, 1], [254, 1], [334, 1], [661, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9, 9, 9, 9]
 n := ![1, 1, 1, 1, 1]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P691P0
  | 1 => exact P691P1
  | 2 => exact P691P2
  | 3 => exact P691P3
  | 4 => exact P691P4

def C6910 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A691.D 0) 691 where
  n := 1
  w := ![![691, 0, 0, 0, 0], ![59, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C6911 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A691.D 1) 691 where
  n := 1
  w := ![![691, 0, 0, 0, 0], ![74, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C6912 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A691.D 2) 691 where
  n := 1
  w := ![![691, 0, 0, 0, 0], ![254, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C6913 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A691.D 3) 691 where
  n := 1
  w := ![![691, 0, 0, 0, 0], ![334, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C6914 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A691.D 4) 691 where
  n := 1
  w := ![![691, 0, 0, 0, 0], ![661, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K691 : KummerData 691 ![I691N0, I691N1, I691N2, I691N3, I691N4] ![691, 691, 691, 691, 691] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A691
  C := by
    intro i
    match i with
    | 0 => exact C6910
    | 1 => exact C6911
    | 2 => exact C6912
    | 3 => exact C6913
    | 4 => exact C6914
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 691 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp701 : Fact (Nat.Prime 701) := {out := by norm_num}

def I701N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![701, 0, 0, 0, 0], ![654, 1, 0, 0, 0]] i)))

def I701N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![701, 0, 0, 0, 0], ![627, 92, 1, 0, 0]] i)))

def I701N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![701, 0, 0, 0, 0], ![89, 656, 1, 0, 0]] i)))

def P701P0 : CertificateIrreducibleZModOfList' 701 1 2 9 [654, 1] where
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
 g := ![![[], [], [331], [529], [612], [636], [], [20], [47, 1]]]
 h' := ![![[0, 1], [700], [135], [328], [23], [450], [340], [239], [106], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P701P1 : CertificateIrreducibleZModOfList' 701 2 2 9 [627, 92, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [609, 700], [0, 1]]
 g := ![![[264, 521], [612], [690, 199], [213, 64], [464, 349], [399, 261], [103], [527, 52], [1]], ![[0, 180], [612], [608, 502], [634, 637], [602, 352], [221, 440], [103], [650, 649], [1]]]
 h' := ![![[609, 700], [575, 532], [588, 251], [340, 30], [688, 8], [84, 511], [581, 573], [443, 96], [74, 609], [0, 1]], ![[0, 1], [0, 169], [629, 450], [384, 671], [653, 693], [39, 190], [440, 128], [23, 605], [126, 92], [609, 700]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [282]]
 b := ![[], [177, 141]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P701P2 : CertificateIrreducibleZModOfList' 701 2 2 9 [89, 656, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [45, 700], [0, 1]]
 g := ![![[31, 638], [676], [253, 142], [382, 322], [314, 400], [201, 155], [293], [397, 623], [1]], ![[0, 63], [676], [334, 559], [151, 379], [88, 301], [166, 546], [293], [392, 78], [1]]]
 h' := ![![[45, 700], [337, 491], [616, 675], [351, 172], [94, 268], [337, 681], [35, 444], [418, 482], [612, 45], [0, 1]], ![[0, 1], [0, 210], [147, 26], [380, 529], [237, 433], [138, 20], [387, 257], [377, 219], [534, 656], [45, 700]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [84]]
 b := ![[], [457, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A701 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 701 3 where
 D := ![[654, 1], [627, 92, 1], [89, 656, 1]]; D' := ![[654, 1], [627, 92, 1], [89, 656, 1]]
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
  w := ![![701, 0, 0, 0, 0], ![654, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C7011 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A701.D 1) 701 where
  n := 2
  w := ![![701, 0, 0, 0, 0], ![627, 92, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C7012 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A701.D 2) 701 where
  n := 2
  w := ![![701, 0, 0, 0, 0], ![89, 656, 1, 0, 0]]
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


lemma PB1045I13_primes (p : ℕ) :
  p ∈ Set.range ![647, 653, 659, 661, 673, 677, 683, 691, 701] ↔ Nat.Prime p ∧ 643 < p ∧ p ≤ 701 := by
  rw [← List.mem_ofFn']
  convert primes_range 643 701 (by omega)
  decide

def PB1045I13 : PrimesBelowBoundCertificateInterval O 643 701 1045 where
  m := 9
  g := ![2, 2, 3, 3, 2, 2, 2, 5, 3]
  P := ![647, 653, 659, 661, 673, 677, 683, 691, 701]
  hP := PB1045I13_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I647N0, I647N1]
    · exact ![I653N0, I653N1]
    · exact ![I659N0, I659N1, I659N2]
    · exact ![I661N0, I661N1, I661N2]
    · exact ![I673N0, I673N1]
    · exact ![I677N0, I677N1]
    · exact ![I683N0, I683N1]
    · exact ![I691N0, I691N1, I691N2, I691N3, I691N4]
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
    · exact ![426409, 278445077]
    · exact ![659, 659, 286191179]
    · exact ![661, 436921, 436921]
    · exact ![673, 205144679041]
    · exact ![677, 210065472241]
    · exact ![466489, 318611987]
    · exact ![691, 691, 691, 691, 691]
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
  β := ![I659N0, I659N1, I661N0, I673N0, I677N0, I691N0, I691N1, I691N2, I691N3, I691N4, I701N0]
  Il := ![[], [], [I659N0, I659N1], [I661N0], [I673N0], [I677N0], [], [I691N0, I691N1, I691N2, I691N3, I691N4], [I701N0]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
