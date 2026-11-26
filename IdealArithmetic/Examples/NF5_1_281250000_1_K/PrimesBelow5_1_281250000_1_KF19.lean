
import IdealArithmetic.Examples.NF5_1_281250000_1_K.RI5_1_281250000_1_K
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 

instance hp1021 : Fact (Nat.Prime 1021) := {out := by norm_num}

def I1021N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1021, 0, 0, 0, 0], ![999, 1, 0, 0, 0]] i)))

def I1021N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1021, 0, 0, 0, 0], ![458, 429, 1, 0, 0]] i)))

def I1021N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1021, 0, 0, 0, 0], ![13, 614, 1, 0, 0]] i)))

def P1021P0 : CertificateIrreducibleZModOfList' 1021 1 2 9 [999, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [17], [765], [272], [3], [277], [917], [484, 22, 1]]]
 h' := ![![[0, 1], [1020], [374], [494], [879], [66], [989], [775], [438], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P1021P1 : CertificateIrreducibleZModOfList' 1021 2 2 9 [458, 429, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [592, 1020], [0, 1]]
 g := ![![[21, 457], [206], [675, 83], [444, 312], [556, 770], [204, 20], [280, 675], [740, 11], [592, 1]], ![[0, 564], [206], [803, 938], [347, 709], [9, 251], [813, 1001], [669, 346], [105, 1010], [163, 1020]]]
 h' := ![![[592, 1020], [29, 388], [213, 472], [848, 444], [602, 851], [500, 774], [406, 212], [52, 480], [450, 824], [0, 1]], ![[0, 1], [0, 633], [904, 549], [278, 577], [20, 170], [279, 247], [327, 809], [374, 541], [220, 197], [592, 1020]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [698]]
 b := ![[], [838, 349]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P1021P2 : CertificateIrreducibleZModOfList' 1021 2 2 9 [13, 614, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [407, 1020], [0, 1]]
 g := ![![[597, 686], [778], [174, 181], [204, 540], [868, 940], [768, 946], [687, 608], [62, 643], [407, 1]], ![[45, 335], [778], [329, 840], [469, 481], [573, 81], [873, 75], [40, 413], [387, 378], [814, 1020]]]
 h' := ![![[407, 1020], [509, 638], [801, 514], [411, 200], [968, 68], [226, 303], [258, 399], [215, 421], [835, 234], [0, 1]], ![[0, 1], [841, 383], [694, 507], [131, 821], [56, 953], [6, 718], [312, 622], [34, 600], [99, 787], [407, 1020]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [178]]
 b := ![[], [777, 89]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A1021 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 1021 3 where
 D := ![[999, 1], [458, 429, 1], [13, 614, 1]]; D' := ![[999, 1], [458, 429, 1], [13, 614, 1]]
 heqm := by decide
 hProd := by decide
 s := ![9, 9, 9]
 n := ![1, 2, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P1021P0
  | 1 => exact P1021P1
  | 2 => exact P1021P2

def C10210 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A1021.D 0) 1021 where
  n := 1
  w := ![![1021, 0, 0, 0, 0], ![999, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C10211 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A1021.D 1) 1021 where
  n := 2
  w := ![![1021, 0, 0, 0, 0], ![458, 429, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C10212 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A1021.D 2) 1021 where
  n := 2
  w := ![![1021, 0, 0, 0, 0], ![13, 614, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K1021 : KummerData 1021 ![I1021N0, I1021N1, I1021N2] ![1021, 1042441, 1042441] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A1021
  C := by
    intro i
    match i with
    | 0 => exact C10210
    | 1 => exact C10211
    | 2 => exact C10212
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 1021 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp1031 : Fact (Nat.Prime 1031) := {out := by norm_num}

def I1031N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1031, 0, 0, 0, 0], ![99, 1, 0, 0, 0]] i)))

def I1031N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1031, 0, 0, 0, 0], ![444, 1, 0, 0, 0]] i)))

def I1031N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1031, 0, 0, 0, 0], ![9, 335, 488, 5, 0]] i)))

def P1031P0 : CertificateIrreducibleZModOfList' 1031 1 2 10 [99, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [729], [94], [], [], [], [], [], [], [932, 1]]]
 h' := ![![[0, 1], [1030], [1004], [929], [78], [438], [50], [303], [300], [522], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P1031P1 : CertificateIrreducibleZModOfList' 1031 1 2 10 [444, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [137], [487], [], [], [], [], [], [], [587, 1]]]
 h' := ![![[0, 1], [1], [282], [480], [339], [49], [1024], [32], [861], [215], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P1031P2 : CertificateIrreducibleZModOfList' 1031 3 2 10 [9, 335, 488, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [287, 706, 599], [256, 324, 432], [0, 1]]
 g := ![![[770, 667, 107], [150, 40, 377], [579, 779, 891], [436, 417], [108, 702], [199, 798], [118, 588], [665, 184], [543, 1], []], ![[874, 117, 26, 742], [546, 602, 799, 630], [993, 555, 168, 1019], [946, 39], [554, 882], [795, 416], [850, 487], [461, 574], [764, 845], [210, 13]], ![[776, 22, 637, 856], [936, 609, 825, 729], [860, 664, 867, 345], [219, 876], [479, 518], [265, 556], [1025, 587], [256, 963], [1004, 463], [377, 13]]]
 h' := ![![[287, 706, 599], [712, 983, 362], [975, 123, 857], [46, 726, 802], [696, 774, 550], [962, 314, 283], [374, 503, 210], [886, 217, 937], [268, 573, 679], [0, 0, 1], [0, 1]], ![[256, 324, 432], [770, 514, 901], [918, 536, 805], [611, 345, 859], [696, 43, 544], [88, 227, 377], [833, 765, 239], [726, 789, 551], [969, 120, 297], [61, 733, 324], [287, 706, 599]], ![[0, 1], [142, 565, 799], [748, 372, 400], [468, 991, 401], [857, 214, 968], [599, 490, 371], [930, 794, 582], [968, 25, 574], [945, 338, 55], [283, 298, 706], [256, 324, 432]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66, 13], []]
 b := ![[], [623, 1011, 432], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A1031 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 1031 3 where
 D := ![[99, 1], [444, 1], [9, 335, 488, 1]]; D' := ![[99, 1], [444, 1], [9, 335, 488, 1]]
 heqm := by decide
 hProd := by decide
 s := ![10, 10, 10]
 n := ![1, 1, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P1031P0
  | 1 => exact P1031P1
  | 2 => exact P1031P2

def C10310 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A1031.D 0) 1031 where
  n := 1
  w := ![![1031, 0, 0, 0, 0], ![99, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C10311 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A1031.D 1) 1031 where
  n := 1
  w := ![![1031, 0, 0, 0, 0], ![444, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C10312 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A1031.D 2) 1031 where
  n := 3
  w := ![![1031, 0, 0, 0, 0], ![9, 335, 488, 5, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K1031 : KummerData 1031 ![I1031N0, I1031N1, I1031N2] ![1031, 1031, 1095912791] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A1031
  C := by
    intro i
    match i with
    | 0 => exact C10310
    | 1 => exact C10311
    | 2 => exact C10312
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 1031 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp1033 : Fact (Nat.Prime 1033) := {out := by norm_num}

def I1033N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1033, 0, 0, 0, 0], ![53, 1, 0, 0, 0]] i)))

def I1033N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1033, 0, 0, 0, 0], ![622, 1, 0, 0, 0]] i)))

def I1033N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1033, 0, 0, 0, 0], ![672, 1, 0, 0, 0]] i)))

def I1033N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1033, 0, 0, 0, 0], ![413, 719, 1, 0, 0]] i)))

def P1033P0 : CertificateIrreducibleZModOfList' 1033 1 2 10 [53, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [288], [], [], [], [], [], [980, 1]]]
 h' := ![![[0, 1], [1032], [678], [231], [317], [862], [795], [521], [427], [743], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P1033P1 : CertificateIrreducibleZModOfList' 1033 1 2 10 [622, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [563], [], [], [], [], [], [411, 1]]]
 h' := ![![[0, 1], [1], [1], [1], [299], [336], [996], [780], [392], [542], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P1033P2 : CertificateIrreducibleZModOfList' 1033 1 2 10 [672, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [186], [], [], [], [], [], [361, 1]]]
 h' := ![![[0, 1], [1], [1], [1], [435], [330], [378], [881], [744], [163], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P1033P3 : CertificateIrreducibleZModOfList' 1033 2 2 10 [413, 719, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [314, 1032], [0, 1]]
 g := ![![[537, 688], [1014], [324], [783, 1031], [252], [866], [330], [743], [461], [1]], ![[672, 345], [1014], [324], [155, 2], [252], [866], [330], [743], [461], [1]]]
 h' := ![![[314, 1032], [795, 316], [912, 768], [983, 18], [230, 167], [893, 662], [1023, 444], [530, 655], [836, 53], [620, 314], [0, 1]], ![[0, 1], [851, 717], [342, 265], [437, 1015], [1018, 866], [95, 371], [984, 589], [633, 378], [950, 980], [48, 719], [314, 1032]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [340]]
 b := ![[], [168, 170]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A1033 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 1033 4 where
 D := ![[53, 1], [622, 1], [672, 1], [413, 719, 1]]; D' := ![[53, 1], [622, 1], [672, 1], [413, 719, 1]]
 heqm := by decide
 hProd := by decide
 s := ![10, 10, 10, 10]
 n := ![1, 1, 1, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P1033P0
  | 1 => exact P1033P1
  | 2 => exact P1033P2
  | 3 => exact P1033P3

def C10330 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A1033.D 0) 1033 where
  n := 1
  w := ![![1033, 0, 0, 0, 0], ![53, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C10331 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A1033.D 1) 1033 where
  n := 1
  w := ![![1033, 0, 0, 0, 0], ![622, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C10332 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A1033.D 2) 1033 where
  n := 1
  w := ![![1033, 0, 0, 0, 0], ![672, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C10333 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A1033.D 3) 1033 where
  n := 2
  w := ![![1033, 0, 0, 0, 0], ![413, 719, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K1033 : KummerData 1033 ![I1033N0, I1033N1, I1033N2, I1033N3] ![1033, 1033, 1033, 1067089] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A1033
  C := by
    intro i
    match i with
    | 0 => exact C10330
    | 1 => exact C10331
    | 2 => exact C10332
    | 3 => exact C10333
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 1033 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp1039 : Fact (Nat.Prime 1039) := {out := by norm_num}

def I1039N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1039, 0, 0, 0, 0], ![1039, 0, 0, 5195, 0]] i)))

def P1039P0 : CertificateIrreducibleZModOfList' 1039 5 2 10 [739, 250, 0, 1014, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [884, 15, 761, 832, 786], [327, 320, 976, 728, 484], [38, 769, 932, 52, 270], [829, 973, 448, 466, 538], [0, 1]]
 g := ![![[848, 159, 297, 319, 1], [926, 17, 629, 392, 325], [498, 342, 1024, 151, 619], [943, 485, 702, 838, 982], [294, 576, 616, 69], [837, 924, 738, 281], [498, 763, 576, 360], [0, 25, 0, 1], [], []], ![[822, 886, 402, 250, 974, 1009, 1020, 1002], [984, 35, 201, 975, 278, 949, 0, 946], [52, 936, 221, 181, 397, 226, 360, 905], [646, 761, 275, 922, 331, 740, 541, 319], [755, 76, 528, 766], [241, 16, 520, 979], [747, 841, 85, 50], [24, 1026, 36, 543], [218, 880, 186, 196], [755, 818, 842, 630]], ![[371, 760, 860, 415, 494, 528, 464, 910], [250, 485, 750, 14, 96, 327, 433, 272], [210, 519, 730, 913, 275, 989, 611, 692], [102, 515, 891, 415, 816, 215, 975, 334], [292, 766, 204, 199], [1036, 769, 878, 100], [840, 856, 881, 725], [872, 225, 366, 650], [207, 24, 734, 790], [158, 1007, 262, 481]], ![[938, 995, 538, 200, 78, 355, 864, 198], [688, 58, 219, 838, 820, 267, 507, 866], [247, 510, 276, 556, 681, 97, 240, 477], [626, 819, 860, 209, 702, 998, 233, 779], [183, 694, 497, 508], [387, 98, 900, 136], [1038, 993, 973, 293], [249, 702, 485, 430], [406, 577, 727, 95], [636, 85, 27, 170]], ![[288, 41, 34, 526, 530, 72, 464, 334], [940, 108, 843, 231, 408, 386, 444, 988], [758, 459, 792, 1037, 65, 641, 627, 128], [862, 875, 69, 736, 451, 306, 329, 966], [292, 908, 968, 961], [984, 26, 469, 136], [138, 991, 781, 640], [910, 115, 76, 825], [221, 884, 12, 475], [398, 461, 618, 602]]]
 h' := ![![[884, 15, 761, 832, 786], [387, 3, 793, 679, 1], [823, 1024, 360, 908, 403], [292, 966, 170, 236, 139], [717, 274, 624, 472, 888], [602, 527, 781, 267, 974], [823, 500, 331, 356, 74], [0, 227, 1023, 300, 375], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[327, 320, 976, 728, 484], [772, 451, 902, 12, 491], [345, 213, 180, 353, 407], [522, 762, 446, 252, 287], [311, 800, 799, 830, 778], [244, 627, 916, 958, 497], [633, 334, 1, 970, 975], [655, 691, 70, 80, 33], [234, 793, 347, 97, 675], [126, 50, 474, 216, 1025], [884, 15, 761, 832, 786]], ![[38, 769, 932, 52, 270], [362, 191, 960, 52, 72], [696, 456, 353, 180, 968], [885, 401, 873, 146, 132], [494, 981, 394, 728, 793], [270, 483, 89, 763, 745], [992, 567, 838, 60, 1029], [964, 329, 518, 274, 997], [387, 709, 70, 419, 665], [557, 174, 260, 81, 415], [327, 320, 976, 728, 484]], ![[829, 973, 448, 466, 538], [145, 851, 759, 976, 262], [258, 154, 39, 83, 998], [669, 188, 645, 225, 930], [624, 119, 750, 222, 927], [669, 993, 567, 309, 870], [350, 488, 858, 42, 456], [374, 116, 736, 1031, 134], [39, 71, 769, 592, 75], [29, 791, 707, 319, 918], [38, 769, 932, 52, 270]], ![[0, 1], [687, 582, 742, 359, 213], [219, 231, 107, 554, 341], [782, 800, 983, 180, 590], [84, 943, 550, 865, 770], [128, 487, 764, 820, 31], [2, 189, 50, 650, 583], [564, 715, 770, 393, 539], [629, 505, 892, 970, 662], [377, 24, 636, 423, 759], [829, 973, 448, 466, 538]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [827, 515, 46, 995], [], [], []]
 b := ![[], [169, 225, 613, 719, 45], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A1039 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 1039 1 where
 D := ![[739, 250, 0, 1014, 0, 1]]; D' := ![[739, 250, 0, 1014, 0, 1]]
 heqm := by decide
 hProd := by decide
 s := ![10]
 n := ![5]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P1039P0

def C10390 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A1039.D 0) 1039 where
  n := 5
  w := ![![1039, 0, 0, 0, 0], ![1039, 0, 0, 5195, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K1039 : KummerData 1039 ![I1039N0] ![1210814847429199] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A1039
  C := by
    intro i
    match i with
    | 0 => exact C10390
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 1039 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


lemma PB1045I19_primes (p : ℕ) :
  p ∈ Set.range ![1021, 1031, 1033, 1039] ↔ Nat.Prime p ∧ 1019 < p ∧ p ≤ 1044 := by
  rw [← List.mem_ofFn']
  convert primes_range 1019 1044 (by omega)
  decide

def PB1045I19 : PrimesBelowBoundCertificateInterval O 1019 1044 1045 where
  m := 4
  g := ![3, 3, 4, 1]
  P := ![1021, 1031, 1033, 1039]
  hP := PB1045I19_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I1021N0, I1021N1, I1021N2]
    · exact ![I1031N0, I1031N1, I1031N2]
    · exact ![I1033N0, I1033N1, I1033N2, I1033N3]
    · exact ![I1039N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · convert (containsPrimesAbove_of_KummerData K1021) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K1031) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K1033) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K1039) <;> rfl
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![1021, 1042441, 1042441]
    · exact ![1031, 1031, 1095912791]
    · exact ![1033, 1033, 1033, 1067089]
    · exact ![1210814847429199]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact (card_quot_of_KummerData K1021)
    · exact (card_quot_of_KummerData K1031)
    · exact (card_quot_of_KummerData K1033)
    · exact (card_quot_of_KummerData K1039)
  β := ![I1021N0, I1031N0, I1031N1, I1033N0, I1033N1, I1033N2]
  Il := ![[I1021N0], [I1031N0, I1031N1], [I1033N0, I1033N1, I1033N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
