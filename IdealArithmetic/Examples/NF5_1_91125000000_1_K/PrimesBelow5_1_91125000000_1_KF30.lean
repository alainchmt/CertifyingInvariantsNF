
import IdealArithmetic.Examples.NF5_1_91125000000_1_K.RI5_1_91125000000_1_K
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 

instance hp1741 : Fact (Nat.Prime 1741) := {out := by norm_num}

def I1741N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1741, 0, 0, 0, 0], ![126, 1, 0, 0, 0]] i)))

def I1741N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1741, 0, 0, 0, 0], ![205, 1, 0, 0, 0]] i)))

def I1741N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1741, 0, 0, 0, 0], ![1338, 164, 1410, 2, 0]] i)))

def P1741P0 : CertificateIrreducibleZModOfList' 1741 1 2 10 [126, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [152], [1512], [], [], [1300], [300], [], [207, 1615, 1]]]
 h' := ![![[0, 1], [1], [1740], [998], [453], [424], [1595], [502], [1089], [33], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P1741P1 : CertificateIrreducibleZModOfList' 1741 1 2 10 [205, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [1495], [1292], [], [], [34], [233], [], [241, 1536, 1]]]
 h' := ![![[0, 1], [1740], [1682], [1513], [1296], [36], [1735], [983], [1622], [1084], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P1741P2 : CertificateIrreducibleZModOfList' 1741 3 2 10 [1338, 163, 1410, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [993, 642, 830], [1079, 1098, 911], [0, 1]]
 g := ![![[698, 706, 125], [1468, 71], [69, 965, 686], [585, 554, 622], [418, 116], [840, 1130], [1617, 375, 770], [566, 362, 405], [1438, 1619], [1]], ![[1626, 231, 254, 104], [1192, 156], [1643, 678, 848, 792], [1040, 677, 764, 995], [1618, 841], [1584, 1337], [1176, 819, 1031, 68], [159, 1528, 825, 384], [1213, 706], [54, 57, 318, 816]], ![[1061, 374, 1305, 307], [968, 1268], [1033, 1551, 867, 1614], [122, 783, 746, 490], [397, 572], [517, 114], [683, 1452, 1425, 1316], [1292, 591, 703, 1673], [954, 1069], [162, 251, 1290, 925]]]
 h' := ![![[993, 642, 830], [324, 1585, 1464], [1692, 1174, 893], [720, 1267, 817], [1317, 1094, 565], [1682, 1580, 637], [517, 1448, 928], [27, 1289, 399], [257, 1161, 546], [403, 1578, 331], [0, 1]], ![[1079, 1098, 911], [105, 1246, 1624], [736, 154, 1532], [900, 159, 497], [542, 302, 1533], [1435, 239, 1712], [17, 1073, 1009], [27, 178, 266], [120, 970, 1461], [422, 808, 77], [993, 642, 830]], ![[0, 1], [1622, 651, 394], [1624, 413, 1057], [1671, 315, 427], [1403, 345, 1384], [1016, 1663, 1133], [144, 961, 1545], [712, 274, 1076], [797, 1351, 1475], [99, 1096, 1333], [1079, 1098, 911]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [277, 1666], []]
 b := ![[], [1629, 1662, 514], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A1741 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 1741 3 where
 D := ![[126, 1], [205, 1], [1338, 163, 1410, 1]]; D' := ![[126, 1], [205, 1], [1338, 163, 1410, 1]]
 heqm := by decide
 hProd := by decide
 s := ![10, 10, 10]
 n := ![1, 1, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P1741P0
  | 1 => exact P1741P1
  | 2 => exact P1741P2

def C17410 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A1741.D 0) 1741 where
  n := 1
  w := ![![1741, 0, 0, 0, 0], ![126, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C17411 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A1741.D 1) 1741 where
  n := 1
  w := ![![1741, 0, 0, 0, 0], ![205, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C17412 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A1741.D 2) 1741 where
  n := 3
  w := ![![1741, 0, 0, 0, 0], ![1338, 164, 1410, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K1741 : KummerData 1741 ![I1741N0, I1741N1, I1741N2] ![1741, 1741, 5277112021] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A1741
  C := by
    intro i
    match i with
    | 0 => exact C17410
    | 1 => exact C17411
    | 2 => exact C17412
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 1741 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp1747 : Fact (Nat.Prime 1747) := {out := by norm_num}

def I1747N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1747, 0, 0, 0, 0], ![969, 118, 1, 0, 0]] i)))

def I1747N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1747, 0, 0, 0, 0], ![622, 727, 1629, 2, 0]] i)))

def P1747P0 : CertificateIrreducibleZModOfList' 1747 2 2 10 [969, 118, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1629, 1746], [0, 1]]
 g := ![![[1172, 897], [1113, 577], [1495], [91], [753, 1188], [640], [669, 164], [743, 1020], [1229], [1629, 1]], ![[146, 850], [1160, 1170], [1495], [91], [329, 559], [640], [534, 1583], [926, 727], [1229], [1511, 1746]]]
 h' := ![![[1629, 1746], [1149, 1491], [1011, 1573], [186, 1413], [589, 955], [1425, 1048], [1623, 762], [1544, 1134], [1484, 165], [787, 726], [0, 1]], ![[0, 1], [1658, 256], [579, 174], [1164, 334], [1454, 792], [51, 699], [804, 985], [504, 613], [1231, 1582], [722, 1021], [1629, 1746]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [475]]
 b := ![[], [910, 1111]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P1747P1 : CertificateIrreducibleZModOfList' 1747 3 2 10 [622, 726, 1629, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [829, 1309, 433], [1036, 437, 1314], [0, 1]]
 g := ![![[1271, 351, 755], [1245, 662, 418], [213, 1694], [1201, 74], [610, 1628, 277], [158, 1554], [1002, 1237, 368], [1463, 391, 481], [722, 1695], [1]], ![[147, 228, 808, 1731], [685, 249, 846, 845], [1138, 866], [711, 1713], [787, 1290, 464, 514], [464, 376], [979, 846, 1382, 1082], [1492, 282, 1416, 891], [227, 259], [531, 290, 1668, 1394]], ![[1033, 1469, 23, 102], [1008, 815, 734, 1210], [1122, 1430], [766, 803], [552, 274, 121, 1484], [597, 568], [321, 1486, 1080, 1027], [73, 50, 1341, 1010], [336, 1542], [142, 785, 146, 353]]]
 h' := ![![[829, 1309, 433], [1278, 946, 135], [33, 236, 763], [662, 1211, 1534], [1426, 318, 782], [105, 852, 316], [435, 533, 405], [201, 1602, 1525], [692, 771, 96], [1125, 1021, 118], [0, 1]], ![[1036, 437, 1314], [27, 175, 417], [601, 1457, 616], [1142, 1731, 1520], [315, 575, 750], [564, 1142, 378], [549, 349, 723], [416, 715, 925], [1116, 1603, 190], [1532, 250, 1005], [829, 1309, 433]], ![[0, 1], [214, 626, 1195], [1335, 54, 368], [477, 552, 440], [1230, 854, 215], [523, 1500, 1053], [906, 865, 619], [557, 1177, 1044], [1019, 1120, 1461], [1375, 476, 624], [1036, 437, 1314]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1483, 43], []]
 b := ![[], [805, 503, 1642], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A1747 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 1747 2 where
 D := ![[969, 118, 1], [622, 726, 1629, 1]]; D' := ![[969, 118, 1], [622, 726, 1629, 1]]
 heqm := by decide
 hProd := by decide
 s := ![10, 10]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P1747P0
  | 1 => exact P1747P1

def C17470 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A1747.D 0) 1747 where
  n := 2
  w := ![![1747, 0, 0, 0, 0], ![969, 118, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C17471 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A1747.D 1) 1747 where
  n := 3
  w := ![![1747, 0, 0, 0, 0], ![622, 727, 1629, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K1747 : KummerData 1747 ![I1747N0, I1747N1] ![3052009, 5331859723] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A1747
  C := by
    intro i
    match i with
    | 0 => exact C17470
    | 1 => exact C17471
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 1747 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp1753 : Fact (Nat.Prime 1753) := {out := by norm_num}

def I1753N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1753, 0, 0, 0, 0], ![287, 1, 0, 0, 0]] i)))

def I1753N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1753, 0, 0, 0, 0], ![658, 1, 0, 0, 0]] i)))

def I1753N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1753, 0, 0, 0, 0], ![1293, 1, 0, 0, 0]] i)))

def I1753N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1753, 0, 0, 0, 0], ![757, 1268, 1, 0, 0]] i)))

def P1753P0 : CertificateIrreducibleZModOfList' 1753 1 2 10 [287, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [868], [141], [], [1646], [1123], [], [1731, 1466, 1]]]
 h' := ![![[0, 1], [1752], [1040], [1563], [1605], [554], [908], [251], [1623], [1055], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P1753P1 : CertificateIrreducibleZModOfList' 1753 1 2 10 [658, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [1449], [934], [], [982], [477], [], [1726, 1095, 1]]]
 h' := ![![[0, 1], [1752], [1040], [190], [731], [561], [701], [1674], [1353], [236], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P1753P2 : CertificateIrreducibleZModOfList' 1753 1 2 10 [1293, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [1612], [1034], [], [403], [1236], [], [1240, 460, 1]]]
 h' := ![![[0, 1], [1], [1], [1], [577], [767], [1315], [588], [1598], [675], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P1753P3 : CertificateIrreducibleZModOfList' 1753 2 2 10 [757, 1268, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [485, 1752], [0, 1]]
 g := ![![[1449, 44], [319], [835], [1704, 123], [1261, 787], [1539], [183, 512], [801, 748], [785], [485, 1]], ![[0, 1709], [319], [835], [4, 1630], [802, 966], [1539], [1330, 1241], [710, 1005], [785], [970, 1752]]]
 h' := ![![[485, 1752], [1332, 84], [253, 1146], [280, 1323], [808, 423], [905, 553], [1709, 388], [181, 346], [838, 808], [985, 1319], [0, 1]], ![[0, 1], [0, 1669], [362, 607], [337, 430], [862, 1330], [901, 1200], [565, 1365], [1456, 1407], [46, 945], [855, 434], [485, 1752]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [685]]
 b := ![[], [1526, 1219]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A1753 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 1753 4 where
 D := ![[287, 1], [658, 1], [1293, 1], [757, 1268, 1]]; D' := ![[287, 1], [658, 1], [1293, 1], [757, 1268, 1]]
 heqm := by decide
 hProd := by decide
 s := ![10, 10, 10, 10]
 n := ![1, 1, 1, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P1753P0
  | 1 => exact P1753P1
  | 2 => exact P1753P2
  | 3 => exact P1753P3

def C17530 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A1753.D 0) 1753 where
  n := 1
  w := ![![1753, 0, 0, 0, 0], ![287, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C17531 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A1753.D 1) 1753 where
  n := 1
  w := ![![1753, 0, 0, 0, 0], ![658, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C17532 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A1753.D 2) 1753 where
  n := 1
  w := ![![1753, 0, 0, 0, 0], ![1293, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C17533 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A1753.D 3) 1753 where
  n := 2
  w := ![![1753, 0, 0, 0, 0], ![757, 1268, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K1753 : KummerData 1753 ![I1753N0, I1753N1, I1753N2, I1753N3] ![1753, 1753, 1753, 3073009] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A1753
  C := by
    intro i
    match i with
    | 0 => exact C17530
    | 1 => exact C17531
    | 2 => exact C17532
    | 3 => exact C17533
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 1753 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp1759 : Fact (Nat.Prime 1759) := {out := by norm_num}

def I1759N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1759, 0, 0, 0, 0], ![66, 1, 0, 0, 0]] i)))

def I1759N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1759, 0, 0, 0, 0], ![13, 598, 1, 0, 0]] i)))

def I1759N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1759, 0, 0, 0, 0], ![363, 1095, 1, 0, 0]] i)))

def P1759P0 : CertificateIrreducibleZModOfList' 1759 1 2 10 [66, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [1146], [703], [862], [8], [], [1149], [196], [], [838, 1693, 1]]]
 h' := ![![[0, 1], [1], [1095], [1155], [1231], [111], [1562], [1136], [1745], [980], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P1759P1 : CertificateIrreducibleZModOfList' 1759 2 2 10 [13, 598, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1161, 1758], [0, 1]]
 g := ![![[46, 406], [818, 1025], [512, 848], [778, 87], [543, 578], [125], [1447, 483], [1558, 1244], [346], [1161, 1]], ![[0, 1353], [0, 734], [0, 911], [1522, 1672], [1422, 1181], [125], [1089, 1276], [1703, 515], [346], [563, 1758]]]
 h' := ![![[1161, 1758], [1679, 747], [380, 1289], [440, 289], [1736, 917], [1102, 1695], [538, 210], [854, 344], [133, 1189], [738, 514], [0, 1]], ![[0, 1], [0, 1012], [0, 470], [0, 1470], [419, 842], [676, 64], [1606, 1549], [945, 1415], [1506, 570], [1191, 1245], [1161, 1758]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [948]]
 b := ![[], [1006, 474]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P1759P2 : CertificateIrreducibleZModOfList' 1759 2 2 10 [363, 1095, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [664, 1758], [0, 1]]
 g := ![![[192, 865], [339, 1210], [491, 902], [133, 144], [557, 710], [800], [888, 555], [1586, 1262], [957], [664, 1]], ![[1118, 894], [1675, 549], [1359, 857], [763, 1615], [585, 1049], [800], [18, 1204], [511, 497], [957], [1328, 1758]]]
 h' := ![![[664, 1758], [73, 1007], [1185, 744], [973, 901], [94, 1747], [877, 246], [1312, 649], [1234, 521], [1533, 1111], [1710, 783], [0, 1]], ![[0, 1], [301, 752], [922, 1015], [1177, 858], [921, 12], [634, 1513], [1293, 1110], [655, 1238], [457, 648], [958, 976], [664, 1758]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46]]
 b := ![[], [1159, 23]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A1759 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 1759 3 where
 D := ![[66, 1], [13, 598, 1], [363, 1095, 1]]; D' := ![[66, 1], [13, 598, 1], [363, 1095, 1]]
 heqm := by decide
 hProd := by decide
 s := ![10, 10, 10]
 n := ![1, 2, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P1759P0
  | 1 => exact P1759P1
  | 2 => exact P1759P2

def C17590 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A1759.D 0) 1759 where
  n := 1
  w := ![![1759, 0, 0, 0, 0], ![66, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C17591 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A1759.D 1) 1759 where
  n := 2
  w := ![![1759, 0, 0, 0, 0], ![13, 598, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C17592 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A1759.D 2) 1759 where
  n := 2
  w := ![![1759, 0, 0, 0, 0], ![363, 1095, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K1759 : KummerData 1759 ![I1759N0, I1759N1, I1759N2] ![1759, 3094081, 3094081] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A1759
  C := by
    intro i
    match i with
    | 0 => exact C17590
    | 1 => exact C17591
    | 2 => exact C17592
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 1759 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp1777 : Fact (Nat.Prime 1777) := {out := by norm_num}

def I1777N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1777, 0, 0, 0, 0], ![458, 1, 0, 0, 0]] i)))

def I1777N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1777, 0, 0, 0, 0], ![2251, 4914, 10973, -400, 22728]] i)))

def P1777P0 : CertificateIrreducibleZModOfList' 1777 1 2 10 [458, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [], [1591], [363], [1300], [1541], [], [78, 1319, 1]]]
 h' := ![![[0, 1], [1], [1776], [1002], [1669], [784], [1672], [1468], [93], [1593], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P1777P1 : CertificateIrreducibleZModOfList' 1777 4 2 10 [1603, 1493, 78, 1319, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [434, 526, 301, 723], [413, 1070, 241, 1168], [1388, 180, 1235, 1663], [0, 1]]
 g := ![![[411, 1113, 696, 1033], [900, 888, 532], [405, 476, 1046], [1220, 769, 1265], [843, 788, 725, 1382], [183, 1469, 19, 1378], [1776, 1235, 1603, 1385], [1641, 1503, 828, 1115], [0, 458, 1], []], ![[1568, 1768, 1428, 711, 616, 1627], [1077, 161, 1366], [17, 1150, 1734], [1056, 1000, 1359], [1351, 1002, 140, 228, 20, 877], [465, 379, 234, 1193, 1664, 588], [1223, 180, 868, 505, 32, 1632], [970, 1291, 792, 330], [1758, 1681, 848], [1161, 887, 1286, 357, 169, 707]], ![[1710, 1341, 1436, 1708, 771, 1752], [164, 622, 69], [7, 1387, 1003], [1027, 194, 1753], [309, 494, 1240, 360, 645, 1048], [368, 534, 411, 1269, 759, 592], [470, 801, 171, 1241, 257, 86], [493, 362, 1450, 1163, 1700, 964], [679, 147, 636], [825, 825, 1595, 958, 676, 833]], ![[375, 69, 477, 1691, 1059, 1304], [1138, 1363, 1009], [6, 208, 782], [880, 511, 338], [1410, 1591, 1207, 567, 661, 211], [542, 891, 1754, 1394, 1667, 846], [1653, 564, 1749, 116, 214, 750], [42, 1248, 146, 285, 66, 1692], [1489, 1171, 1604], [1471, 254, 1052, 405, 886, 474]]]
 h' := ![![[434, 526, 301, 723], [100, 1361, 467, 1568], [1023, 1724, 54, 648], [1362, 1371, 928, 600], [968, 989, 1105, 609], [1633, 224, 449, 1443], [1603, 252, 1014, 983], [1214, 773, 453, 755], [0, 1504, 525, 100], [0, 0, 0, 1], [0, 1]], ![[413, 1070, 241, 1168], [588, 1219, 1434, 1465], [814, 74, 137, 1615], [1052, 1732, 294, 1341], [1731, 1192, 1274, 56], [1173, 235, 1363, 1312], [847, 216, 1725, 455], [1169, 1054, 569, 1147], [1753, 378, 673], [386, 135, 1684, 560], [434, 526, 301, 723]], ![[1388, 180, 1235, 1663], [941, 561, 1112, 1137], [552, 818, 372, 694], [1457, 701, 630, 1288], [1084, 692, 1183, 909], [341, 1294, 689, 98], [527, 1091, 1037, 1215], [1321, 1772, 790, 1317], [637, 958, 623, 730], [776, 153, 796, 1689], [413, 1070, 241, 1168]], ![[0, 1], [1183, 413, 541, 1161], [752, 938, 1214, 597], [1659, 1527, 1702, 325], [573, 681, 1769, 203], [1703, 24, 1053, 701], [201, 218, 1555, 901], [1127, 1732, 1742, 335], [862, 714, 1733, 947], [1099, 1489, 1074, 1304], [1388, 180, 1235, 1663]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [648, 909, 1539], []]
 b := ![[], [], [742, 216, 301, 1123], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A1777 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 1777 2 where
 D := ![[458, 1], [1603, 1493, 78, 1319, 1]]; D' := ![[458, 1], [1603, 1493, 78, 1319, 1]]
 heqm := by decide
 hProd := by decide
 s := ![10, 10]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P1777P0
  | 1 => exact P1777P1

def C17770 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A1777.D 0) 1777 where
  n := 1
  w := ![![1777, 0, 0, 0, 0], ![458, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C17771 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A1777.D 1) 1777 where
  n := 4
  w := ![![1777, 0, 0, 0, 0], ![2251, 4914, 10973, -400, 22728]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K1777 : KummerData 1777 ![I1777N0, I1777N1] ![1777, 9971252437441] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A1777
  C := by
    intro i
    match i with
    | 0 => exact C17770
    | 1 => exact C17771
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 1777 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp1783 : Fact (Nat.Prime 1783) := {out := by norm_num}

def I1783N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1783, 0, 0, 0, 0], ![59, 567, 1, 0, 0]] i)))

def I1783N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1783, 0, 0, 0, 0], ![1577, 491, 1216, 2, 0]] i)))

def P1783P0 : CertificateIrreducibleZModOfList' 1783 2 2 10 [59, 567, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1216, 1782], [0, 1]]
 g := ![![[886, 272], [866, 1099], [1386, 1605], [476], [340, 1745], [293, 36], [210, 1441], [586, 362], [1178], [1216, 1]], ![[0, 1511], [0, 684], [681, 178], [476], [490, 38], [1277, 1747], [1560, 342], [377, 1421], [1178], [649, 1782]]]
 h' := ![![[1216, 1782], [613, 1130], [244, 252], [557, 1556], [1336, 897], [543, 496], [91, 6], [1086, 295], [1511, 618], [1359, 490], [0, 1]], ![[0, 1], [0, 653], [0, 1531], [890, 227], [892, 886], [1025, 1287], [255, 1777], [1423, 1488], [573, 1165], [1677, 1293], [1216, 1782]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1276]]
 b := ![[], [790, 638]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P1783P1 : CertificateIrreducibleZModOfList' 1783 3 2 10 [1577, 490, 1216, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [577, 942, 609], [1773, 840, 1174], [0, 1]]
 g := ![![[1379, 1215, 899], [1584, 237, 1377], [1416, 1355, 1137], [1265, 976], [1233, 640, 324], [1751, 650, 1096], [691, 1585, 301], [1276, 1188, 33], [1677, 549], [1]], ![[895, 734, 786, 866], [1521, 1770, 358, 1051], [1381, 352, 1683, 774], [1475, 1062], [637, 57, 914, 1567], [242, 1594, 607, 1219], [1083, 1740, 168, 1618], [1549, 212, 722, 1199], [252, 1251], [1288, 962, 416, 1438]], ![[1451, 821, 220, 478], [1341, 1445, 403, 1147], [1191, 1053, 1570, 565], [1658, 1287], [10, 104, 990, 765], [143, 521, 1238, 1320], [1544, 1668, 1642, 1343], [18, 956, 501, 158], [201, 939], [323, 1682, 1316, 345]]]
 h' := ![![[577, 942, 609], [15, 1061, 1135], [1067, 650, 132], [1689, 1453, 737], [812, 1136, 756], [540, 660, 18], [1489, 1649, 866], [755, 1701, 96], [987, 597, 169], [206, 1293, 567], [0, 1]], ![[1773, 840, 1174], [547, 1739, 198], [716, 940, 358], [56, 1589, 888], [252, 1509, 312], [395, 373, 1621], [440, 1439, 388], [1200, 1360, 391], [1296, 848, 944], [1057, 669, 1353], [577, 942, 609]], ![[0, 1], [1339, 766, 450], [1051, 193, 1293], [1371, 524, 158], [491, 921, 715], [1632, 750, 144], [847, 478, 529], [1590, 505, 1296], [671, 338, 670], [1350, 1604, 1646], [1773, 840, 1174]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [908, 1691], []]
 b := ![[], [1724, 757, 1303], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A1783 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 1783 2 where
 D := ![[59, 567, 1], [1577, 490, 1216, 1]]; D' := ![[59, 567, 1], [1577, 490, 1216, 1]]
 heqm := by decide
 hProd := by decide
 s := ![10, 10]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P1783P0
  | 1 => exact P1783P1

def C17830 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A1783.D 0) 1783 where
  n := 2
  w := ![![1783, 0, 0, 0, 0], ![59, 567, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C17831 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A1783.D 1) 1783 where
  n := 3
  w := ![![1783, 0, 0, 0, 0], ![1577, 491, 1216, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K1783 : KummerData 1783 ![I1783N0, I1783N1] ![3179089, 5668315687] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A1783
  C := by
    intro i
    match i with
    | 0 => exact C17830
    | 1 => exact C17831
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 1783 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp1787 : Fact (Nat.Prime 1787) := {out := by norm_num}

def I1787N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1787, 0, 0, 0, 0], ![1266, 1217, 1, 0, 0]] i)))

def I1787N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1787, 0, 0, 0, 0], ![1385, 188, 570, 2, 0]] i)))

def P1787P0 : CertificateIrreducibleZModOfList' 1787 2 2 10 [1266, 1217, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [570, 1786], [0, 1]]
 g := ![![[838, 1077], [256, 683], [1278], [531, 681], [1604, 510], [1594, 1378], [1130, 1660], [344, 608], [1016], [570, 1]], ![[0, 710], [0, 1104], [1278], [922, 1106], [1023, 1277], [774, 409], [220, 127], [226, 1179], [1016], [1140, 1786]]]
 h' := ![![[570, 1786], [1138, 230], [49, 1464], [1453, 778], [1155, 1408], [1306, 1129], [807, 110], [524, 152], [748, 1288], [328, 187], [0, 1]], ![[0, 1], [0, 1557], [0, 323], [1737, 1009], [1352, 379], [1516, 658], [962, 1677], [1388, 1635], [451, 499], [1485, 1600], [570, 1786]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [145]]
 b := ![[], [1675, 966]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P1787P1 : CertificateIrreducibleZModOfList' 1787 3 2 10 [1385, 187, 570, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1641, 234, 569], [1363, 1552, 1218], [0, 1]]
 g := ![![[1351, 596, 1023], [546, 467, 1306], [155, 1171], [1504, 1085, 1604], [57, 366, 1637], [1237, 459, 91], [292, 1302, 818], [1144, 25, 534], [1485, 1453], [1]], ![[1066, 997, 126, 1658], [801, 1782, 629, 1174], [1182, 287], [1221, 397, 1363, 173], [58, 1190, 403, 167], [905, 300, 1720, 1282], [958, 1544, 1503, 757], [407, 482, 642, 812], [1273, 168], [145, 1165, 350, 1753]], ![[268, 2, 825, 700], [512, 1389, 1384, 1233], [615, 1436], [647, 1246, 1430, 1231], [1659, 859, 721, 1613], [1423, 155, 1755, 1472], [1146, 960, 1392, 647], [1554, 856, 300, 320], [1220, 992], [1112, 615, 495, 34]]]
 h' := ![![[1641, 234, 569], [1478, 68, 534], [1195, 1104, 1434], [602, 1657, 422], [1470, 1134, 521], [488, 87, 928], [1229, 1320, 164], [629, 343, 1114], [886, 594, 709], [402, 1600, 1217], [0, 1]], ![[1363, 1552, 1218], [1782, 1438, 765], [1272, 530, 1692], [1298, 414, 199], [1552, 1302, 1007], [1197, 1583, 1188], [1649, 270, 1314], [214, 667, 1283], [1563, 565, 1606], [137, 1107, 742], [1641, 234, 569]], ![[0, 1], [713, 281, 488], [606, 153, 448], [392, 1503, 1166], [1156, 1138, 259], [817, 117, 1458], [779, 197, 309], [1459, 777, 1177], [1334, 628, 1259], [1522, 867, 1615], [1363, 1552, 1218]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [115, 547], []]
 b := ![[], [993, 691, 847], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A1787 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 1787 2 where
 D := ![[1266, 1217, 1], [1385, 187, 570, 1]]; D' := ![[1266, 1217, 1], [1385, 187, 570, 1]]
 heqm := by decide
 hProd := by decide
 s := ![10, 10]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P1787P0
  | 1 => exact P1787P1

def C17870 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A1787.D 0) 1787 where
  n := 2
  w := ![![1787, 0, 0, 0, 0], ![1266, 1217, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C17871 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A1787.D 1) 1787 where
  n := 3
  w := ![![1787, 0, 0, 0, 0], ![1385, 188, 570, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K1787 : KummerData 1787 ![I1787N0, I1787N1] ![3193369, 5706550403] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A1787
  C := by
    intro i
    match i with
    | 0 => exact C17870
    | 1 => exact C17871
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 1787 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp1789 : Fact (Nat.Prime 1789) := {out := by norm_num}

def I1789N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1789, 0, 0, 0, 0], ![380, 1, 0, 0, 0]] i)))

def I1789N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1789, 0, 0, 0, 0], ![657, 1, 0, 0, 0]] i)))

def I1789N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1789, 0, 0, 0, 0], ![288, 981, 752, 2, 0]] i)))

def P1789P0 : CertificateIrreducibleZModOfList' 1789 1 2 10 [380, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [774], [483], [1151], [900], [47], [244], [], [1280, 1409, 1]]]
 h' := ![![[0, 1], [1788], [1065], [727], [925], [1488], [30], [308], [328], [208], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P1789P1 : CertificateIrreducibleZModOfList' 1789 1 2 10 [657, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [403], [344], [916], [1560], [604], [1701], [], [500, 1132, 1]]]
 h' := ![![[0, 1], [1], [1], [1195], [1081], [177], [330], [568], [781], [676], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P1789P2 : CertificateIrreducibleZModOfList' 1789 3 2 10 [288, 980, 752, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [128, 1683, 757], [909, 105, 1032], [0, 1]]
 g := ![![[1391, 1216, 930], [296, 26], [1392, 1769, 1306], [1133, 216, 816], [223, 904, 449], [747, 385, 1587], [495, 934, 426], [1270, 1743, 1478], [388, 180], [1]], ![[41, 233, 1003, 446], [329, 169], [1097, 876, 1441, 330], [255, 1757, 1033, 508], [1313, 1746, 280, 1335], [153, 1140, 1762, 59], [632, 260, 1188, 1280], [553, 430, 1618, 409], [1325, 432], [472, 1355, 1293, 1373]], ![[1031, 88, 1360, 295], [1404, 1202], [1583, 295, 642, 667], [909, 997, 1039, 1125], [815, 790, 1059, 317], [446, 252, 1069, 792], [257, 1762, 1099, 442], [1611, 1146, 170, 845], [644, 130], [1025, 163, 578, 416]]]
 h' := ![![[128, 1683, 757], [1178, 328, 108], [1629, 545, 1131], [1083, 1234, 1175], [180, 972, 1398], [1333, 204, 479], [560, 1453, 111], [985, 43, 1198], [1613, 14, 463], [1501, 809, 1037], [0, 1]], ![[909, 105, 1032], [867, 1532, 231], [1125, 948, 1776], [311, 746, 214], [408, 1299, 617], [1548, 30, 777], [302, 768, 607], [1242, 150, 909], [405, 679, 176], [472, 9, 331], [128, 1683, 757]], ![[0, 1], [898, 1718, 1450], [1419, 296, 671], [430, 1598, 400], [768, 1307, 1563], [508, 1555, 533], [451, 1357, 1071], [642, 1596, 1471], [38, 1096, 1150], [1021, 971, 421], [909, 105, 1032]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [841, 758], []]
 b := ![[], [945, 1325, 1183], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A1789 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 1789 3 where
 D := ![[380, 1], [657, 1], [288, 980, 752, 1]]; D' := ![[380, 1], [657, 1], [288, 980, 752, 1]]
 heqm := by decide
 hProd := by decide
 s := ![10, 10, 10]
 n := ![1, 1, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P1789P0
  | 1 => exact P1789P1
  | 2 => exact P1789P2

def C17890 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A1789.D 0) 1789 where
  n := 1
  w := ![![1789, 0, 0, 0, 0], ![380, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C17891 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A1789.D 1) 1789 where
  n := 1
  w := ![![1789, 0, 0, 0, 0], ![657, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C17892 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A1789.D 2) 1789 where
  n := 3
  w := ![![1789, 0, 0, 0, 0], ![288, 981, 752, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K1789 : KummerData 1789 ![I1789N0, I1789N1, I1789N2] ![1789, 1789, 5725732069] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A1789
  C := by
    intro i
    match i with
    | 0 => exact C17890
    | 1 => exact C17891
    | 2 => exact C17892
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 1789 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp1801 : Fact (Nat.Prime 1801) := {out := by norm_num}

def I1801N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1801, 0, 0, 0, 0], ![594, 1, 0, 0, 0]] i)))

def I1801N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1801, 0, 0, 0, 0], ![1240, 275, 1, 0, 0]] i)))

def I1801N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1801, 0, 0, 0, 0], ![1644, 932, 1, 0, 0]] i)))

def P1801P0 : CertificateIrreducibleZModOfList' 1801 1 2 10 [594, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [1315], [], [], [], [], [1275], [1641, 1207, 1]]]
 h' := ![![[0, 1], [1800], [824], [524], [402], [599], [1703], [420], [871], [1388], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P1801P1 : CertificateIrreducibleZModOfList' 1801 2 2 10 [1240, 275, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1526, 1800], [0, 1]]
 g := ![![[1518, 777], [1284], [197], [1321, 283], [487], [422], [1486], [1206], [1387, 572], [1526, 1]], ![[361, 1024], [1284], [197], [939, 1518], [487], [422], [1486], [1206], [774, 1229], [1251, 1800]]]
 h' := ![![[1526, 1800], [904, 1154], [1136, 538], [870, 225], [55, 785], [1752, 1088], [844, 605], [1413, 83], [75, 1215], [611, 544], [0, 1]], ![[0, 1], [530, 647], [868, 1263], [229, 1576], [300, 1016], [1518, 713], [161, 1196], [200, 1718], [936, 586], [494, 1257], [1526, 1800]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [93]]
 b := ![[], [1441, 947]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P1801P2 : CertificateIrreducibleZModOfList' 1801 2 2 10 [1644, 932, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [869, 1800], [0, 1]]
 g := ![![[820, 1546], [1028], [50], [972, 565], [1616], [387], [1733], [544], [1545, 530], [869, 1]], ![[748, 255], [1028], [50], [284, 1236], [1616], [387], [1733], [544], [1059, 1271], [1738, 1800]]]
 h' := ![![[869, 1800], [333, 169], [1479, 1468], [1320, 463], [1626, 304], [1246, 194], [1674, 1146], [1481, 1251], [1231, 1164], [1358, 699], [0, 1]], ![[0, 1], [1313, 1632], [262, 333], [243, 1338], [1055, 1497], [538, 1607], [1595, 655], [796, 550], [585, 637], [51, 1102], [869, 1800]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1253]]
 b := ![[], [187, 1527]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A1801 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 1801 3 where
 D := ![[594, 1], [1240, 275, 1], [1644, 932, 1]]; D' := ![[594, 1], [1240, 275, 1], [1644, 932, 1]]
 heqm := by decide
 hProd := by decide
 s := ![10, 10, 10]
 n := ![1, 2, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P1801P0
  | 1 => exact P1801P1
  | 2 => exact P1801P2

def C18010 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A1801.D 0) 1801 where
  n := 1
  w := ![![1801, 0, 0, 0, 0], ![594, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C18011 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A1801.D 1) 1801 where
  n := 2
  w := ![![1801, 0, 0, 0, 0], ![1240, 275, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C18012 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A1801.D 2) 1801 where
  n := 2
  w := ![![1801, 0, 0, 0, 0], ![1644, 932, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K1801 : KummerData 1801 ![I1801N0, I1801N1, I1801N2] ![1801, 3243601, 3243601] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A1801
  C := by
    intro i
    match i with
    | 0 => exact C18010
    | 1 => exact C18011
    | 2 => exact C18012
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 1801 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


lemma PB18792I30_primes (p : ℕ) :
  p ∈ Set.range ![1741, 1747, 1753, 1759, 1777, 1783, 1787, 1789, 1801] ↔ Nat.Prime p ∧ 1733 < p ∧ p ≤ 1801 := by
  rw [← List.mem_ofFn']
  convert primes_range 1733 1801 (by omega)
  decide

def PB18792I30 : PrimesBelowBoundCertificateInterval O 1733 1801 18792 where
  m := 9
  g := ![3, 2, 4, 3, 2, 2, 2, 3, 3]
  P := ![1741, 1747, 1753, 1759, 1777, 1783, 1787, 1789, 1801]
  hP := PB18792I30_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I1741N0, I1741N1, I1741N2]
    · exact ![I1747N0, I1747N1]
    · exact ![I1753N0, I1753N1, I1753N2, I1753N3]
    · exact ![I1759N0, I1759N1, I1759N2]
    · exact ![I1777N0, I1777N1]
    · exact ![I1783N0, I1783N1]
    · exact ![I1787N0, I1787N1]
    · exact ![I1789N0, I1789N1, I1789N2]
    · exact ![I1801N0, I1801N1, I1801N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · convert (containsPrimesAbove_of_KummerData K1741) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K1747) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K1753) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K1759) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K1777) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K1783) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K1787) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K1789) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K1801) <;> rfl
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![1741, 1741, 5277112021]
    · exact ![3052009, 5331859723]
    · exact ![1753, 1753, 1753, 3073009]
    · exact ![1759, 3094081, 3094081]
    · exact ![1777, 9971252437441]
    · exact ![3179089, 5668315687]
    · exact ![3193369, 5706550403]
    · exact ![1789, 1789, 5725732069]
    · exact ![1801, 3243601, 3243601]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact (card_quot_of_KummerData K1741)
    · exact (card_quot_of_KummerData K1747)
    · exact (card_quot_of_KummerData K1753)
    · exact (card_quot_of_KummerData K1759)
    · exact (card_quot_of_KummerData K1777)
    · exact (card_quot_of_KummerData K1783)
    · exact (card_quot_of_KummerData K1787)
    · exact (card_quot_of_KummerData K1789)
    · exact (card_quot_of_KummerData K1801)
  β := ![I1741N0, I1741N1, I1753N0, I1753N1, I1753N2, I1759N0, I1777N0, I1789N0, I1789N1, I1801N0]
  Il := ![[I1741N0, I1741N1], [], [I1753N0, I1753N1, I1753N2], [I1759N0], [I1777N0], [], [], [I1789N0, I1789N1], [I1801N0]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
