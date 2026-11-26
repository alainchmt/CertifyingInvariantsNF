
import IdealArithmetic.Examples.NF5_1_91125000000_1_K.RI5_1_91125000000_1_K
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 

instance hp2437 : Fact (Nat.Prime 2437) := {out := by norm_num}

def I2437N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2437, 0, 0, 0, 0], ![1235, 1, 0, 0, 0]] i)))

def I2437N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2437, 0, 0, 0, 0], ![803, 5109, 12995, -634, 22728]] i)))

def P2437P0 : CertificateIrreducibleZModOfList' 2437 1 2 11 [1235, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [517], [], [], [], [], [376], [218], [], [1202, 1]]]
 h' := ![![[0, 1], [1], [2436], [1820], [2291], [1883], [2075], [1107], [1277], [1467], [2100], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P2437P1 : CertificateIrreducibleZModOfList' 2437 4 2 11 [155, 1805, 2100, 1202, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2268, 289, 1055, 1252], [81, 1841, 668, 1450], [1323, 306, 714, 2172], [0, 1]]
 g := ![![[913, 987, 1001, 1151], [1813, 2150, 2004], [44, 405, 730, 786], [1886, 251, 1171], [949, 2179, 1945], [809, 1963, 908], [1035, 1357, 2273], [1484, 1733, 2115, 452], [1231, 2330, 1905, 2100], [1], []], ![[1476, 1266, 2286, 1256, 1275, 1132], [2153, 2034, 645], [2076, 445, 1519, 2185, 240, 467], [394, 1529, 1586], [1225, 1438, 372], [1755, 2216, 1226], [1919, 1513, 499], [1684, 890, 896, 1723, 237, 674], [2198, 940, 201, 324, 1230, 1411], [1087, 1526, 884], [1818, 2384, 513]], ![[2084, 655, 761, 2160, 1246, 2197], [1893, 1405, 1738], [261, 117, 2036, 914, 596, 1899], [2160, 1993, 1893], [1800, 2304, 530], [1106, 1272, 1501], [407, 1474, 846], [1312, 846, 2399, 1325, 1081, 390], [846, 1270, 104, 1862, 2366, 1218], [1855, 388, 1856], [2231, 340, 1806]], ![[1629, 2367, 889, 55, 183, 1896], [272, 1807, 1238], [716, 934, 170, 2069, 785, 1660], [2021, 1671, 1597], [2037, 2199, 1538], [2147, 667, 653], [856, 592, 2046], [1175, 194, 1301, 992, 1534, 1027], [1668, 524, 2317, 1603, 104, 2326], [2004, 961, 750], [1226, 1671, 1989]]]
 h' := ![![[2268, 289, 1055, 1252], [1495, 1489, 2050, 2169], [491, 874, 1344, 906], [230, 1684, 1505, 2220], [752, 1268, 294, 152], [365, 661, 625, 1410], [713, 867, 1763, 778], [1495, 1852, 2044, 1635], [1718, 2207, 2248, 1310], [2282, 632, 337, 1235], [0, 0, 1], [0, 1]], ![[81, 1841, 668, 1450], [2150, 707, 1339, 2112], [1390, 2155, 62, 530], [1028, 376, 1424, 743], [973, 2014, 1876, 1121], [2035, 2223, 872, 2384], [2123, 296, 1234, 2249], [2240, 2241, 515, 695], [130, 1065, 792, 527], [1326, 1263, 2097, 2030], [219, 1851, 2382, 1448], [2268, 289, 1055, 1252]], ![[1323, 306, 714, 2172], [1245, 826, 2150, 381], [1632, 2068, 567, 2082], [352, 899, 2218, 1520], [1262, 2380, 124, 624], [829, 1027, 990, 702], [299, 650, 1584, 993], [666, 418, 2227, 697], [325, 744, 1111, 2209], [31, 2284, 911, 219], [1936, 811, 2402, 1546], [81, 1841, 668, 1450]], ![[0, 1], [40, 1852, 1772, 212], [1092, 2214, 464, 1356], [372, 1915, 2164, 391], [348, 1649, 143, 540], [137, 963, 2387, 378], [1613, 624, 293, 854], [87, 363, 88, 1847], [1154, 858, 723, 828], [1868, 695, 1529, 1390], [619, 2212, 89, 1880], [1323, 306, 714, 2172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [332, 887, 1680], []]
 b := ![[], [], [2253, 259, 1684, 2335], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A2437 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 2437 2 where
 D := ![[1235, 1], [155, 1805, 2100, 1202, 1]]; D' := ![[1235, 1], [155, 1805, 2100, 1202, 1]]
 heqm := by decide
 hProd := by decide
 s := ![11, 11]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P2437P0
  | 1 => exact P2437P1

def C24370 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A2437.D 0) 2437 where
  n := 1
  w := ![![2437, 0, 0, 0, 0], ![1235, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C24371 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A2437.D 1) 2437 where
  n := 4
  w := ![![2437, 0, 0, 0, 0], ![803, 5109, 12995, -634, 22728]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K2437 : KummerData 2437 ![I2437N0, I2437N1] ![2437, 35271352782961] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A2437
  C := by
    intro i
    match i with
    | 0 => exact C24370
    | 1 => exact C24371
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 2437 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp2441 : Fact (Nat.Prime 2441) := {out := by norm_num}

def I2441N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2441, 0, 0, 0, 0], ![1088, 1, 0, 0, 0]] i)))

def I2441N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2441, 0, 0, 0, 0], ![458, 209, 1, 0, 0]] i)))

def I2441N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2441, 0, 0, 0, 0], ![1964, 1144, 1, 0, 0]] i)))

def P2441P0 : CertificateIrreducibleZModOfList' 2441 1 2 11 [1088, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [693], [], [], [], [1721], [118], [], [1353, 1]]]
 h' := ![![[0, 1], [2440], [672], [285], [952], [244], [1345], [2240], [989], [353], [2300], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P2441P1 : CertificateIrreducibleZModOfList' 2441 2 2 11 [458, 209, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2232, 2440], [0, 1]]
 g := ![![[1157, 1956], [602], [2172], [1486, 2127], [591], [901], [1826], [646, 591], [117, 1712], [2184], [1]], ![[0, 485], [602], [2172], [1205, 314], [591], [901], [1826], [1618, 1850], [1136, 729], [2184], [1]]]
 h' := ![![[2232, 2440], [1980, 2322], [1950, 133], [451, 1935], [2214, 1679], [1210, 780], [1699, 2131], [1934, 765], [116, 1661], [376, 1057], [1983, 2232], [0, 1]], ![[0, 1], [0, 119], [1004, 2308], [1242, 506], [366, 762], [1737, 1661], [582, 310], [714, 1676], [2030, 780], [1594, 1384], [1726, 209], [2232, 2440]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1803]]
 b := ![[], [2059, 2122]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P2441P2 : CertificateIrreducibleZModOfList' 2441 2 2 11 [1964, 1144, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1297, 2440], [0, 1]]
 g := ![![[1497, 923], [872], [1931], [259, 9], [204], [2312], [1992], [477, 2287], [1961, 761], [360], [1]], ![[97, 1518], [872], [1931], [2168, 2432], [204], [2312], [1992], [901, 154], [373, 1680], [360], [1]]]
 h' := ![![[1297, 2440], [1014, 58], [1246, 1182], [1493, 871], [275, 2438], [1460, 370], [822, 834], [516, 804], [494, 215], [1366, 440], [477, 1297], [0, 1]], ![[0, 1], [569, 2383], [1352, 1259], [997, 1570], [1266, 3], [473, 2071], [1157, 1607], [997, 1637], [1075, 2226], [852, 2001], [837, 1144], [1297, 2440]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [254]]
 b := ![[], [1855, 127]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A2441 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 2441 3 where
 D := ![[1088, 1], [458, 209, 1], [1964, 1144, 1]]; D' := ![[1088, 1], [458, 209, 1], [1964, 1144, 1]]
 heqm := by decide
 hProd := by decide
 s := ![11, 11, 11]
 n := ![1, 2, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P2441P0
  | 1 => exact P2441P1
  | 2 => exact P2441P2

def C24410 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A2441.D 0) 2441 where
  n := 1
  w := ![![2441, 0, 0, 0, 0], ![1088, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C24411 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A2441.D 1) 2441 where
  n := 2
  w := ![![2441, 0, 0, 0, 0], ![458, 209, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C24412 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A2441.D 2) 2441 where
  n := 2
  w := ![![2441, 0, 0, 0, 0], ![1964, 1144, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K2441 : KummerData 2441 ![I2441N0, I2441N1, I2441N2] ![2441, 5958481, 5958481] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A2441
  C := by
    intro i
    match i with
    | 0 => exact C24410
    | 1 => exact C24411
    | 2 => exact C24412
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 2441 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp2447 : Fact (Nat.Prime 2447) := {out := by norm_num}

def I2447N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2447, 0, 0, 0, 0], ![2335, 2007, 1, 0, 0]] i)))

def I2447N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2447, 0, 0, 0, 0], ![2063, 400, 440, 2, 0]] i)))

def P2447P0 : CertificateIrreducibleZModOfList' 2447 2 2 11 [2335, 2007, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [440, 2446], [0, 1]]
 g := ![![[1577, 1726], [399, 761], [1300, 1752], [1524, 927], [1120], [1768], [1157], [1601, 1243], [2193, 2352], [287], [1]], ![[0, 721], [0, 1686], [1375, 695], [755, 1520], [1120], [1768], [1157], [393, 1204], [1992, 95], [287], [1]]]
 h' := ![![[440, 2446], [642, 2034], [1227, 114], [1845, 753], [97, 1311], [730, 1150], [1171, 989], [681, 1623], [916, 1018], [642, 2163], [112, 440], [0, 1]], ![[0, 1], [0, 413], [0, 2333], [373, 1694], [1892, 1136], [201, 1297], [765, 1458], [277, 824], [1035, 1429], [479, 284], [399, 2007], [440, 2446]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1355]]
 b := ![[], [217, 1901]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P2447P1 : CertificateIrreducibleZModOfList' 2447 3 2 11 [2063, 399, 440, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2319, 1131, 2340], [2135, 1315, 107], [0, 1]]
 g := ![![[1631, 525, 2114], [573, 294, 1604], [646, 2353, 1032], [253, 717, 288], [301, 2145], [2406, 1330], [1393, 231], [2311, 609, 1848], [1009, 998, 309], [2007, 1], []], ![[2394, 2014, 1305, 2274], [2113, 61, 1329, 2366], [323, 2263, 13, 1361], [90, 396, 177, 1808], [257, 1275], [432, 635], [1369, 1711], [2314, 1032, 675, 1590], [181, 2425, 1092, 1359], [461, 1643], [1032, 1661]], ![[991, 1850, 954, 2024], [252, 2228, 1337, 1965], [2396, 1838, 55, 882], [1299, 1511, 992, 1068], [1227, 235], [2291, 31], [1067, 1820], [2085, 1917, 476, 1313], [1949, 281, 165, 2002], [536, 1827], [818, 1661]]]
 h' := ![![[2319, 1131, 2340], [2249, 846, 1506], [917, 1222, 1192], [1719, 1759, 1203], [1882, 2413, 393], [2279, 572, 1760], [2193, 1995, 1326], [1610, 667, 1785], [830, 1671, 685], [2330, 2207, 2335], [0, 0, 1], [0, 1]], ![[2135, 1315, 107], [1495, 1012, 784], [405, 2395, 337], [1194, 2001, 1389], [1617, 223, 1669], [1335, 1250, 1956], [1359, 84, 850], [989, 2130, 196], [264, 207, 113], [911, 1402, 750], [1576, 142, 1315], [2319, 1131, 2340]], ![[0, 1], [1499, 589, 157], [2280, 1277, 918], [1000, 1134, 2302], [2256, 2258, 385], [2273, 625, 1178], [1486, 368, 271], [540, 2097, 466], [142, 569, 1649], [185, 1285, 1809], [360, 2305, 1131], [2135, 1315, 107]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1030, 1616], []]
 b := ![[], [1479, 408, 907], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A2447 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 2447 2 where
 D := ![[2335, 2007, 1], [2063, 399, 440, 1]]; D' := ![[2335, 2007, 1], [2063, 399, 440, 1]]
 heqm := by decide
 hProd := by decide
 s := ![11, 11]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P2447P0
  | 1 => exact P2447P1

def C24470 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A2447.D 0) 2447 where
  n := 2
  w := ![![2447, 0, 0, 0, 0], ![2335, 2007, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C24471 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A2447.D 1) 2447 where
  n := 3
  w := ![![2447, 0, 0, 0, 0], ![2063, 400, 440, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K2447 : KummerData 2447 ![I2447N0, I2447N1] ![5987809, 14652168623] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A2447
  C := by
    intro i
    match i with
    | 0 => exact C24470
    | 1 => exact C24471
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 2447 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp2459 : Fact (Nat.Prime 2459) := {out := by norm_num}

def I2459N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2459, 0, 0, 0, 0], ![2216, 1, 0, 0, 0]] i)))

def I2459N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2459, 0, 0, 0, 0], ![2280, 1, 0, 0, 0]] i)))

def I2459N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2459, 0, 0, 0, 0], ![792, 1802, 422, 2, 0]] i)))

def P2459P0 : CertificateIrreducibleZModOfList' 2459 1 2 11 [2216, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [678], [], [1539], [1454], [], [], [797], [683], [], [243, 1]]]
 h' := ![![[0, 1], [1], [1878], [209], [1685], [1436], [1381], [1869], [1216], [1089], [33], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P2459P1 : CertificateIrreducibleZModOfList' 2459 1 2 11 [2280, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [1099], [], [481], [1285], [], [], [2345], [1530], [], [179, 1]]]
 h' := ![![[0, 1], [1], [1156], [34], [1328], [1127], [235], [1725], [921], [558], [74], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P2459P2 : CertificateIrreducibleZModOfList' 2459 3 2 11 [792, 1801, 422, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [483, 635, 87], [1554, 1823, 2372], [0, 1]]
 g := ![![[847, 1815, 1873], [611, 136, 2377], [897, 707], [2123, 381, 1285], [571, 2077, 2241], [698, 243], [131, 1283], [453, 2120, 858], [2357, 2120, 2442], [2037, 1], []], ![[503, 453, 2138, 1709], [456, 1946, 795, 1938], [1664, 2107], [1802, 1740, 863, 43], [1632, 2017, 334, 2217], [688, 2156], [1480, 1937], [1481, 1220, 28, 1692], [2106, 112, 389, 416], [1539, 1220], [2417, 192]], ![[2011, 515, 283, 2127], [929, 433, 1615, 227], [1631, 2449], [161, 1920, 223, 1843], [481, 349, 1042, 2301], [1293, 179], [1900, 121], [347, 1692, 1915, 1187], [2017, 926, 1651, 2432], [1232, 2408], [132, 192]]]
 h' := ![![[483, 635, 87], [511, 178, 1431], [1665, 2218, 347], [540, 1923, 2384], [224, 380, 1332], [229, 1023, 2123], [2072, 2418, 1020], [238, 2434, 136], [2096, 390, 76], [2259, 1858, 1694], [0, 0, 1], [0, 1]], ![[1554, 1823, 2372], [142, 2080, 446], [1900, 1075, 1782], [42, 843, 1068], [302, 1791, 2296], [2428, 1586, 240], [1748, 1278, 1807], [1088, 1865, 2312], [1909, 815, 348], [1668, 1771, 1469], [981, 926, 1823], [483, 635, 87]], ![[0, 1], [1334, 201, 582], [2069, 1625, 330], [1650, 2152, 1466], [2178, 288, 1290], [634, 2309, 96], [1541, 1222, 2091], [304, 619, 11], [1701, 1254, 2035], [1444, 1289, 1755], [1371, 1533, 635], [1554, 1823, 2372]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1592, 841], []]
 b := ![[], [602, 1588, 810], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A2459 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 2459 3 where
 D := ![[2216, 1], [2280, 1], [792, 1801, 422, 1]]; D' := ![[2216, 1], [2280, 1], [792, 1801, 422, 1]]
 heqm := by decide
 hProd := by decide
 s := ![11, 11, 11]
 n := ![1, 1, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P2459P0
  | 1 => exact P2459P1
  | 2 => exact P2459P2

def C24590 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A2459.D 0) 2459 where
  n := 1
  w := ![![2459, 0, 0, 0, 0], ![2216, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C24591 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A2459.D 1) 2459 where
  n := 1
  w := ![![2459, 0, 0, 0, 0], ![2280, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C24592 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A2459.D 2) 2459 where
  n := 3
  w := ![![2459, 0, 0, 0, 0], ![792, 1802, 422, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K2459 : KummerData 2459 ![I2459N0, I2459N1, I2459N2] ![2459, 2459, 14868788579] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A2459
  C := by
    intro i
    match i with
    | 0 => exact C24590
    | 1 => exact C24591
    | 2 => exact C24592
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 2459 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp2467 : Fact (Nat.Prime 2467) := {out := by norm_num}

def I2467N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2467, 0, 0, 0, 0], ![1804, 1, 0, 0, 0]] i)))

def I2467N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2467, 0, 0, 0, 0], ![1788, 2801, 11338, -1712, 22728]] i)))

def P2467P0 : CertificateIrreducibleZModOfList' 2467 1 2 11 [1804, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [160], [], [], [], [134], [], [1884], [821], [], [663, 1]]]
 h' := ![![[0, 1], [2466], [551], [824], [900], [30], [2416], [790], [1583], [1356], [443], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P2467P1 : CertificateIrreducibleZModOfList' 2467 4 2 11 [1140, 36, 443, 663, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2085, 1741, 44, 664], [2052, 2079, 839, 1817], [134, 1113, 1584, 2453], [0, 1]]
 g := ![![[550, 1465, 999, 823], [465, 2257, 1334, 394], [1256, 1748, 1976], [2455, 2172, 2168], [798, 1928, 139], [955, 2159, 1661, 741], [1926, 1170, 134], [628, 10, 1194, 1979], [690, 1974, 136, 443], [1], []], ![[1255, 888, 1748, 2310, 34, 712], [730, 2095, 401, 509, 1813, 1453], [1795, 1943, 665], [110, 563, 13], [1001, 2425, 1899], [967, 1821, 1470, 1301, 1273, 1718], [416, 717, 1617], [1184, 2407, 1450, 1096, 2327, 1032], [116, 1852, 1577, 77, 1830, 2321], [899, 1420, 1864], [1290, 6, 1770]], ![[733, 66, 594, 1955, 992, 1427], [2105, 1758, 1371, 687, 1435, 2426], [1397, 105, 2447], [1090, 1145, 1384], [311, 1418, 1483], [1588, 1967, 133, 1244, 940, 1772], [146, 2186, 1047], [807, 119, 1181, 1839, 1500, 1868], [236, 1327, 2149, 713, 840, 1333], [385, 157, 1299], [1617, 196, 643]], ![[2016, 759, 1396, 587, 471, 312], [1151, 653, 1763, 2010, 1984, 861], [109, 2057, 2207], [1279, 2339, 1556], [1449, 1298, 1333], [1681, 945, 911, 2057, 465, 458], [2065, 470, 1673], [1236, 2414, 775, 761, 2166, 699], [991, 1315, 1954, 694, 1303, 1736], [847, 347, 1739], [2227, 857, 196]]]
 h' := ![![[2085, 1741, 44, 664], [305, 1536, 1208, 2342], [1181, 1918, 762, 2063], [210, 146, 1115, 1387], [202, 2330, 2163, 148], [1714, 27, 1736, 1591], [791, 1460, 1866, 103], [1977, 1507, 302, 51], [373, 1332, 1767, 847], [1327, 2431, 2024, 1804], [0, 0, 1], [0, 1]], ![[2052, 2079, 839, 1817], [214, 1495, 1191, 177], [1786, 604, 1170, 215], [2098, 233, 1817, 445], [2426, 1358, 837, 1939], [1434, 263, 898, 2304], [71, 509, 2005, 21], [1239, 1705, 1307, 350], [995, 2307, 2097, 1137], [2153, 941, 1039, 305], [103, 583, 924, 2170], [2085, 1741, 44, 664]], ![[134, 1113, 1584, 2453], [946, 1056, 1090, 1782], [1712, 2374, 2198, 913], [1883, 786, 1059, 172], [1060, 474, 26, 826], [330, 1682, 1144, 2038], [1713, 1766, 1805, 2281], [571, 2184, 372, 800], [707, 1277, 883, 1884], [508, 494, 929, 1445], [1471, 916, 971, 1564], [2052, 2079, 839, 1817]], ![[0, 1], [2156, 847, 1445, 633], [2149, 38, 804, 1743], [957, 1302, 943, 463], [195, 772, 1908, 2021], [357, 495, 1156, 1468], [1570, 1199, 1725, 62], [2043, 2005, 486, 1266], [1968, 18, 187, 1066], [1690, 1068, 942, 1380], [450, 968, 571, 1200], [134, 1113, 1584, 2453]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [857, 436, 2005], []]
 b := ![[], [], [2372, 404, 1235, 895], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A2467 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 2467 2 where
 D := ![[1804, 1], [1140, 36, 443, 663, 1]]; D' := ![[1804, 1], [1140, 36, 443, 663, 1]]
 heqm := by decide
 hProd := by decide
 s := ![11, 11]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P2467P0
  | 1 => exact P2467P1

def C24670 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A2467.D 0) 2467 where
  n := 1
  w := ![![2467, 0, 0, 0, 0], ![1804, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C24671 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A2467.D 1) 2467 where
  n := 4
  w := ![![2467, 0, 0, 0, 0], ![1788, 2801, 11338, -1712, 22728]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K2467 : KummerData 2467 ![I2467N0, I2467N1] ![2467, 37040479315921] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A2467
  C := by
    intro i
    match i with
    | 0 => exact C24670
    | 1 => exact C24671
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 2467 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp2473 : Fact (Nat.Prime 2473) := {out := by norm_num}

def I2473N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2473, 0, 0, 0, 0], ![2035, 1, 0, 0, 0]] i)))

def I2473N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2473, 0, 0, 0, 0], ![2852, 4991, 12318, -2162, 22728]] i)))

def P2473P0 : CertificateIrreducibleZModOfList' 2473 1 2 11 [2035, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [357], [], [2034], [], [452], [2032], [], [438, 1]]]
 h' := ![![[0, 1], [1], [2472], [567], [1121], [612], [1185], [136], [2209], [2015], [1423], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P2473P1 : CertificateIrreducibleZModOfList' 2473 4 2 11 [2204, 2451, 1423, 438, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1581, 1623, 643, 732], [1159, 466, 553, 2269], [1768, 383, 1277, 1945], [0, 1]]
 g := ![![[1486, 1202, 793, 1379], [1628, 2408, 1931], [502, 1188, 214], [556, 1329, 1751, 112], [2090, 1433, 2116], [2369, 1953, 1115, 143], [2141, 1055, 2427], [1292, 21, 475, 817], [921, 970, 78, 1423], [1], []], ![[1392, 421, 1138, 1170, 585, 690], [2181, 1283, 1461], [854, 1240, 502], [1244, 1894, 2431, 666, 837, 934], [1601, 2458, 100], [1429, 56, 5, 2293, 1165, 668], [2347, 1483, 687], [1915, 882, 593, 1004, 2355, 831], [2254, 2444, 756, 641, 1183, 764], [703, 933, 150], [1199, 873, 1656]], ![[1271, 1605, 2186, 566, 1911, 1180], [1241, 985, 1936], [1707, 1751, 436], [555, 1136, 2106, 1414, 1567, 1626], [1196, 1986, 1717], [324, 705, 618, 2117, 2381, 56], [445, 406, 1133], [2041, 1892, 561, 1697, 835, 2431], [299, 752, 1329, 152, 1863, 2079], [2398, 1826, 2202], [1682, 94, 2048]], ![[2464, 291, 1872, 2298, 1742, 619], [697, 2071, 2341], [426, 102, 1466], [1219, 2069, 1289, 1471, 1587, 391], [431, 2086, 1205], [296, 421, 198, 1579, 608, 1711], [1259, 1763, 1059], [784, 1282, 531, 2176, 1218, 908], [304, 2441, 1988, 247, 546, 1038], [1796, 1025, 1399], [1555, 1202, 1808]]]
 h' := ![![[1581, 1623, 643, 732], [347, 657, 2115, 865], [1161, 1460, 1798, 1079], [1184, 968, 2100, 2001], [2375, 2328, 1328, 1629], [1700, 1818, 797, 2427], [55, 1210, 446, 601], [1328, 739, 472, 2403], [449, 2387, 2332, 2053], [269, 22, 1050, 2035], [0, 0, 1], [0, 1]], ![[1159, 466, 553, 2269], [1064, 1364, 107, 315], [459, 2383, 1111, 815], [2285, 56, 1592, 2384], [655, 673, 2333, 1751], [1160, 1541, 902, 2463], [1893, 525, 1841, 1998], [2248, 1099, 2358, 1083], [213, 1671, 972, 772], [2088, 1072, 1435, 426], [399, 2001, 683, 2386], [1581, 1623, 643, 732]], ![[1768, 383, 1277, 1945], [568, 2104, 1684, 296], [831, 62, 1397, 2429], [2102, 622, 1202, 1472], [1860, 1054, 1157, 1649], [2102, 994, 2464, 1799], [2017, 1449, 1956, 1849], [1769, 1666, 1894, 105], [2366, 50, 1830, 584], [2132, 1776, 1561, 1040], [341, 2425, 2251, 1043], [1159, 466, 553, 2269]], ![[0, 1], [116, 821, 1040, 997], [1405, 1041, 640, 623], [1176, 827, 52, 1562], [1557, 891, 128, 2390], [43, 593, 783, 730], [1226, 1762, 703, 498], [546, 1442, 222, 1355], [405, 838, 2285, 1537], [542, 2076, 900, 1445], [310, 520, 2011, 1517], [1768, 383, 1277, 1945]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [674, 1044, 1058], []]
 b := ![[], [], [2096, 2395, 1994, 2163], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A2473 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 2473 2 where
 D := ![[2035, 1], [2204, 2451, 1423, 438, 1]]; D' := ![[2035, 1], [2204, 2451, 1423, 438, 1]]
 heqm := by decide
 hProd := by decide
 s := ![11, 11]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P2473P0
  | 1 => exact P2473P1

def C24730 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A2473.D 0) 2473 where
  n := 1
  w := ![![2473, 0, 0, 0, 0], ![2035, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C24731 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A2473.D 1) 2473 where
  n := 4
  w := ![![2473, 0, 0, 0, 0], ![2852, 4991, 12318, -2162, 22728]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K2473 : KummerData 2473 ![I2473N0, I2473N1] ![2473, 37402141201441] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A2473
  C := by
    intro i
    match i with
    | 0 => exact C24730
    | 1 => exact C24731
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 2473 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp2477 : Fact (Nat.Prime 2477) := {out := by norm_num}

def I2477N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2477, 0, 0, 0, 0], ![1098, 1, 0, 0, 0]] i)))

def I2477N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2477, 0, 0, 0, 0], ![1253, 1, 0, 0, 0]] i)))

def I2477N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2477, 0, 0, 0, 0], ![2089, 1, 0, 0, 0]] i)))

def I2477N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2477, 0, 0, 0, 0], ![1227, 514, 1, 0, 0]] i)))

def P2477P0 : CertificateIrreducibleZModOfList' 2477 1 2 11 [1098, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [2001], [1991], [], [2354], [], [462], [100], [], [1379, 1]]]
 h' := ![![[0, 1], [1], [1], [1073], [210], [1296], [1473], [509], [1665], [10], [1782], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P2477P1 : CertificateIrreducibleZModOfList' 2477 1 2 11 [1253, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [2050], [2043], [], [1215], [], [1835], [1399], [], [1224, 1]]]
 h' := ![![[0, 1], [1], [2476], [1339], [156], [960], [2113], [1878], [769], [1322], [2068], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P2477P2 : CertificateIrreducibleZModOfList' 2477 1 2 11 [2089, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [545], [446], [], [1448], [], [825], [2050], [], [388, 1]]]
 h' := ![![[0, 1], [2476], [915], [2135], [1434], [2022], [1956], [567], [283], [1138], [1924], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P2477P3 : CertificateIrreducibleZModOfList' 2477 2 2 11 [1227, 514, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1963, 2476], [0, 1]]
 g := ![![[63, 1072], [2250], [1012, 2141], [183, 2082], [1968], [1092, 494], [1554], [89, 277], [1843, 1003], [1634], [1]], ![[1426, 1405], [2250], [326, 336], [99, 395], [1968], [2307, 1983], [1554], [1377, 2200], [1517, 1474], [1634], [1]]]
 h' := ![![[1963, 2476], [1789, 685], [1730, 517], [866, 410], [544, 385], [173, 1228], [2171, 1008], [2262, 571], [140, 1650], [965, 390], [1250, 1963], [0, 1]], ![[0, 1], [1433, 1792], [1031, 1960], [671, 2067], [814, 2092], [616, 1249], [1752, 1469], [1054, 1906], [1651, 827], [1142, 2087], [407, 514], [1963, 2476]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1728]]
 b := ![[], [1595, 864]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A2477 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 2477 4 where
 D := ![[1098, 1], [1253, 1], [2089, 1], [1227, 514, 1]]; D' := ![[1098, 1], [1253, 1], [2089, 1], [1227, 514, 1]]
 heqm := by decide
 hProd := by decide
 s := ![11, 11, 11, 11]
 n := ![1, 1, 1, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P2477P0
  | 1 => exact P2477P1
  | 2 => exact P2477P2
  | 3 => exact P2477P3

def C24770 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A2477.D 0) 2477 where
  n := 1
  w := ![![2477, 0, 0, 0, 0], ![1098, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C24771 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A2477.D 1) 2477 where
  n := 1
  w := ![![2477, 0, 0, 0, 0], ![1253, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C24772 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A2477.D 2) 2477 where
  n := 1
  w := ![![2477, 0, 0, 0, 0], ![2089, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C24773 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A2477.D 3) 2477 where
  n := 2
  w := ![![2477, 0, 0, 0, 0], ![1227, 514, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K2477 : KummerData 2477 ![I2477N0, I2477N1, I2477N2, I2477N3] ![2477, 2477, 2477, 6135529] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A2477
  C := by
    intro i
    match i with
    | 0 => exact C24770
    | 1 => exact C24771
    | 2 => exact C24772
    | 3 => exact C24773
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 2477 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp2503 : Fact (Nat.Prime 2503) := {out := by norm_num}

def I2503N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2503, 0, 0, 0, 0], ![359, 1, 0, 0, 0]] i)))

def I2503N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2503, 0, 0, 0, 0], ![1200, 1, 0, 0, 0]] i)))

def I2503N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2503, 0, 0, 0, 0], ![1702, 1, 0, 0, 0]] i)))

def I2503N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2503, 0, 0, 0, 0], ![855, 1745, 1, 0, 0]] i)))

def P2503P0 : CertificateIrreducibleZModOfList' 2503 1 2 11 [359, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [251], [2364], [], [], [], [747], [1547], [1022], [], [2144, 1]]]
 h' := ![![[0, 1], [2502], [2344], [2323], [656], [1257], [2151], [293], [1043], [1178], [1228], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P2503P1 : CertificateIrreducibleZModOfList' 2503 1 2 11 [1200, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [2017], [2098], [], [], [], [869], [1085], [1516], [], [1303, 1]]]
 h' := ![![[0, 1], [1], [418], [1519], [823], [818], [951], [2063], [481], [2408], [775], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P2503P2 : CertificateIrreducibleZModOfList' 2503 1 2 11 [1702, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [25], [2378], [], [], [], [277], [321], [992], [], [801, 1]]]
 h' := ![![[0, 1], [1], [2498], [1381], [514], [1152], [1613], [1815], [1141], [558], [833], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P2503P3 : CertificateIrreducibleZModOfList' 2503 2 2 11 [855, 1745, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [758, 2502], [0, 1]]
 g := ![![[690, 1366], [187, 2407], [2414, 1046], [1315], [1420], [2349], [836, 1352], [230, 1427], [838, 1141], [1377], [1]], ![[2379, 1137], [6, 96], [1831, 1457], [1315], [1420], [2349], [1925, 1151], [600, 1076], [2181, 1362], [1377], [1]]]
 h' := ![![[758, 2502], [307, 2375], [1005, 1761], [2454, 1272], [459, 1195], [2206, 1553], [1078, 1008], [1087, 1956], [1871, 1513], [1727, 389], [1648, 758], [0, 1]], ![[0, 1], [900, 128], [1744, 742], [472, 1231], [183, 1308], [467, 950], [1727, 1495], [1959, 547], [2351, 990], [1235, 2114], [522, 1745], [758, 2502]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [370]]
 b := ![[], [2472, 185]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A2503 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 2503 4 where
 D := ![[359, 1], [1200, 1], [1702, 1], [855, 1745, 1]]; D' := ![[359, 1], [1200, 1], [1702, 1], [855, 1745, 1]]
 heqm := by decide
 hProd := by decide
 s := ![11, 11, 11, 11]
 n := ![1, 1, 1, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P2503P0
  | 1 => exact P2503P1
  | 2 => exact P2503P2
  | 3 => exact P2503P3

def C25030 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A2503.D 0) 2503 where
  n := 1
  w := ![![2503, 0, 0, 0, 0], ![359, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C25031 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A2503.D 1) 2503 where
  n := 1
  w := ![![2503, 0, 0, 0, 0], ![1200, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C25032 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A2503.D 2) 2503 where
  n := 1
  w := ![![2503, 0, 0, 0, 0], ![1702, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C25033 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A2503.D 3) 2503 where
  n := 2
  w := ![![2503, 0, 0, 0, 0], ![855, 1745, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K2503 : KummerData 2503 ![I2503N0, I2503N1, I2503N2, I2503N3] ![2503, 2503, 2503, 6265009] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A2503
  C := by
    intro i
    match i with
    | 0 => exact C25030
    | 1 => exact C25031
    | 2 => exact C25032
    | 3 => exact C25033
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 2503 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp2521 : Fact (Nat.Prime 2521) := {out := by norm_num}

def I2521N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2521, 0, 0, 0, 0], ![149, 1, 0, 0, 0]] i)))

def I2521N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2521, 0, 0, 0, 0], ![2226, 1, 0, 0, 0]] i)))

def I2521N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2521, 0, 0, 0, 0], ![1571, 2247, 146, 2, 0]] i)))

def P2521P0 : CertificateIrreducibleZModOfList' 2521 1 2 11 [149, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [2116], [355], [], [2506], [650], [2518], [], [2372, 1]]]
 h' := ![![[0, 1], [2520], [71], [2362], [46], [1124], [2235], [1469], [447], [1170], [2033], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P2521P1 : CertificateIrreducibleZModOfList' 2521 1 2 11 [2226, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [180], [2149], [], [2101], [1363], [698], [], [295, 1]]]
 h' := ![![[0, 1], [2520], [71], [159], [1184], [1507], [2150], [1246], [1709], [1920], [1311], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P2521P2 : CertificateIrreducibleZModOfList' 2521 3 2 11 [1571, 2246, 146, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [187, 2115, 1436], [2188, 405, 1085], [0, 1]]
 g := ![![[1335, 471, 1440], [11, 302], [1730, 2155], [827, 1427, 591], [2403, 2319, 1463], [238, 1081], [109, 280, 2281], [2305, 1609, 1479], [2286, 1691, 566], [2375, 1], []], ![[1640, 2367, 1324, 2316], [224, 2121], [1883, 246], [625, 2110, 45, 649], [1478, 2482, 1328, 1616], [620, 1786], [164, 1982, 757, 1690], [1121, 1505, 75, 2340], [889, 375, 2246, 369], [983, 160], [558, 2439]], ![[2207, 2141, 1286, 953], [1753, 1852], [195, 2095], [926, 1170, 408, 1546], [941, 2333, 201, 2413], [2081, 317], [1520, 1356, 1985, 1532], [2050, 1764, 1678, 583], [2028, 2178, 721, 1355], [2257, 971], [909, 2439]]]
 h' := ![![[187, 2115, 1436], [186, 1429, 1306], [1650, 429, 2211], [1619, 1355, 340], [1345, 696, 945], [2158, 1836, 1401], [189, 703, 1970], [1522, 1152, 834], [1119, 998, 2025], [2476, 1136, 1423], [0, 0, 1], [0, 1]], ![[2188, 405, 1085], [404, 2217, 1991], [1496, 1414, 1420], [954, 578, 1134], [2474, 25, 673], [2236, 785, 2231], [1123, 2295, 2322], [2030, 2038, 452], [1663, 2307, 2000], [692, 630, 1736], [365, 1857, 405], [187, 2115, 1436]], ![[0, 1], [2206, 1396, 1745], [183, 678, 1411], [1103, 588, 1047], [694, 1800, 903], [324, 2421, 1410], [2192, 2044, 750], [1059, 1852, 1235], [891, 1737, 1017], [884, 755, 1883], [1333, 664, 2115], [2188, 405, 1085]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1595, 375], []]
 b := ![[], [1942, 1184, 1894], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A2521 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 2521 3 where
 D := ![[149, 1], [2226, 1], [1571, 2246, 146, 1]]; D' := ![[149, 1], [2226, 1], [1571, 2246, 146, 1]]
 heqm := by decide
 hProd := by decide
 s := ![11, 11, 11]
 n := ![1, 1, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P2521P0
  | 1 => exact P2521P1
  | 2 => exact P2521P2

def C25210 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A2521.D 0) 2521 where
  n := 1
  w := ![![2521, 0, 0, 0, 0], ![149, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C25211 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A2521.D 1) 2521 where
  n := 1
  w := ![![2521, 0, 0, 0, 0], ![2226, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C25212 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A2521.D 2) 2521 where
  n := 3
  w := ![![2521, 0, 0, 0, 0], ![1571, 2247, 146, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K2521 : KummerData 2521 ![I2521N0, I2521N1, I2521N2] ![2521, 2521, 16022066761] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A2521
  C := by
    intro i
    match i with
    | 0 => exact C25210
    | 1 => exact C25211
    | 2 => exact C25212
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 2521 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


lemma PB18792I40_primes (p : ℕ) :
  p ∈ Set.range ![2437, 2441, 2447, 2459, 2467, 2473, 2477, 2503, 2521] ↔ Nat.Prime p ∧ 2423 < p ∧ p ≤ 2521 := by
  rw [← List.mem_ofFn']
  convert primes_range 2423 2521 (by omega)
  decide

def PB18792I40 : PrimesBelowBoundCertificateInterval O 2423 2521 18792 where
  m := 9
  g := ![2, 3, 2, 3, 2, 2, 4, 4, 3]
  P := ![2437, 2441, 2447, 2459, 2467, 2473, 2477, 2503, 2521]
  hP := PB18792I40_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2437N0, I2437N1]
    · exact ![I2441N0, I2441N1, I2441N2]
    · exact ![I2447N0, I2447N1]
    · exact ![I2459N0, I2459N1, I2459N2]
    · exact ![I2467N0, I2467N1]
    · exact ![I2473N0, I2473N1]
    · exact ![I2477N0, I2477N1, I2477N2, I2477N3]
    · exact ![I2503N0, I2503N1, I2503N2, I2503N3]
    · exact ![I2521N0, I2521N1, I2521N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · convert (containsPrimesAbove_of_KummerData K2437) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K2441) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K2447) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K2459) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K2467) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K2473) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K2477) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K2503) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K2521) <;> rfl
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2437, 35271352782961]
    · exact ![2441, 5958481, 5958481]
    · exact ![5987809, 14652168623]
    · exact ![2459, 2459, 14868788579]
    · exact ![2467, 37040479315921]
    · exact ![2473, 37402141201441]
    · exact ![2477, 2477, 2477, 6135529]
    · exact ![2503, 2503, 2503, 6265009]
    · exact ![2521, 2521, 16022066761]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact (card_quot_of_KummerData K2437)
    · exact (card_quot_of_KummerData K2441)
    · exact (card_quot_of_KummerData K2447)
    · exact (card_quot_of_KummerData K2459)
    · exact (card_quot_of_KummerData K2467)
    · exact (card_quot_of_KummerData K2473)
    · exact (card_quot_of_KummerData K2477)
    · exact (card_quot_of_KummerData K2503)
    · exact (card_quot_of_KummerData K2521)
  β := ![I2437N0, I2441N0, I2459N0, I2459N1, I2467N0, I2473N0, I2477N0, I2477N1, I2477N2, I2503N0, I2503N1, I2503N2, I2521N0, I2521N1]
  Il := ![[I2437N0], [I2441N0], [], [I2459N0, I2459N1], [I2467N0], [I2473N0], [I2477N0, I2477N1, I2477N2], [I2503N0, I2503N1, I2503N2], [I2521N0, I2521N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
