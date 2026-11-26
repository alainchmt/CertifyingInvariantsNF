
import IdealArithmetic.Examples.NF5_1_91125000000_1_K.RI5_1_91125000000_1_K
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 

instance hp2857 : Fact (Nat.Prime 2857) := {out := by norm_num}

def I2857N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2857, 0, 0, 0, 0], ![1457, 1, 0, 0, 0]] i)))

def I2857N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2857, 0, 0, 0, 0], ![1149, 6323, 10993, -238, 22728]] i)))

def P2857P0 : CertificateIrreducibleZModOfList' 2857 1 2 11 [1457, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [2055], [], [392], [], [], [2808], [1033], [1400, 1]]]
 h' := ![![[0, 1], [1], [1], [1], [2682], [256], [57], [1024], [2825], [558], [98], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P2857P1 : CertificateIrreducibleZModOfList' 2857 4 2 11 [501, 2821, 98, 1400, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2688, 1070, 2601, 2800], [893, 2166, 1937, 98], [733, 2477, 1176, 2816], [0, 1]]
 g := ![![[2116, 1906, 2091, 2690], [2437, 473, 2448], [698, 709, 1352], [256, 942, 1876, 2051], [2738, 1129, 918], [720, 1146, 292, 846], [412, 1074, 1302], [439, 900, 55], [1448, 1429], [1457, 1], []], ![[1391, 673, 252, 1202, 667, 1910], [38, 1586, 1993], [1845, 726, 119], [2636, 182, 2761, 1223, 796, 1531], [1737, 994, 181], [1251, 1809, 73, 2626, 2832, 1937], [2642, 2694, 2843], [506, 201, 1593], [1534, 186, 1571, 1856, 72, 1002], [53, 2458, 13, 873, 398, 78], [1053, 358, 392]], ![[431, 2160, 1901, 2483, 2424, 316], [2064, 1905, 188], [2225, 2182, 2631], [1911, 2721, 315, 2627, 781, 2086], [2760, 17, 1568], [2636, 1834, 151, 2001, 1837, 89], [2071, 1759, 2676], [2291, 1769, 867], [1334, 2532, 304, 378, 1148, 1587], [194, 1430, 2662, 1324, 2050, 361], [194, 1970, 1033]], ![[1819, 380, 2760, 1999, 2608, 229], [1058, 288, 2178], [733, 1086, 679], [1365, 1499, 1055, 2410, 2258, 74], [2017, 2033, 519], [1568, 2099, 739, 1518, 1273, 1471], [1408, 1329, 1916], [1198, 1111, 1458], [819, 124, 2548, 2501, 2688, 2068], [2719, 1399, 1904, 531, 2481, 1337], [43, 1474, 1681]]]
 h' := ![![[2688, 1070, 2601, 2800], [2138, 556, 627, 1950], [56, 1414, 467, 663], [309, 2307, 1985, 2343], [1436, 2015, 2181, 1856], [2119, 2485, 1173, 664], [1984, 856, 2447, 1468], [1524, 590, 1420, 439], [230, 1208, 2075, 1017], [1435, 525, 100], [0, 0, 1], [0, 1]], ![[893, 2166, 1937, 98], [1792, 1013, 956, 518], [313, 2323, 1964, 2484], [2047, 621, 1071, 697], [1773, 244, 534, 2839], [25, 2543, 1227, 2325], [2634, 680, 2134, 404], [2062, 1683, 1034, 1669], [1595, 1411, 675, 503], [2439, 2548, 460, 2497], [983, 2579, 1920, 1867], [2688, 1070, 2601, 2800]], ![[733, 2477, 1176, 2816], [19, 1914, 1714, 639], [2148, 2781, 1317, 1681], [1599, 1848, 698, 2284], [2247, 1307, 1296, 2674], [2061, 1133, 794, 114], [2296, 1589, 813, 48], [507, 166, 2445, 2410], [1242, 288, 872, 1023], [2142, 650, 2419, 1862], [290, 63, 83, 1904], [893, 2166, 1937, 98]], ![[0, 1], [2081, 2231, 2417, 2607], [144, 2053, 1966, 886], [41, 938, 1960, 390], [579, 2148, 1703, 1202], [1135, 2410, 2520, 2611], [638, 2589, 320, 937], [404, 418, 815, 1196], [375, 2807, 2092, 314], [601, 1991, 2735, 1355], [1486, 215, 853, 1943], [733, 2477, 1176, 2816]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [2477, 1509, 2225], []]
 b := ![[], [], [178, 1282, 351, 2397], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A2857 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 2857 2 where
 D := ![[1457, 1], [501, 2821, 98, 1400, 1]]; D' := ![[1457, 1], [501, 2821, 98, 1400, 1]]
 heqm := by decide
 hProd := by decide
 s := ![11, 11]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P2857P0
  | 1 => exact P2857P1

def C28570 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A2857.D 0) 2857 where
  n := 1
  w := ![![2857, 0, 0, 0, 0], ![1457, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C28571 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A2857.D 1) 2857 where
  n := 4
  w := ![![2857, 0, 0, 0, 0], ![1149, 6323, 10993, -238, 22728]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K2857 : KummerData 2857 ![I2857N0, I2857N1] ![2857, 66625573677601] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A2857
  C := by
    intro i
    match i with
    | 0 => exact C28570
    | 1 => exact C28571
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 2857 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp2861 : Fact (Nat.Prime 2861) := {out := by norm_num}

def I2861N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2861, 0, 0, 0, 0], ![2364, 1, 0, 0, 0]] i)))

def I2861N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2861, 0, 0, 0, 0], ![1819, 1121, 1, 0, 0]] i)))

def I2861N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2861, 0, 0, 0, 0], ![564, 2237, 1, 0, 0]] i)))

def P2861P0 : CertificateIrreducibleZModOfList' 2861 1 2 11 [2364, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [662], [1103], [], [2683], [], [], [265], [405], [497, 1]]]
 h' := ![![[0, 1], [1], [2860], [1740], [1988], [225], [1526], [1218], [99], [1015], [963], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P2861P1 : CertificateIrreducibleZModOfList' 2861 2 2 11 [1819, 1121, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1740, 2860], [0, 1]]
 g := ![![[2017, 2241], [43], [1624, 623], [1736, 497], [2256], [300, 570], [2183], [2224], [155, 16], [170, 662], [1]], ![[1814, 620], [43], [1325, 2238], [2494, 2364], [2256], [2194, 2291], [2183], [2224], [2246, 2845], [1928, 2199], [1]]]
 h' := ![![[1740, 2860], [856, 2254], [1357, 1350], [760, 485], [2255, 1543], [751, 1420], [436, 2682], [749, 1114], [1294, 1616], [2619, 4], [1042, 1740], [0, 1]], ![[0, 1], [385, 607], [1476, 1511], [665, 2376], [596, 1318], [2508, 1441], [825, 179], [2212, 1747], [771, 1245], [996, 2857], [1704, 1121], [1740, 2860]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1732]]
 b := ![[], [1884, 866]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P2861P2 : CertificateIrreducibleZModOfList' 2861 2 2 11 [564, 2237, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [624, 2860], [0, 1]]
 g := ![![[425, 279], [1589], [103, 2238], [2098, 1004], [2515], [292, 2292], [9], [596], [1350, 289], [133, 280], [1]], ![[0, 2582], [1589], [447, 623], [2035, 1857], [2515], [0, 569], [9], [596], [1443, 2572], [332, 2581], [1]]]
 h' := ![![[624, 2860], [1516, 2180], [1989, 1755], [1182, 674], [990, 1329], [1250, 484], [772, 1631], [1141, 2858], [2487, 1266], [2235, 2844], [2297, 624], [0, 1]], ![[0, 1], [0, 681], [1346, 1106], [1191, 2187], [596, 1532], [0, 2377], [0, 1230], [2130, 3], [2835, 1595], [210, 17], [2577, 2237], [624, 2860]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1500]]
 b := ![[], [602, 750]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A2861 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 2861 3 where
 D := ![[2364, 1], [1819, 1121, 1], [564, 2237, 1]]; D' := ![[2364, 1], [1819, 1121, 1], [564, 2237, 1]]
 heqm := by decide
 hProd := by decide
 s := ![11, 11, 11]
 n := ![1, 2, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P2861P0
  | 1 => exact P2861P1
  | 2 => exact P2861P2

def C28610 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A2861.D 0) 2861 where
  n := 1
  w := ![![2861, 0, 0, 0, 0], ![2364, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C28611 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A2861.D 1) 2861 where
  n := 2
  w := ![![2861, 0, 0, 0, 0], ![1819, 1121, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C28612 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A2861.D 2) 2861 where
  n := 2
  w := ![![2861, 0, 0, 0, 0], ![564, 2237, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K2861 : KummerData 2861 ![I2861N0, I2861N1, I2861N2] ![2861, 8185321, 8185321] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A2861
  C := by
    intro i
    match i with
    | 0 => exact C28610
    | 1 => exact C28611
    | 2 => exact C28612
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 2861 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp2879 : Fact (Nat.Prime 2879) := {out := by norm_num}

def I2879N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2879, 0, 0, 0, 0], ![1309, 1, 0, 0, 0]] i)))

def I2879N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2879, 0, 0, 0, 0], ![2344, 1, 0, 0, 0]] i)))

def I2879N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2879, 0, 0, 0, 0], ![888, 963, 2105, 2, 0]] i)))

def P2879P0 : CertificateIrreducibleZModOfList' 2879 1 2 11 [1309, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [2162], [915], [862], [2200], [81], [], [], [2647], [2014], [1570, 1]]]
 h' := ![![[0, 1], [2878], [2808], [210], [2079], [494], [9], [3], [1393], [838], [476], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P2879P1 : CertificateIrreducibleZModOfList' 2879 1 2 11 [2344, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [2131], [2828], [1051], [1672], [2544], [], [], [1433], [1479], [535, 1]]]
 h' := ![![[0, 1], [1], [1505], [880], [2030], [2152], [1324], [1926], [841], [2419], [1204], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P2879P2 : CertificateIrreducibleZModOfList' 2879 3 2 11 [888, 962, 2105, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1503, 838, 2491], [2150, 2040, 388], [0, 1]]
 g := ![![[2284, 1117, 2421], [2234, 1984, 1923], [1400, 1100, 1455], [1598, 213, 721], [497, 1125, 676], [1865, 761, 19], [154, 324], [649, 2774], [1187, 2604, 1363], [2161, 774, 1], []], ![[2631, 1033, 1568, 1471], [2078, 963, 2512, 586], [332, 2785, 281, 2340], [2378, 405, 1865, 1641], [1332, 1114, 1244, 399], [2072, 135, 1614, 1409], [603, 1277], [1845, 1441], [2018, 2406, 639, 2270], [2859, 2090, 1940, 745], [2534, 836]], ![[2387, 2445, 1458, 2142], [2459, 1004, 26, 245], [1766, 2824, 1865, 934], [2665, 1616, 510, 32], [769, 136, 993, 214], [1275, 1603, 253, 2001], [2025, 2292], [2025, 1495], [1623, 2826, 2740, 123], [1808, 758, 126, 2112], [1758, 836]]]
 h' := ![![[1503, 838, 2491], [2718, 1182, 517], [528, 438, 2201], [323, 2031, 2697], [2030, 2045, 60], [2184, 1531, 26], [884, 607, 1945], [1292, 404, 2861], [2537, 2868, 2427], [1325, 525, 100], [0, 0, 1], [0, 1]], ![[2150, 2040, 388], [974, 1535, 111], [1308, 751, 1596], [85, 694, 929], [177, 1808, 2626], [1878, 2205, 264], [2303, 1970, 1100], [674, 1666, 2300], [2530, 1858, 589], [2280, 2261, 300], [180, 1122, 2040], [1503, 838, 2491]], ![[0, 1], [1827, 162, 2251], [873, 1690, 1961], [1207, 154, 2132], [349, 1905, 193], [841, 2022, 2589], [71, 302, 2713], [2245, 809, 597], [1971, 1032, 2742], [2642, 93, 2479], [1019, 1757, 838], [2150, 2040, 388]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [912, 1247], []]
 b := ![[], [1256, 566, 441], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A2879 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 2879 3 where
 D := ![[1309, 1], [2344, 1], [888, 962, 2105, 1]]; D' := ![[1309, 1], [2344, 1], [888, 962, 2105, 1]]
 heqm := by decide
 hProd := by decide
 s := ![11, 11, 11]
 n := ![1, 1, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P2879P0
  | 1 => exact P2879P1
  | 2 => exact P2879P2

def C28790 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A2879.D 0) 2879 where
  n := 1
  w := ![![2879, 0, 0, 0, 0], ![1309, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C28791 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A2879.D 1) 2879 where
  n := 1
  w := ![![2879, 0, 0, 0, 0], ![2344, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C28792 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A2879.D 2) 2879 where
  n := 3
  w := ![![2879, 0, 0, 0, 0], ![888, 963, 2105, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K2879 : KummerData 2879 ![I2879N0, I2879N1, I2879N2] ![2879, 2879, 23862997439] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A2879
  C := by
    intro i
    match i with
    | 0 => exact C28790
    | 1 => exact C28791
    | 2 => exact C28792
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 2879 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp2887 : Fact (Nat.Prime 2887) := {out := by norm_num}

def I2887N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2887, 0, 0, 0, 0], ![571, 1, 0, 0, 0]] i)))

def I2887N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2887, 0, 0, 0, 0], ![1389, 1, 0, 0, 0]] i)))

def I2887N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2887, 0, 0, 0, 0], ![1811, 1, 0, 0, 0]] i)))

def I2887N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2887, 0, 0, 0, 0], ![1335, 2003, 1, 0, 0]] i)))

def P2887P0 : CertificateIrreducibleZModOfList' 2887 1 2 11 [571, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [1714], [2025], [], [], [], [1762], [], [626], [1456], [2316, 1]]]
 h' := ![![[0, 1], [2886], [1412], [2842], [142], [1028], [1461], [2177], [542], [80], [2697], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P2887P1 : CertificateIrreducibleZModOfList' 2887 1 2 11 [1389, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [927], [2372], [], [], [], [2847], [], [2539], [1337], [1498, 1]]]
 h' := ![![[0, 1], [2886], [2246], [811], [2506], [398], [707], [504], [1243], [2135], [805], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P2887P2 : CertificateIrreducibleZModOfList' 2887 1 2 11 [1811, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [1253], [104], [], [], [], [2049], [], [953], [2147], [1076, 1]]]
 h' := ![![[0, 1], [2886], [2198], [1244], [1839], [1940], [1943], [375], [543], [572], [89], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P2887P3 : CertificateIrreducibleZModOfList' 2887 2 2 11 [1335, 2003, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [884, 2886], [0, 1]]
 g := ![![[1139, 2275], [578, 1887], [2285, 582], [837], [1539], [2307], [1498, 2727], [1914], [591, 953], [1256, 1966], [1]], ![[0, 612], [0, 1000], [0, 2305], [837], [1539], [2307], [1521, 160], [1914], [39, 1934], [1226, 921], [1]]]
 h' := ![![[884, 2886], [2086, 1206], [1084, 2520], [2601, 1274], [1008, 1796], [2833, 1567], [861, 2225], [2481, 1879], [2053, 1825], [587, 2315], [1552, 884], [0, 1]], ![[0, 1], [0, 1681], [0, 367], [0, 1613], [822, 1091], [2301, 1320], [1714, 662], [605, 1008], [1520, 1062], [164, 572], [631, 2003], [884, 2886]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1073]]
 b := ![[], [2488, 1980]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A2887 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 2887 4 where
 D := ![[571, 1], [1389, 1], [1811, 1], [1335, 2003, 1]]; D' := ![[571, 1], [1389, 1], [1811, 1], [1335, 2003, 1]]
 heqm := by decide
 hProd := by decide
 s := ![11, 11, 11, 11]
 n := ![1, 1, 1, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P2887P0
  | 1 => exact P2887P1
  | 2 => exact P2887P2
  | 3 => exact P2887P3

def C28870 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A2887.D 0) 2887 where
  n := 1
  w := ![![2887, 0, 0, 0, 0], ![571, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C28871 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A2887.D 1) 2887 where
  n := 1
  w := ![![2887, 0, 0, 0, 0], ![1389, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C28872 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A2887.D 2) 2887 where
  n := 1
  w := ![![2887, 0, 0, 0, 0], ![1811, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C28873 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A2887.D 3) 2887 where
  n := 2
  w := ![![2887, 0, 0, 0, 0], ![1335, 2003, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K2887 : KummerData 2887 ![I2887N0, I2887N1, I2887N2, I2887N3] ![2887, 2887, 2887, 8334769] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A2887
  C := by
    intro i
    match i with
    | 0 => exact C28870
    | 1 => exact C28871
    | 2 => exact C28872
    | 3 => exact C28873
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 2887 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp2897 : Fact (Nat.Prime 2897) := {out := by norm_num}

def I2897N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2897, 0, 0, 0, 0], ![1387, 809, 1, 0, 0]] i)))

def I2897N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2897, 0, 0, 0, 0], ![2658, 1270, 2088, 2, 0]] i)))

def P2897P0 : CertificateIrreducibleZModOfList' 2897 2 2 11 [1387, 809, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2088, 2896], [0, 1]]
 g := ![![[2507, 1790], [1416], [1153], [2357], [1992, 1927], [1970], [70, 330], [2283], [1773, 1548], [2758, 2656], [1]], ![[0, 1107], [1416], [1153], [2357], [1635, 970], [1970], [2521, 2567], [2283], [945, 1349], [731, 241], [1]]]
 h' := ![![[2088, 2896], [1284, 1015], [2798, 1920], [1830, 777], [834, 1557], [397, 1342], [1408, 1159], [2169, 1090], [402, 1459], [1591, 741], [1510, 2088], [0, 1]], ![[0, 1], [0, 1882], [2310, 977], [1886, 2120], [1416, 1340], [1094, 1555], [2405, 1738], [1047, 1807], [2047, 1438], [1801, 2156], [1269, 809], [2088, 2896]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1158]]
 b := ![[], [997, 579]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P2897P1 : CertificateIrreducibleZModOfList' 2897 3 2 11 [2658, 1269, 2088, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1792, 1883, 2224], [1914, 1013, 673], [0, 1]]
 g := ![![[1656, 2217, 639], [1777, 2626], [916, 362], [1790, 399], [945, 1717, 269], [2182, 2741], [2319, 1714, 1245], [2678, 1397], [2392, 2284, 1309], [1387, 809, 1], []], ![[1442, 1692, 2231, 1245], [1169, 182], [], [2294, 1981], [2288, 809, 1084, 2372], [680, 657], [1189, 1472, 1206, 1365], [2673, 2155], [360, 1528, 967, 1354], [1537, 1215, 2046, 1196], [1564, 997]], ![[182, 357, 609, 354], [574, 1095], [379, 362], [2649, 1080], [2343, 1437, 1050, 31], [2335, 2362], [1555, 620, 1090, 1648], [979, 2224], [2802, 923, 2571, 265], [2018, 1326, 2180, 1385], [218, 997]]]
 h' := ![![[1792, 1883, 2224], [2056, 2100, 1686], [666, 1878, 318], [2684, 2720, 972], [2786, 2491, 2775], [1098, 1244, 2242], [914, 1184, 639], [2236, 1276, 790], [979, 354, 302], [1235, 525, 100], [0, 0, 1], [0, 1]], ![[1914, 1013, 673], [2327, 2376, 2021], [1089, 206, 2662], [2864, 2016], [2533, 481, 1905], [852, 1573, 2816], [482, 1377, 1119], [591, 1175, 2359], [1905, 1036, 1053], [2760, 2505, 14], [1471, 2017, 1013], [1792, 1883, 2224]], ![[0, 1], [2098, 1318, 2087], [1380, 813, 2814], [80, 1058, 1925], [2035, 2822, 1114], [513, 80, 736], [375, 336, 1139], [2452, 446, 2645], [508, 1507, 1542], [1685, 2764, 2783], [1544, 880, 1883], [1914, 1013, 673]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1001, 2267], []]
 b := ![[], [1776, 2035, 2556], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A2897 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 2897 2 where
 D := ![[1387, 809, 1], [2658, 1269, 2088, 1]]; D' := ![[1387, 809, 1], [2658, 1269, 2088, 1]]
 heqm := by decide
 hProd := by decide
 s := ![11, 11]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P2897P0
  | 1 => exact P2897P1

def C28970 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A2897.D 0) 2897 where
  n := 2
  w := ![![2897, 0, 0, 0, 0], ![1387, 809, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C28971 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A2897.D 1) 2897 where
  n := 3
  w := ![![2897, 0, 0, 0, 0], ![2658, 1270, 2088, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K2897 : KummerData 2897 ![I2897N0, I2897N1] ![8392609, 24313388273] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A2897
  C := by
    intro i
    match i with
    | 0 => exact C28970
    | 1 => exact C28971
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 2897 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp2903 : Fact (Nat.Prime 2903) := {out := by norm_num}

def I2903N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2903, 0, 0, 0, 0], ![198, 1092, 1, 0, 0]] i)))

def I2903N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2903, 0, 0, 0, 0], ![1680, 2037, 1811, 2, 0]] i)))

def P2903P0 : CertificateIrreducibleZModOfList' 2903 2 2 11 [198, 1092, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1811, 2902], [0, 1]]
 g := ![![[1501, 1950], [844, 2723], [171, 1986], [129], [2404, 1656], [578], [2321, 2156], [1150], [1431, 1046], [1780, 2234], [1]], ![[0, 953], [0, 180], [0, 917], [129], [2621, 1247], [578], [2302, 747], [1150], [78, 1857], [772, 669], [1]]]
 h' := ![![[1811, 2902], [1262, 804], [978, 1580], [1876, 1416], [100, 305], [2225, 1482], [2019, 2844], [2593, 2431], [1156, 1668], [1726, 1639], [2705, 1811], [0, 1]], ![[0, 1], [0, 2099], [0, 1323], [0, 1487], [885, 2598], [852, 1421], [2581, 59], [1283, 472], [2784, 1235], [186, 1264], [2036, 1092], [1811, 2902]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [306]]
 b := ![[], [2254, 153]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P2903P1 : CertificateIrreducibleZModOfList' 2903 3 2 11 [1680, 2036, 1811, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2309, 1407, 2199], [1686, 1495, 704], [0, 1]]
 g := ![![[695, 2513, 1373], [1246, 2193, 1829], [1532, 2422, 2120], [1683, 2624], [2423, 2252, 2469], [2142, 2258], [2692, 277, 1778], [2446, 11], [254, 2309, 1291], [198, 1092, 1], []], ![[1298, 253, 956, 2324], [650, 2902, 1243, 1531], [2092, 2081, 1821, 953], [2121, 1523], [1917, 2484, 1157, 1504], [2512, 34], [981, 171, 56, 181], [406, 1993], [1231, 1661, 1848, 2088], [2249, 2297, 2434, 333], [2269, 2106]], ![[323, 2684, 690, 895], [1402, 1241, 42, 1614], [2858, 1926, 2798, 1460], [589, 1670], [617, 238, 1934, 2281], [18, 287], [1314, 888, 717, 1456], [2629, 2465], [2397, 2404, 513, 513], [2413, 962, 1270, 656], [861, 2106]]]
 h' := ![![[2309, 1407, 2199], [2686, 2546, 1271], [1201, 1198, 1994], [1424, 2854, 2033], [2269, 188, 1610], [1054, 875, 1002], [314, 2775, 1935], [1809, 1483, 1856], [21, 2306, 2522], [1205, 525, 100], [0, 0, 1], [0, 1]], ![[1686, 1495, 704], [1859, 1995, 350], [2111, 1705, 1030], [921, 2721, 2457], [2483, 861, 1549], [787, 121, 2381], [1405, 765, 1556], [590, 1461, 500], [1731, 481, 1649], [1444, 83, 528], [1292, 278, 1495], [2309, 1407, 2199]], ![[0, 1], [585, 1265, 1282], [771, 0, 2782], [180, 231, 1316], [215, 1854, 2647], [560, 1907, 2423], [1339, 2266, 2315], [2287, 2862, 547], [217, 116, 1635], [1464, 2295, 2275], [2676, 2625, 1407], [1686, 1495, 704]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1823, 2802], []]
 b := ![[], [518, 689, 672], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A2903 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 2903 2 where
 D := ![[198, 1092, 1], [1680, 2036, 1811, 1]]; D' := ![[198, 1092, 1], [1680, 2036, 1811, 1]]
 heqm := by decide
 hProd := by decide
 s := ![11, 11]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P2903P0
  | 1 => exact P2903P1

def C29030 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A2903.D 0) 2903 where
  n := 2
  w := ![![2903, 0, 0, 0, 0], ![198, 1092, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C29031 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A2903.D 1) 2903 where
  n := 3
  w := ![![2903, 0, 0, 0, 0], ![1680, 2037, 1811, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K2903 : KummerData 2903 ![I2903N0, I2903N1] ![8427409, 24464768327] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A2903
  C := by
    intro i
    match i with
    | 0 => exact C29030
    | 1 => exact C29031
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 2903 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp2909 : Fact (Nat.Prime 2909) := {out := by norm_num}

def I2909N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2909, 0, 0, 0, 0], ![23, 1, 0, 0, 0]] i)))

def I2909N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2909, 0, 0, 0, 0], ![2300, 1, 0, 0, 0]] i)))

def I2909N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2909, 0, 0, 0, 0], ![598, 2506, 586, 2, 0]] i)))

def P2909P0 : CertificateIrreducibleZModOfList' 2909 1 2 11 [23, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [1859], [2766], [1885], [], [606], [], [2763], [577], [2886, 1]]]
 h' := ![![[0, 1], [2908], [878], [380], [280], [1915], [607], [880], [449], [1274], [529], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P2909P1 : CertificateIrreducibleZModOfList' 2909 1 2 11 [2300, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [1465], [399], [1363], [], [862], [], [708], [2454], [609, 1]]]
 h' := ![![[0, 1], [2908], [2031], [1544], [1002], [1209], [1338], [2340], [640], [2169], [1438], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P2909P2 : CertificateIrreducibleZModOfList' 2909 3 2 11 [598, 2505, 586, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2330, 1264, 1575], [2902, 1644, 1334], [0, 1]]
 g := ![![[2837, 408, 2680], [1498, 625], [1508, 360, 721], [1867, 540, 831], [792, 1281, 794], [129, 265], [2056, 1341, 1603], [871, 379], [1068, 1911, 1273], [538, 2323, 1], []], ![[2805, 1783, 196, 109], [1072, 2642], [2852, 562, 1098, 1284], [1799, 768, 608, 1645], [2535, 1054, 1682, 479], [1239, 1334], [2389, 483, 1372, 1764], [1848, 1708], [1648, 2329, 1522, 2588], [2111, 1333, 2908, 2593], [592, 2157]], ![[2807, 1172, 684, 2458], [2536, 2441], [268, 978, 1579, 2082], [2887, 2773, 425, 190], [993, 1773, 822, 1333], [844, 1521], [1931, 2487, 1091, 509], [765, 1491], [2029, 760, 720, 1206], [2203, 2505, 266, 1070], [833, 2157]]]
 h' := ![![[2330, 1264, 1575], [204, 1806, 2458], [6, 257, 25], [590, 1881, 714], [551, 2693, 124], [1249, 2393, 1242], [1019, 1682, 1486], [854, 998, 1662], [1316, 249, 1984], [1175, 525, 100], [0, 0, 1], [0, 1]], ![[2902, 1644, 1334], [1196, 406, 2708], [1445, 1780, 798], [1688, 1806, 2702], [2537, 631, 379], [380, 2283, 1550], [2225, 1276, 1384], [2696, 1345, 1767], [2740, 999, 167], [1450, 2581, 2215], [1588, 1855, 1644], [2330, 1264, 1575]], ![[0, 1], [2553, 697, 652], [2420, 872, 2086], [346, 2131, 2402], [502, 2494, 2406], [2504, 1142, 117], [895, 2860, 39], [2364, 566, 2389], [778, 1661, 758], [2716, 2712, 594], [2263, 1054, 1264], [2902, 1644, 1334]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2321, 2472], []]
 b := ![[], [2779, 223, 752], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A2909 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 2909 3 where
 D := ![[23, 1], [2300, 1], [598, 2505, 586, 1]]; D' := ![[23, 1], [2300, 1], [598, 2505, 586, 1]]
 heqm := by decide
 hProd := by decide
 s := ![11, 11, 11]
 n := ![1, 1, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P2909P0
  | 1 => exact P2909P1
  | 2 => exact P2909P2

def C29090 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A2909.D 0) 2909 where
  n := 1
  w := ![![2909, 0, 0, 0, 0], ![23, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C29091 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A2909.D 1) 2909 where
  n := 1
  w := ![![2909, 0, 0, 0, 0], ![2300, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C29092 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A2909.D 2) 2909 where
  n := 3
  w := ![![2909, 0, 0, 0, 0], ![598, 2506, 586, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K2909 : KummerData 2909 ![I2909N0, I2909N1, I2909N2] ![2909, 2909, 24616775429] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A2909
  C := by
    intro i
    match i with
    | 0 => exact C29090
    | 1 => exact C29091
    | 2 => exact C29092
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 2909 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp2917 : Fact (Nat.Prime 2917) := {out := by norm_num}

def I2917N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2917, 0, 0, 0, 0], ![1479, 651, 1, 0, 0]] i)))

def I2917N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2917, 0, 0, 0, 0], ![1581, 2275, 2266, 2, 0]] i)))

def P2917P0 : CertificateIrreducibleZModOfList' 2917 2 2 11 [1479, 651, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2266, 2916], [0, 1]]
 g := ![![[2095, 1921], [456], [635, 83], [2784], [1546], [2712, 332], [1393, 2715], [2703], [2591, 366], [1681, 836], [1]], ![[0, 996], [456], [2025, 2834], [2784], [1546], [2438, 2585], [1630, 202], [2703], [602, 2551], [7, 2081], [1]]]
 h' := ![![[2266, 2916], [2533, 1962], [109, 2013], [525, 1430], [1153, 1204], [2744, 578], [2072, 2860], [1772, 2328], [849, 579], [2002, 2516], [1438, 2266], [0, 1]], ![[0, 1], [0, 955], [2296, 904], [118, 1487], [2022, 1713], [2759, 2339], [1258, 57], [167, 589], [213, 2338], [523, 401], [2274, 651], [2266, 2916]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1532]]
 b := ![[], [1388, 766]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P2917P1 : CertificateIrreducibleZModOfList' 2917 3 2 11 [1581, 2274, 2266, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [137, 828, 1085], [514, 2088, 1832], [0, 1]]
 g := ![![[618, 247, 465], [2553, 880], [1797, 1374, 1135], [2853, 119], [1018, 1040], [903, 1571, 904], [2652, 566, 1791], [1512, 660], [2650, 2161, 1249], [1479, 651, 1], []], ![[1677, 1666, 1190, 2175], [2369, 439], [43, 1556, 2749, 13], [1170, 1078], [2056, 305], [2875, 136, 2246, 2402], [587, 577, 2686, 178], [1744, 831], [739, 356, 857, 76], [1443, 2221, 1125, 1277], [1621, 1674]], ![[2277, 2392, 574, 2541], [2084, 2530], [525, 510, 2372, 1133], [2439, 2309], [1043, 2586], [1580, 2473, 65, 656], [1029, 1833, 778, 1672], [827, 1507], [1622, 1371, 1970, 1398], [546, 1908, 2062, 2613], [874, 1674]]]
 h' := ![![[137, 828, 1085], [2285, 2730, 2821], [101, 2399, 711], [2705, 1634, 2212], [2620, 2101, 346], [1687, 1934, 2792], [1834, 214, 1607], [715, 1572, 1317], [2079, 1516, 1071], [1135, 525, 100], [0, 0, 1], [0, 1]], ![[514, 2088, 1832], [1249, 1462, 2120], [755, 2732, 766], [811, 1808, 399], [522, 2333, 440], [2609, 1369, 2597], [2651, 2783, 2613], [2530, 1692, 1257], [329, 2516, 1498], [173, 1824, 2503], [2509, 2322, 2088], [137, 828, 1085]], ![[0, 1], [1659, 1642, 893], [1254, 703, 1440], [1122, 2392, 306], [607, 1400, 2131], [2769, 2531, 445], [396, 2837, 1614], [1510, 2570, 343], [2201, 1802, 348], [1842, 568, 314], [2530, 595, 828], [514, 2088, 1832]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1067, 1368], []]
 b := ![[], [1931, 1156, 1058], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A2917 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 2917 2 where
 D := ![[1479, 651, 1], [1581, 2274, 2266, 1]]; D' := ![[1479, 651, 1], [1581, 2274, 2266, 1]]
 heqm := by decide
 hProd := by decide
 s := ![11, 11]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P2917P0
  | 1 => exact P2917P1

def C29170 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A2917.D 0) 2917 where
  n := 2
  w := ![![2917, 0, 0, 0, 0], ![1479, 651, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C29171 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A2917.D 1) 2917 where
  n := 3
  w := ![![2917, 0, 0, 0, 0], ![1581, 2275, 2266, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K2917 : KummerData 2917 ![I2917N0, I2917N1] ![8508889, 24820429213] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A2917
  C := by
    intro i
    match i with
    | 0 => exact C29170
    | 1 => exact C29171
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 2917 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp2927 : Fact (Nat.Prime 2927) := {out := by norm_num}

def I2927N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2927, 0, 0, 0, 0], ![1412, 1306, 1, 0, 0]] i)))

def I2927N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2927, 0, 0, 0, 0], ![561, 711, 1621, 2, 0]] i)))

def P2927P0 : CertificateIrreducibleZModOfList' 2927 2 2 11 [1412, 1306, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1621, 2926], [0, 1]]
 g := ![![[884, 2920], [1950, 1184], [159, 627], [2348, 537], [91], [1820, 974], [784, 2341], [1916], [1776, 2614], [661, 2122], [1]], ![[1245, 7], [1102, 1743], [857, 2300], [579, 2390], [91], [94, 1953], [2153, 586], [1916], [774, 313], [1198, 805], [1]]]
 h' := ![![[1621, 2926], [907, 2774], [871, 1823], [915, 2650], [1725, 450], [66, 2589], [2325, 1198], [825, 452], [727, 445], [381, 1640], [1515, 1621], [0, 1]], ![[0, 1], [1689, 153], [2611, 1104], [2656, 277], [2352, 2477], [2444, 338], [755, 1729], [1767, 2475], [2030, 2482], [1105, 1287], [710, 1306], [1621, 2926]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [689]]
 b := ![[], [1043, 1808]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P2927P1 : CertificateIrreducibleZModOfList' 2927 3 2 11 [561, 710, 1621, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [917, 390, 2854], [389, 2536, 73], [0, 1]]
 g := ![![[1741, 2435, 809], [1240, 340, 2332], [2076, 1284, 230], [637, 145, 266], [1379, 560], [505, 2249, 603], [2005, 649, 2760], [1304, 417], [1091, 2281, 1219], [1412, 1306, 1], []], ![[1034, 973, 1191, 2567], [1762, 1779, 567, 1332], [1927, 2002, 1395, 1840], [2030, 1259, 2759, 1768], [2797, 974], [1840, 1128, 59, 230], [240, 282, 1669, 1027], [191, 1713], [2653, 1619, 957, 1241], [2486, 2281, 2033, 338], [868, 2402]], ![[1876, 720, 962, 1778], [1524, 2919, 1771, 2697], [1341, 1855, 2062, 426], [2904, 1527, 2545, 1908], [1369, 2315], [134, 1721, 906, 271], [1605, 1707, 2108, 2043], [117, 837], [547, 1757, 2665, 2336], [1007, 2466, 2729, 1189], [722, 2402]]]
 h' := ![![[917, 390, 2854], [986, 2578, 2655], [310, 2814, 1119], [2664, 41, 2849], [1449, 2331, 2656], [614, 2335, 886], [2090, 1869, 959], [1406, 2160, 1817], [2619, 1074, 224], [1085, 525, 100], [0, 0, 1], [0, 1]], ![[389, 2536, 73], [1, 2635, 114], [889, 2831, 989], [2276, 487, 1162], [2045, 1256, 192], [972, 2032, 1198], [605, 2053, 819], [2612, 2157, 1192], [213, 1741, 853], [371, 2699, 1604], [2701, 1287, 2536], [917, 390, 2854]], ![[0, 1], [2100, 641, 158], [2532, 209, 819], [1842, 2399, 1843], [1072, 2267, 79], [1280, 1487, 843], [452, 1932, 1149], [1821, 1537, 2845], [1899, 112, 1850], [2483, 2630, 1223], [928, 1640, 390], [389, 2536, 73]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [351, 2687], []]
 b := ![[], [1394, 752, 117], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A2927 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 2927 2 where
 D := ![[1412, 1306, 1], [561, 710, 1621, 1]]; D' := ![[1412, 1306, 1], [561, 710, 1621, 1]]
 heqm := by decide
 hProd := by decide
 s := ![11, 11]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P2927P0
  | 1 => exact P2927P1

def C29270 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A2927.D 0) 2927 where
  n := 2
  w := ![![2927, 0, 0, 0, 0], ![1412, 1306, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C29271 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A2927.D 1) 2927 where
  n := 3
  w := ![![2927, 0, 0, 0, 0], ![561, 711, 1621, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K2927 : KummerData 2927 ![I2927N0, I2927N1] ![8567329, 25076571983] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A2927
  C := by
    intro i
    match i with
    | 0 => exact C29270
    | 1 => exact C29271
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 2927 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


lemma PB18792I46_primes (p : ℕ) :
  p ∈ Set.range ![2857, 2861, 2879, 2887, 2897, 2903, 2909, 2917, 2927] ↔ Nat.Prime p ∧ 2851 < p ∧ p ≤ 2927 := by
  rw [← List.mem_ofFn']
  convert primes_range 2851 2927 (by omega)
  decide

def PB18792I46 : PrimesBelowBoundCertificateInterval O 2851 2927 18792 where
  m := 9
  g := ![2, 3, 3, 4, 2, 2, 3, 2, 2]
  P := ![2857, 2861, 2879, 2887, 2897, 2903, 2909, 2917, 2927]
  hP := PB18792I46_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2857N0, I2857N1]
    · exact ![I2861N0, I2861N1, I2861N2]
    · exact ![I2879N0, I2879N1, I2879N2]
    · exact ![I2887N0, I2887N1, I2887N2, I2887N3]
    · exact ![I2897N0, I2897N1]
    · exact ![I2903N0, I2903N1]
    · exact ![I2909N0, I2909N1, I2909N2]
    · exact ![I2917N0, I2917N1]
    · exact ![I2927N0, I2927N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · convert (containsPrimesAbove_of_KummerData K2857) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K2861) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K2879) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K2887) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K2897) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K2903) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K2909) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K2917) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K2927) <;> rfl
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2857, 66625573677601]
    · exact ![2861, 8185321, 8185321]
    · exact ![2879, 2879, 23862997439]
    · exact ![2887, 2887, 2887, 8334769]
    · exact ![8392609, 24313388273]
    · exact ![8427409, 24464768327]
    · exact ![2909, 2909, 24616775429]
    · exact ![8508889, 24820429213]
    · exact ![8567329, 25076571983]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact (card_quot_of_KummerData K2857)
    · exact (card_quot_of_KummerData K2861)
    · exact (card_quot_of_KummerData K2879)
    · exact (card_quot_of_KummerData K2887)
    · exact (card_quot_of_KummerData K2897)
    · exact (card_quot_of_KummerData K2903)
    · exact (card_quot_of_KummerData K2909)
    · exact (card_quot_of_KummerData K2917)
    · exact (card_quot_of_KummerData K2927)
  β := ![I2857N0, I2861N0, I2879N0, I2879N1, I2887N0, I2887N1, I2887N2, I2909N0, I2909N1]
  Il := ![[I2857N0], [I2861N0], [I2879N0, I2879N1], [I2887N0, I2887N1, I2887N2], [], [], [I2909N0, I2909N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
