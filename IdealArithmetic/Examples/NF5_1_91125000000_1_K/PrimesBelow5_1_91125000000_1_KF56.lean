
import IdealArithmetic.Examples.NF5_1_91125000000_1_K.RI5_1_91125000000_1_K
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 

instance hp3613 : Fact (Nat.Prime 3613) := {out := by norm_num}

def I3613N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3613, 0, 0, 0, 0], ![970, 1, 0, 0, 0]] i)))

def I3613N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3613, 0, 0, 0, 0], ![988, 1, 0, 0, 0]] i)))

def I3613N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3613, 0, 0, 0, 0], ![2858, 1, 0, 0, 0]] i)))

def I3613N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3613, 0, 0, 0, 0], ![1667, 2410, 1, 0, 0]] i)))

def P3613P0 : CertificateIrreducibleZModOfList' 3613 1 2 11 [970, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [1069], [3041], [3522], [], [], [], [], [904], [1520, 2643, 1]]]
 h' := ![![[0, 1], [1], [1], [2051], [1558], [1835], [3240], [1199], [855], [1079], [3317], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P3613P1 : CertificateIrreducibleZModOfList' 3613 1 2 11 [988, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [3207], [1580], [1649], [], [], [], [], [762], [634, 2625, 1]]]
 h' := ![![[0, 1], [3612], [85], [3389], [251], [2190], [2934], [2816], [3339], [2261], [2270], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P3613P2 : CertificateIrreducibleZModOfList' 3613 1 2 11 [2858, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [2431], [2300], [840], [], [], [], [], [342], [2784, 755, 1]]]
 h' := ![![[0, 1], [1], [1], [2260], [1925], [916], [798], [3078], [2538], [1687], [2767], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P3613P3 : CertificateIrreducibleZModOfList' 3613 2 2 11 [1667, 2410, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1203, 3612], [0, 1]]
 g := ![![[1718, 3095], [903], [2814, 2881], [1992, 680], [1284, 1172], [3543], [494], [2622], [1976], [2251, 1348], [1203, 1]], ![[0, 518], [903], [177, 732], [3494, 2933], [2130, 2441], [3543], [494], [2622], [1976], [1658, 2265], [2406, 3612]]]
 h' := ![![[1203, 3612], [2070, 3359], [2349, 1849], [3296, 453], [2081, 172], [2727, 2369], [2226, 2153], [1334, 3387], [2782, 2698], [1490, 452], [3427, 342], [0, 1]], ![[0, 1], [0, 254], [1088, 1764], [2692, 3160], [3056, 3441], [1977, 1244], [1764, 1460], [431, 226], [389, 915], [3296, 3161], [2971, 3271], [1203, 3612]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [753]]
 b := ![[], [251, 2183]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A3613 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 3613 4 where
 D := ![[970, 1], [988, 1], [2858, 1], [1667, 2410, 1]]; D' := ![[970, 1], [988, 1], [2858, 1], [1667, 2410, 1]]
 heqm := by decide
 hProd := by decide
 s := ![11, 11, 11, 11]
 n := ![1, 1, 1, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P3613P0
  | 1 => exact P3613P1
  | 2 => exact P3613P2
  | 3 => exact P3613P3

def C36130 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A3613.D 0) 3613 where
  n := 1
  w := ![![3613, 0, 0, 0, 0], ![970, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C36131 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A3613.D 1) 3613 where
  n := 1
  w := ![![3613, 0, 0, 0, 0], ![988, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C36132 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A3613.D 2) 3613 where
  n := 1
  w := ![![3613, 0, 0, 0, 0], ![2858, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C36133 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A3613.D 3) 3613 where
  n := 2
  w := ![![3613, 0, 0, 0, 0], ![1667, 2410, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K3613 : KummerData 3613 ![I3613N0, I3613N1, I3613N2, I3613N3] ![3613, 3613, 3613, 13053769] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A3613
  C := by
    intro i
    match i with
    | 0 => exact C36130
    | 1 => exact C36131
    | 2 => exact C36132
    | 3 => exact C36133
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 3613 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp3617 : Fact (Nat.Prime 3617) := {out := by norm_num}

def I3617N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3617, 0, 0, 0, 0], ![453, 1, 0, 0, 0]] i)))

def I3617N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3617, 0, 0, 0, 0], ![1284, 6006, 13552, 3290, 22728]] i)))

def P3617P0 : CertificateIrreducibleZModOfList' 3617 1 2 11 [453, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [], [], [828], [], [], [], [285], [2657, 3164, 1]]]
 h' := ![![[0, 1], [3616], [1234], [2941], [3148], [1084], [614], [3416], [2903], [1107], [840], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P3617P1 : CertificateIrreducibleZModOfList' 3617 4 2 11 [636, 740, 2657, 3164, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2062, 1511, 1392, 3261], [2032, 458, 3275, 1686], [3593, 1647, 2567, 2287], [0, 1]]
 g := ![![[1919, 1439, 401, 3263], [3421, 1145, 392], [3201, 1357, 2132], [2358, 771, 1755], [1076, 293, 1668], [2278, 656, 1952, 227], [2963, 1158, 3402], [1850, 2989, 3543], [377, 703, 1701], [100, 0, 453, 1], []], ![[2610, 1813, 1693, 23, 1165, 850], [2147, 23, 861], [198, 1921, 1752], [1129, 1888, 2755], [2788, 2817, 2475], [1922, 1785, 547, 2812, 2666, 3026], [3175, 857, 2569], [3441, 1999, 2570], [816, 1158, 2169], [355, 638, 688, 26, 2493, 694], [2502, 2187, 3270, 2155, 536, 442]], ![[3604, 1539, 2714, 996, 307, 2366], [284, 701, 3288], [2133, 110, 359], [689, 3451, 1091], [3069, 828, 2670], [2097, 3021, 2082, 1626, 3426, 2946], [737, 1179, 2905], [3428, 1743, 17], [1938, 2719, 234], [2411, 3016, 1297, 3568, 2582, 2038], [60, 2502, 1948, 1275, 148, 1431]], ![[3441, 1253, 1661, 2554, 1309, 3109], [3515, 483, 196], [266, 229, 3601], [1369, 2526, 714], [366, 1494, 3111], [2938, 2683, 353, 2623, 145, 1733], [1534, 2985, 1916], [3442, 3354, 25], [1888, 649, 113], [852, 2260, 3615, 1160, 1244, 2856], [2662, 3224, 2781, 1238, 824, 863]]]
 h' := ![![[2062, 1511, 1392, 3261], [1947, 1893, 2908, 2593], [882, 223, 1442, 670], [2123, 239, 2999, 2024], [2003, 2260, 1127, 2504], [1609, 3415, 719, 2722], [3109, 2556, 376, 3555], [1484, 1095, 2523, 2185], [2744, 3320, 220, 1538], [1506, 1957, 3210, 2421], [0, 0, 0, 1], [0, 1]], ![[2032, 458, 3275, 1686], [852, 2828, 2175, 760], [3156, 3397, 2195, 2317], [2540, 3311, 2065, 452], [2766, 1609, 2916, 1815], [3392, 3270, 2668, 1584], [2101, 1163, 3596, 2698], [746, 799, 3350, 1392], [314, 1156, 2379, 167], [2499, 2590, 1914, 1640], [1981, 3200, 1579, 1274], [2062, 1511, 1392, 3261]], ![[3593, 1647, 2567, 2287], [496, 2718, 3018, 2713], [1081, 37, 421, 616], [431, 2462, 3570, 2460], [759, 1669, 1832, 486], [1222, 2097, 3330, 669], [2359, 1902, 2047, 1189], [1735, 157, 2998, 168], [2915, 343, 1306, 1917], [2120, 3023, 1590, 1900], [728, 2837, 1645, 3375], [2032, 458, 3275, 1686]], ![[0, 1], [91, 3412, 2750, 1168], [678, 3577, 3176, 14], [2437, 1222, 2217, 2298], [71, 1696, 1359, 2429], [764, 2069, 517, 2259], [1865, 1613, 1215, 3409], [409, 1566, 1980, 3489], [3478, 2415, 3329, 3612], [2185, 3281, 520, 1273], [368, 1197, 393, 2584], [3593, 1647, 2567, 2287]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [1886, 3579, 1688], []]
 b := ![[], [], [3267, 1344, 350, 1372], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A3617 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 3617 2 where
 D := ![[453, 1], [636, 740, 2657, 3164, 1]]; D' := ![[453, 1], [636, 740, 2657, 3164, 1]]
 heqm := by decide
 hProd := by decide
 s := ![11, 11]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P3617P0
  | 1 => exact P3617P1

def C36170 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A3617.D 0) 3617 where
  n := 1
  w := ![![3617, 0, 0, 0, 0], ![453, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C36171 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A3617.D 1) 3617 where
  n := 4
  w := ![![3617, 0, 0, 0, 0], ![1284, 6006, 13552, 3290, 22728]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K3617 : KummerData 3617 ![I3617N0, I3617N1] ![3617, 171156751470721] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A3617
  C := by
    intro i
    match i with
    | 0 => exact C36170
    | 1 => exact C36171
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 3617 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp3623 : Fact (Nat.Prime 3623) := {out := by norm_num}

def I3623N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3623, 0, 0, 0, 0], ![3168, 1, 0, 0, 0]] i)))

def I3623N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3623, 0, 0, 0, 0], ![1439, 4455, 11409, -2128, 22728]] i)))

def P3623P0 : CertificateIrreducibleZModOfList' 3623 1 2 11 [3168, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [2771], [2012], [], [], [1423], [], [], [], [3081], [514, 455, 1]]]
 h' := ![![[0, 1], [1], [2464], [1420], [1689], [2571], [1675], [3511], [2548], [3377], [1998], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P3623P1 : CertificateIrreducibleZModOfList' 3623 4 2 11 [791, 1898, 514, 455, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2862, 2823, 1645, 387], [52, 2422, 3320, 2825], [254, 2000, 2281, 411], [0, 1]]
 g := ![![[1943, 1047, 3, 2567], [981, 1078, 1823, 2140], [2787, 2813, 2527, 2937], [706, 3529, 3416], [1035, 1343, 949], [1260, 1149, 1151, 3488], [589, 2466, 2263], [187, 1280, 3363], [3340, 2972, 741], [100, 0, 3168, 1], []], ![[2354, 1871, 1199, 1687, 2572, 1432], [3366, 588, 3302, 1721, 1469, 1360], [2500, 2922, 2057, 1351, 935, 572], [2196, 1013, 1264], [3305, 3416, 514], [869, 2022, 907, 2257, 1989, 3308], [2325, 117, 3061], [335, 547, 1083], [2640, 2896, 2868], [1482, 2869, 3247, 2037, 1587, 3039], [2657, 989, 3476, 1206, 3391, 3472]], ![[3605, 3388, 3348, 1163, 653, 1707], [2313, 528, 68, 559, 2823, 580], [826, 1643, 219, 1607, 480, 2188], [2179, 2754, 2835], [1954, 190, 148], [3124, 442, 1233, 2569, 3472, 2185], [76, 2783, 3463], [398, 278, 2909], [193, 753, 2962], [2859, 1821, 2003, 2932, 987, 1184], [2192, 1924, 93, 1654, 2615, 3257]], ![[270, 1023, 1169, 3031, 3554, 1741], [1356, 2739, 1375, 3479, 3261, 2580], [950, 3249, 242, 637, 859, 3233], [2642, 2958, 989], [215, 2059, 906], [1991, 452, 1757, 1591, 938, 2351], [2125, 2211, 1126], [3263, 1657, 2594], [2674, 1896, 1225], [1834, 3118, 3002, 3389, 3300, 1779], [2744, 3236, 2954, 2122, 453, 2605]]]
 h' := ![![[2862, 2823, 1645, 387], [2974, 2436, 3244, 2063], [1890, 3065, 1431, 1527], [121, 2832, 1645, 2627], [25, 588, 2083, 180], [3288, 2441, 819, 1043], [2731, 3058, 57, 1251], [2386, 2853, 1119, 411], [540, 2567, 1764, 3520], [606, 2219, 550, 2124], [0, 0, 0, 1], [0, 1]], ![[52, 2422, 3320, 2825], [2635, 79, 1408, 256], [2310, 2210, 3531, 2280], [657, 419, 2785, 1114], [2154, 1966, 2751, 1504], [1382, 233, 1487, 455], [3023, 389, 2522, 1816], [2680, 2448, 21, 3317], [678, 381, 1933, 2045], [2830, 1790, 3374, 2932], [1161, 1589, 1837, 2647], [2862, 2823, 1645, 387]], ![[254, 2000, 2281, 411], [2970, 2826, 1762, 1400], [1279, 245, 1488, 493], [2477, 3216, 1911, 1250], [1961, 1426, 74, 1268], [2671, 606, 50, 313], [1194, 1640, 3611, 2634], [737, 1413, 2295, 868], [226, 1191, 3297, 2276], [2087, 3017, 1388, 2155], [856, 1922, 2170, 154], [52, 2422, 3320, 2825]], ![[0, 1], [3206, 1905, 832, 3527], [3518, 1726, 796, 2946], [3599, 779, 905, 2255], [583, 3266, 2338, 671], [106, 343, 1267, 1812], [2384, 2159, 1056, 1545], [1289, 532, 188, 2650], [3004, 3107, 252, 3028], [3546, 220, 1934, 35], [3531, 112, 3239, 821], [254, 2000, 2281, 411]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [2436, 2392, 1256], []]
 b := ![[], [], [2310, 1950, 1478, 1182], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A3623 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 3623 2 where
 D := ![[3168, 1], [791, 1898, 514, 455, 1]]; D' := ![[3168, 1], [791, 1898, 514, 455, 1]]
 heqm := by decide
 hProd := by decide
 s := ![11, 11]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P3623P0
  | 1 => exact P3623P1

def C36230 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A3623.D 0) 3623 where
  n := 1
  w := ![![3623, 0, 0, 0, 0], ![3168, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C36231 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A3623.D 1) 3623 where
  n := 4
  w := ![![3623, 0, 0, 0, 0], ![1439, 4455, 11409, -2128, 22728]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K3623 : KummerData 3623 ![I3623N0, I3623N1] ![3623, 172295262524641] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A3623
  C := by
    intro i
    match i with
    | 0 => exact C36230
    | 1 => exact C36231
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 3623 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp3631 : Fact (Nat.Prime 3631) := {out := by norm_num}

def I3631N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3631, 0, 0, 0, 0], ![118, 1, 0, 0, 0]] i)))

def I3631N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3631, 0, 0, 0, 0], ![1179, 1, 0, 0, 0]] i)))

def I3631N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3631, 0, 0, 0, 0], ![164, 3544, 2334, 2, 0]] i)))

def P3631P0 : CertificateIrreducibleZModOfList' 3631 1 2 11 [118, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [1077], [557], [787], [], [1002], [], [], [], [928], [3031, 3513, 1]]]
 h' := ![![[0, 1], [3630], [3263], [1540], [2286], [1587], [460], [3430], [2686], [3057], [1811], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P3631P1 : CertificateIrreducibleZModOfList' 3631 1 2 11 [1179, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [1352], [3326], [2680], [], [1711], [], [], [], [2045], [2999, 2452, 1]]]
 h' := ![![[0, 1], [1], [126], [2881], [933], [1567], [2640], [1943], [1410], [3560], [773], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P3631P2 : CertificateIrreducibleZModOfList' 3631 3 2 11 [164, 3543, 2334, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1549, 3418, 1256], [3379, 212, 2375], [0, 1]]
 g := ![![[2271, 2213, 3458], [781, 1283, 3477], [2396, 3205, 3068], [535, 2498, 3152], [176, 1164], [2591, 87, 1678], [3176, 1567], [2242, 2770], [2934, 2296], [3140, 264, 1056], [1]], ![[1065, 2690, 2348, 300], [1232, 3423, 3352, 1937], [1364, 1257, 2734, 1249], [3523, 2163, 2723, 2176], [3608, 2725], [1721, 1103, 1741, 975], [474, 1912], [896, 1160], [2940, 2260], [524, 3478, 737, 2486], [52, 2892, 2951, 2981]], ![[1501, 1197, 755, 315], [1661, 1200, 2353, 2452], [1734, 212, 3538, 2295], [2984, 3203, 1326, 821], [3020, 1639], [2438, 2518, 1316, 2525], [1119, 3525], [247, 3241], [2246, 278], [1441, 2716, 209, 2269], [1562, 868, 2896, 650]]]
 h' := ![![[1549, 3418, 1256], [2632, 1747, 1765], [2835, 503, 3127], [3035, 2093, 399], [2331, 1225, 1913], [3534, 3151, 468], [3, 1997, 2207], [3203, 2463, 1750], [3608, 2648, 1154], [642, 2119, 1332], [3467, 88, 1297], [0, 1]], ![[3379, 212, 2375], [1860, 3595, 1295], [1887, 2242, 2056], [1250, 1506, 1039], [1835, 2808, 1571], [3321, 1450, 1045], [2219, 3622, 2327], [835, 3235, 554], [3532, 2777, 1263], [80, 558, 2738], [1069, 246, 606], [1549, 3418, 1256]], ![[0, 1], [3030, 1920, 571], [2567, 886, 2079], [1205, 32, 2193], [1571, 3229, 147], [1335, 2661, 2118], [2029, 1643, 2728], [357, 1564, 1327], [1590, 1837, 1214], [692, 954, 3192], [442, 3297, 1728], [3379, 212, 2375]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2568, 1864], []]
 b := ![[], [1083, 499, 2265], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A3631 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 3631 3 where
 D := ![[118, 1], [1179, 1], [164, 3543, 2334, 1]]; D' := ![[118, 1], [1179, 1], [164, 3543, 2334, 1]]
 heqm := by decide
 hProd := by decide
 s := ![11, 11, 11]
 n := ![1, 1, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P3631P0
  | 1 => exact P3631P1
  | 2 => exact P3631P2

def C36310 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A3631.D 0) 3631 where
  n := 1
  w := ![![3631, 0, 0, 0, 0], ![118, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C36311 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A3631.D 1) 3631 where
  n := 1
  w := ![![3631, 0, 0, 0, 0], ![1179, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C36312 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A3631.D 2) 3631 where
  n := 3
  w := ![![3631, 0, 0, 0, 0], ![164, 3544, 2334, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K3631 : KummerData 3631 ![I3631N0, I3631N1, I3631N2] ![3631, 3631, 47871688591] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A3631
  C := by
    intro i
    match i with
    | 0 => exact C36310
    | 1 => exact C36311
    | 2 => exact C36312
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 3631 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp3637 : Fact (Nat.Prime 3637) := {out := by norm_num}

def I3637N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3637, 0, 0, 0, 0], ![1567, 1, 0, 0, 0]] i)))

def I3637N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3637, 0, 0, 0, 0], ![2764, 6048, 11409, 1102, 22728]] i)))

def P3637P0 : CertificateIrreducibleZModOfList' 3637 1 2 11 [1567, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [3449], [], [1633], [766], [], [], [], [2075], [514, 2070, 1]]]
 h' := ![![[0, 1], [1], [3636], [1956], [1537], [3525], [1143], [2464], [2209], [3590], [1976], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P3637P1 : CertificateIrreducibleZModOfList' 3637 4 2 11 [2116, 1876, 514, 2070, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1843, 542, 497, 2951], [2873, 553, 3108, 134], [488, 2541, 32, 552], [0, 1]]
 g := ![![[2610, 607, 78, 859], [1695, 1082, 3352], [299, 810, 3462, 141], [2235, 2144, 819], [1024, 2168, 3607, 2806], [1709, 3483, 2688, 2860], [2872, 3045, 1863], [2749, 1205, 3319], [961, 1720, 889], [100, 0, 1567, 1], []], ![[918, 2272, 1490, 2973, 87, 605], [157, 597, 833], [2935, 2898, 3317, 817, 2061, 3015], [460, 3125, 1624], [798, 2942, 2812, 1123, 189, 563], [3379, 2178, 2126, 3419, 2019, 829], [2043, 1127, 66], [1224, 2822, 750], [3597, 1224, 2819], [991, 3429, 538, 378, 2457, 234], [3213, 2703, 1218, 1755, 1678, 2175]], ![[30, 3300, 2055, 2735, 3355, 140], [1612, 1406, 522], [435, 1799, 183, 3038, 1068, 2129], [2361, 3008, 1917], [1870, 1595, 3386, 2652, 386, 1074], [11, 3269, 235, 2740, 1702, 1384], [250, 406, 1782], [3417, 910, 1566], [2338, 1647, 3138], [226, 2301, 3631, 2787, 2025, 2530], [950, 672, 2956, 753, 3175, 2047]], ![[1739, 765, 3435, 839, 1961, 3095], [2874, 2834, 3553], [1489, 780, 2270, 3298, 2447, 2970], [1345, 2823, 1083], [2449, 1128, 2472, 3525, 2413, 1784], [119, 437, 2662, 2204, 623, 902], [2183, 3440, 37], [2634, 1733, 1670], [2733, 2297, 1811], [2681, 814, 183, 2259, 214, 2400], [2477, 731, 2744, 1462, 1012, 3543]]]
 h' := ![![[1843, 542, 497, 2951], [1356, 3297, 1780, 3499], [154, 3114, 2741, 1522], [3042, 923, 2214, 3477], [868, 3330, 2912, 2973], [2571, 3053, 2340, 565], [2165, 2727, 3085, 1830], [2007, 528, 1781, 186], [1794, 1917, 808, 2661], [2983, 1524, 690, 834], [0, 0, 0, 1], [0, 1]], ![[2873, 553, 3108, 134], [1868, 1593, 3390, 1231], [934, 3325, 2089, 3464], [1399, 1607, 3363, 2124], [1943, 1429, 529, 2235], [842, 445, 415, 948], [3357, 1870, 1683, 574], [344, 0, 2981, 3374], [28, 77, 3386, 901], [896, 1028, 1969, 3163], [367, 3483, 176, 928], [1843, 542, 497, 2951]], ![[488, 2541, 32, 552], [1184, 3625, 565, 3401], [235, 3339, 321, 1470], [573, 759, 736, 3311], [2149, 1299, 1721, 1718], [2372, 1431, 3042, 3290], [1063, 2160, 2247, 862], [2991, 772, 2164, 286], [3144, 1224, 2331, 449], [1465, 3516, 616, 884], [798, 459, 2470, 714], [2873, 553, 3108, 134]], ![[0, 1], [2999, 2396, 1539, 2780], [2661, 1133, 2123, 818], [1739, 348, 961, 1999], [2782, 1216, 2112, 348], [2025, 2345, 1477, 2471], [762, 517, 259, 371], [2962, 2337, 348, 3428], [419, 419, 749, 3263], [2140, 1206, 362, 2393], [796, 3332, 991, 1994], [488, 2541, 32, 552]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [3000, 1575, 1899], []]
 b := ![[], [], [1649, 1514, 3314, 2890], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A3637 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 3637 2 where
 D := ![[1567, 1], [2116, 1876, 514, 2070, 1]]; D' := ![[1567, 1], [2116, 1876, 514, 2070, 1]]
 heqm := by decide
 hProd := by decide
 s := ![11, 11]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P3637P0
  | 1 => exact P3637P1

def C36370 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A3637.D 0) 3637 where
  n := 1
  w := ![![3637, 0, 0, 0, 0], ![1567, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C36371 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A3637.D 1) 3637 where
  n := 4
  w := ![![3637, 0, 0, 0, 0], ![2764, 6048, 11409, 1102, 22728]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K3637 : KummerData 3637 ![I3637N0, I3637N1] ![3637, 174973872717361] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A3637
  C := by
    intro i
    match i with
    | 0 => exact C36370
    | 1 => exact C36371
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 3637 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp3643 : Fact (Nat.Prime 3643) := {out := by norm_num}

def I3643N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3643, 0, 0, 0, 0], ![2702, 3548, 1, 0, 0]] i)))

def I3643N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3643, 0, 0, 0, 0], ![1453, 2681, 95, 2, 0]] i)))

def P3643P0 : CertificateIrreducibleZModOfList' 3643 2 2 11 [2702, 3548, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [95, 3642], [0, 1]]
 g := ![![[244, 2142], [438, 786], [1178], [186, 1842], [2285, 597], [1309, 114], [1721], [16], [2634], [2082, 2047], [95, 1]], ![[3369, 1501], [2248, 2857], [1178], [312, 1801], [712, 3046], [1210, 3529], [1721], [16], [2634], [3468, 1596], [190, 3642]]]
 h' := ![![[95, 3642], [499, 1658], [1769, 1956], [162, 3551], [815, 2682], [435, 1738], [3172, 1383], [2551, 608], [3529, 4], [2871, 2866], [1963, 2680], [0, 1]], ![[0, 1], [1360, 1985], [1796, 1687], [2351, 92], [595, 961], [1610, 1905], [3409, 2260], [2023, 3035], [266, 3639], [1916, 777], [1553, 963], [95, 3642]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1230]]
 b := ![[], [1753, 615]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P3643P1 : CertificateIrreducibleZModOfList' 3643 3 2 11 [1453, 2680, 95, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1148, 2951, 3309], [2400, 691, 334], [0, 1]]
 g := ![![[2702, 2112, 1094], [448, 2018, 2175], [745, 2851], [2385, 3010, 322], [2001, 623, 1213], [3427, 650, 2944], [2568, 2520], [15, 3093], [1590, 1478], [1954, 1553, 1739], [1]], ![[1039, 1537, 141, 1350], [2300, 3485, 1744, 3077], [3397, 885], [151, 3518, 1984, 3519], [2764, 1182, 46, 1839], [944, 2691, 912, 178], [1527, 2351], [2110, 1197], [1336, 1301], [2567, 3437, 3131, 1815], [1572, 3300, 829, 900]], ![[2264, 2660, 3483, 38], [151, 1219, 1621, 3306], [181, 1732], [470, 137, 2475, 61], [1895, 1909, 2626, 142], [3431, 3398, 2185, 1207], [155, 160], [2760, 2097], [293, 1869], [2383, 3472, 2473, 2876], [1581, 2560, 3302, 2743]]]
 h' := ![![[1148, 2951, 3309], [1153, 443, 720], [626, 509, 2871], [2731, 1723, 1950], [3304, 1835, 2054], [550, 493, 2992], [2093, 3620, 2459], [2730, 197, 2149], [340, 3229, 1625], [2378, 2334, 2893], [2190, 963, 3548], [0, 1]], ![[2400, 691, 334], [3457, 348, 3473], [2499, 1239, 3284], [626, 1968, 3295], [1194, 2634, 1321], [878, 2726, 1164], [269, 1982, 1927], [2504, 1352, 2034], [1882, 603, 673], [2717, 2042, 2745], [1365, 2078, 2514], [1148, 2951, 3309]], ![[0, 1], [1748, 2852, 3093], [2631, 1895, 1131], [627, 3595, 2041], [139, 2817, 268], [996, 424, 3130], [1912, 1684, 2900], [2375, 2094, 3103], [1018, 3454, 1345], [604, 2910, 1648], [515, 602, 1224], [2400, 691, 334]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [934, 2196], []]
 b := ![[], [1658, 2686, 2777], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A3643 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 3643 2 where
 D := ![[2702, 3548, 1], [1453, 2680, 95, 1]]; D' := ![[2702, 3548, 1], [1453, 2680, 95, 1]]
 heqm := by decide
 hProd := by decide
 s := ![11, 11]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P3643P0
  | 1 => exact P3643P1

def C36430 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A3643.D 0) 3643 where
  n := 2
  w := ![![3643, 0, 0, 0, 0], ![2702, 3548, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C36431 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A3643.D 1) 3643 where
  n := 3
  w := ![![3643, 0, 0, 0, 0], ![1453, 2681, 95, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K3643 : KummerData 3643 ![I3643N0, I3643N1] ![13271449, 48347888707] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A3643
  C := by
    intro i
    match i with
    | 0 => exact C36430
    | 1 => exact C36431
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 3643 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp3659 : Fact (Nat.Prime 3659) := {out := by norm_num}

def I3659N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3659, 0, 0, 0, 0], ![897, 1, 0, 0, 0]] i)))

def I3659N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3659, 0, 0, 0, 0], ![1502, 1373, 1, 0, 0]] i)))

def I3659N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3659, 0, 0, 0, 0], ![1028, 1389, 1, 0, 0]] i)))

def P3659P0 : CertificateIrreducibleZModOfList' 3659 1 2 11 [897, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [1546], [], [930], [], [], [1097], [], [], [193], [3288, 2762, 1]]]
 h' := ![![[0, 1], [3658], [1764], [42], [739], [2782], [262], [1816], [664], [2511], [3477], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P3659P1 : CertificateIrreducibleZModOfList' 3659 2 2 11 [1502, 1373, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2286, 3658], [0, 1]]
 g := ![![[2113, 324], [1444, 299], [820], [3115, 2879], [2546], [1627], [1057, 2971], [3336], [2909], [2121, 101], [2286, 1]], ![[0, 3335], [725, 3360], [820], [1968, 780], [2546], [1627], [1659, 688], [3336], [2909], [2490, 3558], [913, 3658]]]
 h' := ![![[2286, 3658], [899, 3641], [3613, 3198], [1131, 1240], [2772, 802], [444, 1152], [392, 1446], [2541, 872], [3121, 748], [1247, 1926], [2229, 2901], [0, 1]], ![[0, 1], [0, 18], [3559, 461], [46, 2419], [2985, 2857], [3095, 2507], [1871, 2213], [1778, 2787], [637, 2911], [2306, 1733], [148, 758], [2286, 3658]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2950]]
 b := ![[], [874, 1475]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P3659P2 : CertificateIrreducibleZModOfList' 3659 2 2 11 [1028, 1389, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2270, 3658], [0, 1]]
 g := ![![[1030, 3449], [210, 419], [2991], [], [], [], [1528, 3189], [85], [278], [], [2270, 1]], ![[0, 210], [0, 3240], [2991], [], [], [], [3056, 470], [85], [278], [], [881, 3658]]]
 h' := ![![[2270, 3658], [1, 1030], [2471, 2125], [0, 919], [507], [2403], [2586], [0, 977], [3277, 1712], [0, 2216], [882], [0, 1]], ![[0, 1], [0, 2629], [0, 1534], [500, 2740], [507], [2403], [2586], [436, 2682], [0, 1947], [2854, 1443], [882], [2270, 3658]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3379]]
 b := ![[], [1563, 3519]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A3659 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 3659 3 where
 D := ![[897, 1], [1502, 1373, 1], [1028, 1389, 1]]; D' := ![[897, 1], [1502, 1373, 1], [1028, 1389, 1]]
 heqm := by decide
 hProd := by decide
 s := ![11, 11, 11]
 n := ![1, 2, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P3659P0
  | 1 => exact P3659P1
  | 2 => exact P3659P2

def C36590 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A3659.D 0) 3659 where
  n := 1
  w := ![![3659, 0, 0, 0, 0], ![897, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C36591 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A3659.D 1) 3659 where
  n := 2
  w := ![![3659, 0, 0, 0, 0], ![1502, 1373, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C36592 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A3659.D 2) 3659 where
  n := 2
  w := ![![3659, 0, 0, 0, 0], ![1028, 1389, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K3659 : KummerData 3659 ![I3659N0, I3659N1, I3659N2] ![3659, 13388281, 13388281] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A3659
  C := by
    intro i
    match i with
    | 0 => exact C36590
    | 1 => exact C36591
    | 2 => exact C36592
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 3659 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp3671 : Fact (Nat.Prime 3671) := {out := by norm_num}

def I3671N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3671, 0, 0, 0, 0], ![1610, 1, 0, 0, 0]] i)))

def I3671N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3671, 0, 0, 0, 0], ![3364, 1, 0, 0, 0]] i)))

def I3671N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3671, 0, 0, 0, 0], ![337, 493, 2368, 2, 0]] i)))

def P3671P0 : CertificateIrreducibleZModOfList' 3671 1 2 11 [1610, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [1457], [2956], [], [2557], [], [1642], [], [], [1874], [374, 2061, 1]]]
 h' := ![![[0, 1], [3670], [2127], [632], [2092], [372], [3171], [2558], [1876], [422], [3575], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P3671P1 : CertificateIrreducibleZModOfList' 3671 1 2 11 [3364, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [1411], [1558], [], [1405], [], [625], [], [], [472], [2474, 307, 1]]]
 h' := ![![[0, 1], [3670], [1076], [974], [1828], [816], [983], [25], [5], [1735], [3292], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P3671P2 : CertificateIrreducibleZModOfList' 3671 3 2 11 [337, 492, 2368, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2980, 3300, 2679], [1994, 370, 992], [0, 1]]
 g := ![![[721, 241, 3178], [2816, 3553, 3229], [1791, 1633, 1780], [918, 3497], [1500, 1285, 256], [3036, 274], [2372, 158, 676], [810, 230], [3657, 2661], [2340, 437, 1807], [1]], ![[2323, 2589, 1402, 3650], [1984, 2656, 281, 569], [522, 1195, 2799, 2482], [564, 2014], [1313, 561, 52, 1281], [2596, 3332], [3324, 3212, 474, 3235], [3108, 2218], [2292, 3139], [272, 37, 2067, 493], [2835, 2653, 2795, 832]], ![[696, 2144, 912, 1335], [3453, 1163, 1480, 1852], [2053, 3639, 509, 368], [2353, 579], [1656, 1822, 742, 577], [3627, 1726], [2606, 2699, 1582, 3332], [3579, 756], [260, 432], [2780, 2890, 636, 2378], [975, 2073, 168, 2839]]]
 h' := ![![[2980, 3300, 2679], [1797, 1008, 2584], [2148, 81, 1243], [514, 1803, 246], [1098, 917, 2422], [3156, 3386, 3655], [914, 259, 1060], [2971, 2125, 26], [384, 2243, 917], [685, 753, 1649], [3334, 3179, 1303], [0, 1]], ![[1994, 370, 992], [3593, 1867, 196], [1163, 105, 1445], [3548, 248, 2117], [1878, 2442, 1160], [3568, 1029, 1475], [3189, 3446, 3116], [2510, 3089, 1432], [0, 2336, 1128], [3577, 2285, 2652], [1832, 1456, 1030], [2980, 3300, 2679]], ![[0, 1], [330, 796, 891], [997, 3485, 983], [1573, 1620, 1308], [2047, 312, 89], [5, 2927, 2212], [737, 3637, 3166], [74, 2128, 2213], [3417, 2763, 1626], [1323, 633, 3041], [2951, 2707, 1338], [1994, 370, 992]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3224, 511], []]
 b := ![[], [3623, 1524, 3579], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A3671 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 3671 3 where
 D := ![[1610, 1], [3364, 1], [337, 492, 2368, 1]]; D' := ![[1610, 1], [3364, 1], [337, 492, 2368, 1]]
 heqm := by decide
 hProd := by decide
 s := ![11, 11, 11]
 n := ![1, 1, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P3671P0
  | 1 => exact P3671P1
  | 2 => exact P3671P2

def C36710 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A3671.D 0) 3671 where
  n := 1
  w := ![![3671, 0, 0, 0, 0], ![1610, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C36711 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A3671.D 1) 3671 where
  n := 1
  w := ![![3671, 0, 0, 0, 0], ![3364, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C36712 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A3671.D 2) 3671 where
  n := 3
  w := ![![3671, 0, 0, 0, 0], ![337, 493, 2368, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K3671 : KummerData 3671 ![I3671N0, I3671N1, I3671N2] ![3671, 3671, 49471280711] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A3671
  C := by
    intro i
    match i with
    | 0 => exact C36710
    | 1 => exact C36711
    | 2 => exact C36712
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 3671 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp3673 : Fact (Nat.Prime 3673) := {out := by norm_num}

def I3673N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3673, 0, 0, 0, 0], ![2944, 610, 1, 0, 0]] i)))

def I3673N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3673, 0, 0, 0, 0], ![2440, 1857, 3063, 2, 0]] i)))

def P3673P0 : CertificateIrreducibleZModOfList' 3673 2 2 11 [2944, 610, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3063, 3672], [0, 1]]
 g := ![![[896, 3542], [1935], [3318], [962, 3276], [98, 1193], [1938], [2047, 1875], [1824], [1131], [2279, 3135], [3063, 1]], ![[0, 131], [1935], [3318], [714, 397], [3295, 2480], [1938], [600, 1798], [1824], [1131], [3562, 538], [2453, 3672]]]
 h' := ![![[3063, 3672], [3390, 2956], [3245, 1647], [3428, 581], [1655, 1221], [2517, 2208], [1025, 567], [3061, 3136], [975, 2339], [1195, 2621], [3416, 1856], [0, 1]], ![[0, 1], [0, 717], [1304, 2026], [1626, 3092], [2464, 2452], [3628, 1465], [417, 3106], [61, 537], [2982, 1334], [140, 1052], [2540, 1817], [3063, 3672]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1767]]
 b := ![[], [3175, 2720]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P3673P1 : CertificateIrreducibleZModOfList' 3673 3 2 11 [2440, 1856, 3063, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1618, 218, 333], [2665, 3454, 3340], [0, 1]]
 g := ![![[2447, 3166, 961], [1981, 1819], [510, 3331], [2121, 3394, 3176], [2556, 991, 2912], [2027, 1202], [1841, 1342, 272], [3143, 2674], [1342, 17], [2757, 2540, 1127], [1]], ![[1804, 670, 2794, 790], [3184, 223], [3364, 73], [611, 3191, 1717, 2427], [3168, 1207, 2945, 2370], [36, 2524], [137, 1721, 1163, 1854], [2830, 59], [3084, 282], [2202, 398, 1935, 2253], [1472, 1383, 2403, 1368]], ![[1807, 2245, 343, 1784], [3653, 205], [3093, 2817], [2805, 1417, 3628, 609], [1147, 1757, 2800, 3309], [1203, 2063], [380, 1675, 2134, 1272], [3203, 315], [2971, 2062], [2856, 2347, 2287, 2003], [21, 2814, 2846, 2305]]]
 h' := ![![[1618, 218, 333], [808, 1584, 3642], [1036, 2017, 1256], [17, 439, 1443], [114, 1611, 1340], [3172, 3603, 2895], [39, 129, 2590], [2874, 2938, 1871], [1298, 1629, 480], [1856, 1588, 2287], [1233, 1817, 610], [0, 1]], ![[2665, 3454, 3340], [3431, 3193, 1676], [2933, 2410, 3586], [567, 230, 2801], [290, 765, 585], [1280, 2363, 152], [2560, 9, 986], [136, 787, 2963], [420, 3019, 250], [1030, 1989, 2240], [2448, 2742, 1327], [1618, 218, 333]], ![[0, 1], [1428, 2569, 2028], [2899, 2919, 2504], [741, 3004, 3102], [1696, 1297, 1748], [1093, 1380, 626], [3477, 3535, 97], [2501, 3621, 2512], [1157, 2698, 2943], [3325, 96, 2819], [1682, 2787, 1736], [2665, 3454, 3340]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3414, 2942], []]
 b := ![[], [3235, 1095, 1767], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A3673 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 3673 2 where
 D := ![[2944, 610, 1], [2440, 1856, 3063, 1]]; D' := ![[2944, 610, 1], [2440, 1856, 3063, 1]]
 heqm := by decide
 hProd := by decide
 s := ![11, 11]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P3673P0
  | 1 => exact P3673P1

def C36730 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A3673.D 0) 3673 where
  n := 2
  w := ![![3673, 0, 0, 0, 0], ![2944, 610, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C36731 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A3673.D 1) 3673 where
  n := 3
  w := ![![3673, 0, 0, 0, 0], ![2440, 1857, 3063, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K3673 : KummerData 3673 ![I3673N0, I3673N1] ![13490929, 49552182217] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A3673
  C := by
    intro i
    match i with
    | 0 => exact C36730
    | 1 => exact C36731
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 3673 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


lemma PB18792I56_primes (p : ℕ) :
  p ∈ Set.range ![3613, 3617, 3623, 3631, 3637, 3643, 3659, 3671, 3673] ↔ Nat.Prime p ∧ 3607 < p ∧ p ≤ 3673 := by
  rw [← List.mem_ofFn']
  convert primes_range 3607 3673 (by omega)
  decide

def PB18792I56 : PrimesBelowBoundCertificateInterval O 3607 3673 18792 where
  m := 9
  g := ![4, 2, 2, 3, 2, 2, 3, 3, 2]
  P := ![3613, 3617, 3623, 3631, 3637, 3643, 3659, 3671, 3673]
  hP := PB18792I56_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I3613N0, I3613N1, I3613N2, I3613N3]
    · exact ![I3617N0, I3617N1]
    · exact ![I3623N0, I3623N1]
    · exact ![I3631N0, I3631N1, I3631N2]
    · exact ![I3637N0, I3637N1]
    · exact ![I3643N0, I3643N1]
    · exact ![I3659N0, I3659N1, I3659N2]
    · exact ![I3671N0, I3671N1, I3671N2]
    · exact ![I3673N0, I3673N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · convert (containsPrimesAbove_of_KummerData K3613) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K3617) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K3623) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K3631) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K3637) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K3643) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K3659) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K3671) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K3673) <;> rfl
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![3613, 3613, 3613, 13053769]
    · exact ![3617, 171156751470721]
    · exact ![3623, 172295262524641]
    · exact ![3631, 3631, 47871688591]
    · exact ![3637, 174973872717361]
    · exact ![13271449, 48347888707]
    · exact ![3659, 13388281, 13388281]
    · exact ![3671, 3671, 49471280711]
    · exact ![13490929, 49552182217]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact (card_quot_of_KummerData K3613)
    · exact (card_quot_of_KummerData K3617)
    · exact (card_quot_of_KummerData K3623)
    · exact (card_quot_of_KummerData K3631)
    · exact (card_quot_of_KummerData K3637)
    · exact (card_quot_of_KummerData K3643)
    · exact (card_quot_of_KummerData K3659)
    · exact (card_quot_of_KummerData K3671)
    · exact (card_quot_of_KummerData K3673)
  β := ![I3613N0, I3613N1, I3613N2, I3617N0, I3623N0, I3631N0, I3631N1, I3637N0, I3659N0, I3671N0, I3671N1]
  Il := ![[I3613N0, I3613N1, I3613N2], [I3617N0], [I3623N0], [I3631N0, I3631N1], [I3637N0], [], [I3659N0], [I3671N0, I3671N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
