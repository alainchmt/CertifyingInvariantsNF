
import IdealArithmetic.Examples.NF5_1_91125000000_1_K.RI5_1_91125000000_1_K
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 

instance hp3391 : Fact (Nat.Prime 3391) := {out := by norm_num}

def I3391N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3391, 0, 0, 0, 0], ![742, 1, 0, 0, 0]] i)))

def I3391N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3391, 0, 0, 0, 0], ![1384, 1, 0, 0, 0]] i)))

def I3391N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3391, 0, 0, 0, 0], ![2051, 219, 1265, 2, 0]] i)))

def P3391P0 : CertificateIrreducibleZModOfList' 3391 1 2 11 [742, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [489], [3025], [233], [106], [800], [], [], [3046], [], [1222, 2649, 1]]]
 h' := ![![[0, 1], [3390], [292], [55], [2732], [3216], [872], [1778], [1665], [1000], [2064], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P3391P1 : CertificateIrreducibleZModOfList' 3391 1 2 11 [1384, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [860], [3010], [702], [487], [1835], [], [], [2460], [], [2932, 2007, 1]]]
 h' := ![![[0, 1], [1], [1699], [1649], [801], [219], [1518], [2385], [3315], [1959], [1139], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P3391P2 : CertificateIrreducibleZModOfList' 3391 3 2 11 [2051, 218, 1265, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1369, 1585, 788], [757, 1805, 2603], [0, 1]]
 g := ![![[206, 1673, 2254], [2177, 1574, 965], [1885, 10, 2470], [315, 2746, 2982], [1927, 1620, 405], [610, 342, 2425], [2937, 1442], [985, 805], [1105, 2879, 348], [2151, 3064], [1]], ![[950, 2592, 789, 1152], [1382, 2166, 978, 1430], [1329, 846, 3029, 2126], [3146, 2355, 695, 1529], [1302, 1910, 2054, 3060], [1902, 1065, 3320, 1404], [2828, 2034], [1862, 360], [1130, 905, 1243, 2462], [3203, 625], [1884, 956, 2466, 2918]], ![[1958, 2238, 422, 1082], [1932, 1422, 3213, 3004], [1970, 744, 656, 328], [3062, 1241, 22, 2201], [2389, 1976, 2013, 1742], [1499, 2471, 441, 1147], [949, 2273], [1485, 1411], [2885, 2012, 2996, 2193], [674, 2510], [847, 301, 3143, 473]]]
 h' := ![![[1369, 1585, 788], [920, 151, 1733], [2996, 2994, 3325], [1616, 1434, 1884], [1629, 2391, 1395], [169, 997, 1824], [3323, 653, 825], [2899, 2391, 1862], [2224, 2701, 662], [1751, 702, 2883], [1340, 3173, 2126], [0, 1]], ![[757, 1805, 2603], [3292, 2430, 1866], [2539, 2019, 2082], [3199, 1901, 236], [1472, 2331, 565], [1056, 276, 1974], [2888, 807, 2999], [196, 2018, 2532], [1292, 357, 118], [3306, 1583, 2464], [2517, 1621, 3366], [1369, 1585, 788]], ![[0, 1], [1031, 810, 3183], [3283, 1769, 1375], [500, 56, 1271], [2332, 2060, 1431], [1518, 2118, 2984], [2977, 1931, 2958], [2491, 2373, 2388], [1281, 333, 2611], [1638, 1106, 1435], [22, 1988, 1290], [757, 1805, 2603]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2539, 3062], []]
 b := ![[], [194, 523, 108], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A3391 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 3391 3 where
 D := ![[742, 1], [1384, 1], [2051, 218, 1265, 1]]; D' := ![[742, 1], [1384, 1], [2051, 218, 1265, 1]]
 heqm := by decide
 hProd := by decide
 s := ![11, 11, 11]
 n := ![1, 1, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P3391P0
  | 1 => exact P3391P1
  | 2 => exact P3391P2

def C33910 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A3391.D 0) 3391 where
  n := 1
  w := ![![3391, 0, 0, 0, 0], ![742, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C33911 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A3391.D 1) 3391 where
  n := 1
  w := ![![3391, 0, 0, 0, 0], ![1384, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C33912 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A3391.D 2) 3391 where
  n := 3
  w := ![![3391, 0, 0, 0, 0], ![2051, 219, 1265, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K3391 : KummerData 3391 ![I3391N0, I3391N1, I3391N2] ![3391, 3391, 38992705471] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A3391
  C := by
    intro i
    match i with
    | 0 => exact C33910
    | 1 => exact C33911
    | 2 => exact C33912
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 3391 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp3407 : Fact (Nat.Prime 3407) := {out := by norm_num}

def I3407N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3407, 0, 0, 0, 0], ![863, 1, 0, 0, 0]] i)))

def I3407N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3407, 0, 0, 0, 0], ![2752, 1, 0, 0, 0]] i)))

def I3407N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3407, 0, 0, 0, 0], ![2980, 1, 0, 0, 0]] i)))

def I3407N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3407, 0, 0, 0, 0], ![200, 219, 1, 0, 0]] i)))

def P3407P0 : CertificateIrreducibleZModOfList' 3407 1 2 11 [863, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [1287], [489], [36], [], [], [108], [], [2765], [], [2043, 2544, 1]]]
 h' := ![![[0, 1], [1], [461], [3002], [6], [994], [2192], [781], [2112], [1034], [1717], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P3407P1 : CertificateIrreducibleZModOfList' 3407 1 2 11 [2752, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [2039], [1354], [2403], [], [], [2347], [], [3032], [], [3150, 655, 1]]]
 h' := ![![[0, 1], [1], [1050], [3338], [1595], [1899], [728], [831], [3086], [2488], [2015], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P3407P2 : CertificateIrreducibleZModOfList' 3407 1 2 11 [2980, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [758], [2620], [1825], [], [], [366], [], [1329], [], [1758, 427, 1]]]
 h' := ![![[0, 1], [1], [1244], [2479], [1066], [2808], [2967], [460], [1921], [472], [1126], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P3407P3 : CertificateIrreducibleZModOfList' 3407 2 2 11 [200, 219, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3188, 3406], [0, 1]]
 g := ![![[1415, 971], [2557, 1054], [1871, 2663], [1040, 3221], [668], [338], [183, 2204], [568], [1422, 3045], [562], [3188, 1]], ![[0, 2436], [0, 2353], [1271, 744], [890, 186], [668], [338], [1301, 1203], [568], [2339, 362], [562], [2969, 3406]]]
 h' := ![![[3188, 3406], [3057, 434], [570, 656], [3234, 948], [1846, 2933], [3094, 2423], [877, 2998], [9, 1273], [1788, 2437], [2622, 2441], [2916, 63], [0, 1]], ![[0, 1], [0, 2973], [0, 2751], [42, 2459], [35, 474], [542, 984], [1866, 409], [596, 2134], [2984, 970], [2942, 966], [2747, 3344], [3188, 3406]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1510]]
 b := ![[], [2608, 755]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A3407 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 3407 4 where
 D := ![[863, 1], [2752, 1], [2980, 1], [200, 219, 1]]; D' := ![[863, 1], [2752, 1], [2980, 1], [200, 219, 1]]
 heqm := by decide
 hProd := by decide
 s := ![11, 11, 11, 11]
 n := ![1, 1, 1, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P3407P0
  | 1 => exact P3407P1
  | 2 => exact P3407P2
  | 3 => exact P3407P3

def C34070 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A3407.D 0) 3407 where
  n := 1
  w := ![![3407, 0, 0, 0, 0], ![863, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C34071 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A3407.D 1) 3407 where
  n := 1
  w := ![![3407, 0, 0, 0, 0], ![2752, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C34072 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A3407.D 2) 3407 where
  n := 1
  w := ![![3407, 0, 0, 0, 0], ![2980, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C34073 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A3407.D 3) 3407 where
  n := 2
  w := ![![3407, 0, 0, 0, 0], ![200, 219, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K3407 : KummerData 3407 ![I3407N0, I3407N1, I3407N2, I3407N3] ![3407, 3407, 3407, 11607649] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A3407
  C := by
    intro i
    match i with
    | 0 => exact C34070
    | 1 => exact C34071
    | 2 => exact C34072
    | 3 => exact C34073
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 3407 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp3413 : Fact (Nat.Prime 3413) := {out := by norm_num}

def I3413N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3413, 0, 0, 0, 0], ![2716, 2521, 1, 0, 0]] i)))

def I3413N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3413, 0, 0, 0, 0], ![3367, 1133, 892, 2, 0]] i)))

def P3413P0 : CertificateIrreducibleZModOfList' 3413 2 2 11 [2716, 2521, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [892, 3412], [0, 1]]
 g := ![![[1010, 1185], [767], [2442, 920], [784], [2783, 1205], [3312], [2270, 1628], [731], [1776, 3025], [1549], [892, 1]], ![[0, 2228], [767], [549, 2493], [784], [2548, 2208], [3312], [508, 1785], [731], [393, 388], [1549], [1784, 3412]]]
 h' := ![![[892, 3412], [1027, 546], [2400, 2834], [470, 168], [1167, 28], [2123, 483], [1971, 1539], [1606, 3342], [2366, 2709], [1926, 3358], [558, 1132], [0, 1]], ![[0, 1], [0, 2867], [1295, 579], [154, 3245], [2252, 3385], [2921, 2930], [2733, 1874], [3121, 71], [2390, 704], [648, 55], [54, 2281], [892, 3412]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1473]]
 b := ![[], [2582, 2443]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P3413P1 : CertificateIrreducibleZModOfList' 3413 3 2 11 [3367, 1132, 892, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3081, 1107, 46], [2853, 2305, 3367], [0, 1]]
 g := ![![[3109, 564, 804], [1098, 1898], [308, 1846, 2234], [149, 905], [786, 2955, 501], [2881, 2468], [1445, 114, 1816], [1311, 2196], [2858, 3253, 556], [54, 435], [1]], ![[3244, 880, 1182, 2192], [1583, 2318], [3145, 1572, 2358, 2402], [3000, 2096], [1795, 2290, 349, 1776], [2771, 844], [263, 3309, 1307, 1381], [2337, 2446], [2251, 832, 1925, 2677], [84, 2789], [352, 742, 2877, 1772]], ![[1947, 1230, 2376, 1196], [2830, 3279], [2072, 2532, 2656, 691], [3074, 1500], [335, 178, 1988, 2908], [2575, 1122], [1784, 738, 203, 2433], [367, 362], [770, 1617, 1851, 1496], [2456, 3144], [17, 758, 1014, 1641]]]
 h' := ![![[3081, 1107, 46], [2768, 998, 2603], [516, 585, 2854], [2278, 1808, 259], [2026, 677, 619], [2125, 2059, 1829], [1623, 84, 2943], [2575, 1774, 2848], [1774, 2547, 3036], [1187, 1497, 63], [46, 2281, 2521], [0, 1]], ![[2853, 2305, 3367], [1189, 1508, 1400], [409, 2930, 1225], [2023, 3375, 976], [3171, 3182, 586], [28, 668, 3353], [3274, 959, 2435], [534, 2942, 1133], [1591, 576, 2450], [838, 1146, 2471], [2358, 274, 1102], [3081, 1107, 46]], ![[0, 1], [1759, 907, 2823], [2916, 3311, 2747], [1429, 1643, 2178], [2063, 2967, 2208], [3287, 686, 1644], [3097, 2370, 1448], [1673, 2110, 2845], [3198, 290, 1340], [1510, 770, 879], [697, 858, 3203], [2853, 2305, 3367]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2439, 1123], []]
 b := ![[], [1091, 2584, 3166], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A3413 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 3413 2 where
 D := ![[2716, 2521, 1], [3367, 1132, 892, 1]]; D' := ![[2716, 2521, 1], [3367, 1132, 892, 1]]
 heqm := by decide
 hProd := by decide
 s := ![11, 11]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P3413P0
  | 1 => exact P3413P1

def C34130 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A3413.D 0) 3413 where
  n := 2
  w := ![![3413, 0, 0, 0, 0], ![2716, 2521, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C34131 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A3413.D 1) 3413 where
  n := 3
  w := ![![3413, 0, 0, 0, 0], ![3367, 1133, 892, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K3413 : KummerData 3413 ![I3413N0, I3413N1] ![11648569, 39756565997] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A3413
  C := by
    intro i
    match i with
    | 0 => exact C34130
    | 1 => exact C34131
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 3413 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp3433 : Fact (Nat.Prime 3433) := {out := by norm_num}

def I3433N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3433, 0, 0, 0, 0], ![2638, 1, 0, 0, 0]] i)))

def I3433N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3433, 0, 0, 0, 0], ![4036, 5359, 11248, -1448, 22728]] i)))

def P3433P0 : CertificateIrreducibleZModOfList' 3433 1 2 11 [2638, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [3338], [], [2288], [331], [], [2704], [], [353, 795, 1]]]
 h' := ![![[0, 1], [1], [1], [1], [2827], [2903], [2237], [2388], [622], [3381], [2562], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P3433P1 : CertificateIrreducibleZModOfList' 3433 4 2 11 [3388, 2462, 353, 795, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [343, 1165, 1051, 458], [1665, 21, 3333, 3314], [630, 2246, 2482, 3094], [0, 1]]
 g := ![![[2220, 2443, 2440, 3059], [355, 1033, 2187], [3392, 3216, 2727], [788, 1562, 2070, 808], [2778, 511, 94], [2077, 2277, 2498, 1551], [1619, 1646, 868, 1], [1993, 1542, 915], [2257, 2185, 2838, 3134], [0, 2638, 1], []], ![[76, 328, 1603, 1738, 3057, 845], [113, 2543, 2727], [2799, 3267, 2794], [216, 299, 2017, 2547, 586, 2379], [1796, 824, 2192], [344, 3123, 3413, 2514, 537, 409], [3103, 1153, 2794, 3015, 1646, 3079], [3051, 1239, 1838], [2916, 2606, 3209, 2441, 1753, 845], [1140, 182, 3249], [2952, 317, 1051, 1457, 2391, 2840]], ![[2754, 3418, 1630, 1871, 1214, 2516], [211, 2381, 2435], [3047, 1599, 1766], [27, 1727, 85, 1461, 365, 2259], [1992, 725, 2909], [477, 3132, 2402, 3124, 2066, 2372], [2232, 1814, 3026, 3184, 1741, 1291], [310, 473, 541], [3398, 2565, 1200, 164, 670, 1098], [1588, 3103, 2555], [79, 145, 2373, 2684, 2373, 444]], ![[2134, 2978, 1974, 539, 3188, 2429], [1346, 2792, 2754], [2004, 607, 1864], [1266, 615, 1154, 3112, 1036, 2070], [340, 671, 795], [3281, 1166, 1805, 1455, 2869, 2353], [1815, 1650, 1154, 2080, 1847, 1228], [561, 997, 3168], [2491, 839, 2980, 3078, 1367, 857], [1151, 1863, 3297], [2030, 1167, 606, 2759, 2118, 2898]]]
 h' := ![![[343, 1165, 1051, 458], [1414, 825, 1714, 617], [1412, 4, 1042, 2973], [1130, 2422, 401, 2643], [3156, 3252, 3196, 2508], [774, 1538, 1563, 1354], [762, 2528, 2879, 1534], [2149, 954, 885, 3432], [2008, 61, 465, 2301], [0, 1988, 525, 100], [0, 0, 0, 1], [0, 1]], ![[1665, 21, 3333, 3314], [2605, 2706, 420, 808], [1932, 2505, 1138, 2643], [2432, 3304, 1201, 3200], [303, 1536, 2628, 560], [1227, 2277, 2292, 3358], [1699, 2371, 3064, 2509], [3312, 3000, 2768, 480], [2813, 1734, 1406, 3234], [1535, 478, 1186, 808], [1078, 2916, 3356, 57], [343, 1165, 1051, 458]], ![[630, 2246, 2482, 3094], [1988, 890, 2350, 2434], [2345, 1809, 704, 3293], [1282, 1838, 3018, 842], [1682, 847, 1579, 2316], [1403, 53, 880, 3304], [1209, 2772, 182, 1319], [2619, 2260, 1983, 2590], [49, 3215, 1497, 1201], [2368, 660, 2419, 245], [422, 575, 3004, 1102], [1665, 21, 3333, 3314]], ![[0, 1], [220, 2445, 2382, 3007], [38, 2548, 549, 1390], [1119, 2735, 2246, 181], [3248, 1231, 2896, 1482], [3025, 2998, 2131, 2283], [2092, 2628, 741, 1504], [3039, 652, 1230, 364], [2934, 1856, 65, 130], [2118, 307, 2736, 2280], [3104, 3375, 506, 2273], [630, 2246, 2482, 3094]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [2712, 1719, 3027], []]
 b := ![[], [], [430, 1460, 1897, 2016], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A3433 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 3433 2 where
 D := ![[2638, 1], [3388, 2462, 353, 795, 1]]; D' := ![[2638, 1], [3388, 2462, 353, 795, 1]]
 heqm := by decide
 hProd := by decide
 s := ![11, 11]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P3433P0
  | 1 => exact P3433P1

def C34330 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A3433.D 0) 3433 where
  n := 1
  w := ![![3433, 0, 0, 0, 0], ![2638, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C34331 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A3433.D 1) 3433 where
  n := 4
  w := ![![3433, 0, 0, 0, 0], ![4036, 5359, 11248, -1448, 22728]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K3433 : KummerData 3433 ![I3433N0, I3433N1] ![3433, 138897750969121] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A3433
  C := by
    intro i
    match i with
    | 0 => exact C34330
    | 1 => exact C34331
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 3433 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp3449 : Fact (Nat.Prime 3449) := {out := by norm_num}

def I3449N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3449, 0, 0, 0, 0], ![1662, 1, 0, 0, 0]] i)))

def I3449N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3449, 0, 0, 0, 0], ![81, 193, 1, 0, 0]] i)))

def I3449N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3449, 0, 0, 0, 0], ![2282, 1594, 1, 0, 0]] i)))

def P3449P0 : CertificateIrreducibleZModOfList' 3449 1 2 11 [1662, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [745], [1982], [179], [1681], [], [824], [], [3044, 1787, 1]]]
 h' := ![![[0, 1], [1], [1], [1], [3160], [2565], [3317], [41], [3214], [1064], [555], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P3449P1 : CertificateIrreducibleZModOfList' 3449 2 2 11 [81, 193, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3256, 3448], [0, 1]]
 g := ![![[2983, 1320], [3113], [1245], [140, 2795], [2801, 3027], [2111, 788], [815, 1199], [3171], [666, 259], [1213], [3256, 1]], ![[0, 2129], [3113], [1245], [2198, 654], [1471, 422], [1783, 2661], [491, 2250], [3171], [2414, 3190], [1213], [3063, 3448]]]
 h' := ![![[3256, 3448], [2704, 1533], [2260, 3187], [2456, 3184], [753, 1240], [1459, 986], [2965, 564], [3112, 2255], [1238, 1811], [3215, 2847], [1837, 2678], [0, 1]], ![[0, 1], [0, 1916], [1091, 262], [1866, 265], [2863, 2209], [856, 2463], [1032, 2885], [2471, 1194], [64, 1638], [2135, 602], [2333, 771], [3256, 3448]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [483]]
 b := ![[], [24, 1966]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P3449P2 : CertificateIrreducibleZModOfList' 3449 2 2 11 [2282, 1594, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1855, 3448], [0, 1]]
 g := ![![[306, 326], [179], [1919], [3356, 2898], [1070, 755], [148, 995], [653, 3018], [2150], [2815, 781], [1202], [1855, 1]], ![[1461, 3123], [179], [1919], [2155, 551], [1301, 2694], [658, 2454], [1316, 431], [2150], [2990, 2668], [1202], [261, 3448]]]
 h' := ![![[1855, 3448], [1154, 300], [2519, 132], [1837, 842], [152, 1592], [266, 1564], [3271, 1493], [1872, 643], [1657, 975], [768, 1834], [2262, 90], [0, 1]], ![[0, 1], [2365, 3149], [2500, 3317], [1350, 2607], [968, 1857], [877, 1885], [3239, 1956], [1283, 2806], [3006, 2474], [2124, 1615], [211, 3359], [1855, 3448]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2526]]
 b := ![[], [2952, 1263]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A3449 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 3449 3 where
 D := ![[1662, 1], [81, 193, 1], [2282, 1594, 1]]; D' := ![[1662, 1], [81, 193, 1], [2282, 1594, 1]]
 heqm := by decide
 hProd := by decide
 s := ![11, 11, 11]
 n := ![1, 2, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P3449P0
  | 1 => exact P3449P1
  | 2 => exact P3449P2

def C34490 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A3449.D 0) 3449 where
  n := 1
  w := ![![3449, 0, 0, 0, 0], ![1662, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C34491 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A3449.D 1) 3449 where
  n := 2
  w := ![![3449, 0, 0, 0, 0], ![81, 193, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C34492 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A3449.D 2) 3449 where
  n := 2
  w := ![![3449, 0, 0, 0, 0], ![2282, 1594, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K3449 : KummerData 3449 ![I3449N0, I3449N1, I3449N2] ![3449, 11895601, 11895601] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A3449
  C := by
    intro i
    match i with
    | 0 => exact C34490
    | 1 => exact C34491
    | 2 => exact C34492
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 3449 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp3457 : Fact (Nat.Prime 3457) := {out := by norm_num}

def I3457N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3457, 0, 0, 0, 0], ![1725, 1, 0, 0, 0]] i)))

def I3457N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3457, 0, 0, 0, 0], ![3164, 4209, 13500, 426, 22728]] i)))

def P3457P0 : CertificateIrreducibleZModOfList' 3457 1 2 11 [1725, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [], [], [], [], [3232], [2892], [], [2605, 1732, 1]]]
 h' := ![![[0, 1], [3456], [708], [1936], [44], [588], [489], [941], [3208], [920], [475], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P3457P1 : CertificateIrreducibleZModOfList' 3457 4 2 11 [2516, 375, 2605, 1732, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1646, 2131, 3249, 780], [2262, 1225, 2242, 295], [1274, 100, 1423, 2382], [0, 1]]
 g := ![![[2206, 2119, 479, 2863], [3220, 3328, 1024], [3217, 2145, 2044], [2420, 1277, 3117], [642, 3249, 2153], [1312, 1867, 522], [1930, 1854, 2309], [3280, 2178, 18, 872], [927, 3051, 860, 3086], [0, 1725, 1], []], ![[1359, 361, 1138, 1325, 1997, 334], [1619, 2750, 3172], [22, 3438, 2805], [330, 1391, 987], [1, 1656, 2684], [1771, 2682, 52], [541, 3209, 3308], [2676, 3290, 1306, 2228, 2329, 1290], [1375, 3016, 2656, 2280, 2370, 3205], [946, 729, 2232], [1220, 1963, 871, 1611, 161, 2696]], ![[679, 2175, 849, 3072, 1087, 2998], [2725, 2749, 2174], [450, 2031, 2470], [1336, 1183, 811], [1507, 109, 795], [1030, 847, 2820], [1422, 1086, 1766], [2352, 2451, 3035, 3124, 1022, 1224], [2972, 163, 414, 2074, 1827, 2052], [444, 2942, 3085], [680, 25, 804, 192, 584, 693]], ![[1896, 1788, 2323, 673, 1813, 791], [1390, 2204, 813], [439, 675, 1659], [2601, 814, 593], [3038, 2489, 2921], [2211, 1409, 1267], [1750, 2742, 1123], [242, 2011, 3450, 1097, 2585, 488], [3398, 1527, 2712, 579, 2108, 548], [485, 3357, 3224], [1662, 1457, 2153, 2255, 1918, 274]]]
 h' := ![![[1646, 2131, 3249, 780], [1498, 62, 2424, 901], [3375, 3427, 3349, 3425], [2538, 976, 3177, 397], [3398, 3217, 911, 1979], [606, 320, 2538, 454], [3119, 362, 3033, 2727], [2836, 3349, 2309, 814], [1143, 3213, 2072, 2445], [0, 1892, 525, 100], [0, 0, 0, 1], [0, 1]], ![[2262, 1225, 2242, 295], [740, 234, 2473, 2067], [692, 1544, 2278, 2938], [2229, 373, 1072, 1542], [1417, 3117, 3425, 2382], [1918, 586, 2020, 268], [3416, 2899, 640, 564], [812, 1620, 3313, 1137], [2769, 3053, 2355, 3073], [1687, 2122, 2928, 830], [975, 1659, 1718, 581], [1646, 2131, 3249, 780]], ![[1274, 100, 1423, 2382], [2346, 382, 1281, 1315], [1312, 932, 1515, 672], [1152, 470, 2022, 560], [1447, 712, 1159, 3024], [382, 3086, 2292, 2001], [2404, 297, 2069, 2493], [2168, 1108, 2018, 938], [533, 387, 1060, 1788], [905, 436, 3298, 494], [3198, 3287, 2272, 116], [2262, 1225, 2242, 295]], ![[0, 1], [500, 2779, 736, 2631], [1321, 1011, 3229, 3336], [455, 1638, 643, 958], [2435, 3325, 1419, 2986], [210, 2922, 64, 734], [391, 3356, 1172, 1130], [1971, 837, 2731, 568], [591, 261, 1427, 3065], [2289, 2464, 163, 2033], [2566, 1968, 2924, 2759], [1274, 100, 1423, 2382]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [3007, 254, 3079], []]
 b := ![[], [], [985, 659, 1147, 13], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A3457 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 3457 2 where
 D := ![[1725, 1], [2516, 375, 2605, 1732, 1]]; D' := ![[1725, 1], [2516, 375, 2605, 1732, 1]]
 heqm := by decide
 hProd := by decide
 s := ![11, 11]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P3457P0
  | 1 => exact P3457P1

def C34570 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A3457.D 0) 3457 where
  n := 1
  w := ![![3457, 0, 0, 0, 0], ![1725, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C34571 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A3457.D 1) 3457 where
  n := 4
  w := ![![3457, 0, 0, 0, 0], ![3164, 4209, 13500, 426, 22728]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K3457 : KummerData 3457 ![I3457N0, I3457N1] ![3457, 142822791820801] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A3457
  C := by
    intro i
    match i with
    | 0 => exact C34570
    | 1 => exact C34571
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 3457 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp3461 : Fact (Nat.Prime 3461) := {out := by norm_num}

def I3461N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3461, 0, 0, 0, 0], ![1974, 1, 0, 0, 0]] i)))

def I3461N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3461, 0, 0, 0, 0], ![2751, 1, 0, 0, 0]] i)))

def I3461N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3461, 0, 0, 0, 0], ![534, 2011, 2197, 2, 0]] i)))

def P3461P0 : CertificateIrreducibleZModOfList' 3461 1 2 11 [1974, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [1464], [], [], [], [], [3284], [2447], [], [3051, 1487, 1]]]
 h' := ![![[0, 1], [1], [3460], [3324], [691], [2740], [2342], [3298], [1178], [1354], [2927], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P3461P1 : CertificateIrreducibleZModOfList' 3461 1 2 11 [2751, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [1711], [], [], [], [], [2318], [3028], [], [2255, 710, 1]]]
 h' := ![![[0, 1], [1], [3460], [3208], [614], [3024], [1224], [1805], [599], [2289], [2068], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P3461P2 : CertificateIrreducibleZModOfList' 3461 3 2 11 [534, 2010, 2197, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [26, 2407, 838], [1238, 1053, 2623], [0, 1]]
 g := ![![[3098, 823, 2678], [1031, 2683], [22, 192, 1744], [770, 1798], [3297, 2998], [145, 3242], [584, 1498], [2524, 1803, 3112], [2579, 344, 854], [634, 2175], [1]], ![[17, 3256, 1142, 1130], [3150, 2598], [1628, 1855, 2297, 3317], [661, 1443], [2211, 841], [1236, 2289], [2384, 1525], [3288, 986, 2211, 1701], [1419, 616, 751, 2283], [146, 2438], [2414, 1751, 1571, 3181]], ![[3347, 2932, 1872, 3277], [2178, 224], [405, 2776, 3338, 985], [2700, 726], [1831, 3026], [953, 3288], [2551, 3294], [3422, 2803, 2565, 2824], [3294, 312, 947, 2321], [2334, 3452], [50, 3378, 2907, 280]]]
 h' := ![![[26, 2407, 838], [952, 2443, 2796], [2096, 395, 532], [125, 1145, 2837], [1139, 1267, 1103], [2135, 850, 165], [2685, 391, 2244], [1974, 2142, 3352], [292, 1093, 1075], [1976, 1614, 2329], [2927, 1451, 1264], [0, 1]], ![[1238, 1053, 2623], [2592, 2388, 660], [1647, 3359, 1729], [1326, 20, 1331], [2964, 1760, 1243], [2454, 1223, 29], [2508, 1285, 1393], [2541, 3376, 1634], [1436, 2586, 2458], [2030, 947, 1330], [2148, 1004, 3095], [26, 2407, 838]], ![[0, 1], [1783, 2091, 5], [1364, 3168, 1200], [1734, 2296, 2754], [1853, 434, 1115], [3449, 1388, 3267], [1339, 1785, 3285], [2760, 1404, 1936], [3000, 3243, 3389], [1585, 900, 3263], [613, 1006, 2563], [1238, 1053, 2623]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3124, 3064], []]
 b := ![[], [1730, 1107, 938], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A3461 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 3461 3 where
 D := ![[1974, 1], [2751, 1], [534, 2010, 2197, 1]]; D' := ![[1974, 1], [2751, 1], [534, 2010, 2197, 1]]
 heqm := by decide
 hProd := by decide
 s := ![11, 11, 11]
 n := ![1, 1, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P3461P0
  | 1 => exact P3461P1
  | 2 => exact P3461P2

def C34610 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A3461.D 0) 3461 where
  n := 1
  w := ![![3461, 0, 0, 0, 0], ![1974, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C34611 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A3461.D 1) 3461 where
  n := 1
  w := ![![3461, 0, 0, 0, 0], ![2751, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C34612 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A3461.D 2) 3461 where
  n := 3
  w := ![![3461, 0, 0, 0, 0], ![534, 2011, 2197, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K3461 : KummerData 3461 ![I3461N0, I3461N1, I3461N2] ![3461, 3461, 41457661181] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A3461
  C := by
    intro i
    match i with
    | 0 => exact C34610
    | 1 => exact C34611
    | 2 => exact C34612
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 3461 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp3463 : Fact (Nat.Prime 3463) := {out := by norm_num}

def I3463N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3463, 0, 0, 0, 0], ![1816, 2924, 1, 0, 0]] i)))

def I3463N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3463, 0, 0, 0, 0], ![3195, 1277, 539, 2, 0]] i)))

def P3463P0 : CertificateIrreducibleZModOfList' 3463 2 2 11 [1816, 2924, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [539, 3462], [0, 1]]
 g := ![![[1428, 2336], [2901, 817], [2441, 112], [227], [1772], [1117], [2075], [1970, 2506], [1913, 1974], [566], [539, 1]], ![[0, 1127], [0, 2646], [475, 3351], [227], [1772], [1117], [2075], [2134, 957], [2758, 1489], [566], [1078, 3462]]]
 h' := ![![[539, 3462], [2470, 1955], [3247, 1189], [2536, 2480], [1127, 2594], [1938, 1643], [2217, 1575], [3222, 406], [2844, 1772], [1683, 346], [1205, 1276], [0, 1]], ![[0, 1], [0, 1508], [0, 2274], [2538, 983], [241, 869], [987, 1820], [2707, 1888], [424, 3057], [2164, 1691], [1175, 3117], [3295, 2187], [539, 3462]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2872]]
 b := ![[], [854, 1436]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P3463P1 : CertificateIrreducibleZModOfList' 3463 3 2 11 [3195, 1276, 539, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [842, 2654, 2342], [2082, 808, 1121], [0, 1]]
 g := ![![[2665, 1937, 2236], [3277, 71, 491], [3231, 2557, 283], [2150, 2832], [2111, 2812], [2132, 1222], [2129, 559], [1849, 1774, 1072], [1921, 1603, 1730], [3295, 3092], [1]], ![[1532, 2776, 625, 2026], [96, 255, 1510, 99], [2913, 1219, 1754, 1254], [165, 2494], [2187, 2434], [2390, 686], [1506, 2016], [1220, 2748, 100, 153], [3276, 3149, 1700, 404], [1400, 1739], [636, 2366, 575, 1894]], ![[1345, 2825, 2954, 1352], [1486, 2284, 1074, 436], [1333, 2637, 2832, 1009], [2152, 128], [2864, 3031], [2359, 3249], [3409, 3295], [1596, 2102, 1964, 2145], [1167, 1128, 1671, 1469], [425, 590], [815, 36, 709, 1569]]]
 h' := ![![[842, 2654, 2342], [2097, 825, 2291], [158, 1763, 574], [22, 1757, 1004], [225, 666, 1080], [1991, 3032, 1417], [3079, 1209, 2433], [323, 3080, 2877], [2304, 748, 2568], [2559, 2399, 2033], [268, 2187, 2924], [0, 1]], ![[2082, 808, 1121], [1163, 2362, 1682], [533, 1137, 800], [1132, 2205, 1740], [1157, 59, 1386], [3227, 2579, 477], [348, 1111, 1087], [1867, 2354, 874], [2010, 317, 145], [1980, 1496, 2674], [3435, 884, 1003], [842, 2654, 2342]], ![[0, 1], [2469, 276, 2953], [141, 563, 2089], [2683, 2964, 719], [1887, 2738, 997], [900, 1315, 1569], [3083, 1143, 3406], [3055, 1492, 3175], [2654, 2398, 750], [1825, 3031, 2219], [2486, 392, 2999], [2082, 808, 1121]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2122, 1965], []]
 b := ![[], [2884, 546, 2192], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A3463 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 3463 2 where
 D := ![[1816, 2924, 1], [3195, 1276, 539, 1]]; D' := ![[1816, 2924, 1], [3195, 1276, 539, 1]]
 heqm := by decide
 hProd := by decide
 s := ![11, 11]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P3463P0
  | 1 => exact P3463P1

def C34630 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A3463.D 0) 3463 where
  n := 2
  w := ![![3463, 0, 0, 0, 0], ![1816, 2924, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C34631 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A3463.D 1) 3463 where
  n := 3
  w := ![![3463, 0, 0, 0, 0], ![3195, 1277, 539, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K3463 : KummerData 3463 ![I3463N0, I3463N1] ![11992369, 41529573847] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A3463
  C := by
    intro i
    match i with
    | 0 => exact C34630
    | 1 => exact C34631
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 3463 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp3467 : Fact (Nat.Prime 3467) := {out := by norm_num}

def I3467N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3467, 0, 0, 0, 0], ![81, 1, 0, 0, 0]] i)))

def I3467N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3467, 0, 0, 0, 0], ![1738, 7865, 13989, 3734, 22728]] i)))

def P3467P0 : CertificateIrreducibleZModOfList' 3467 1 2 11 [81, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [3253], [], [2240], [], [], [], [705], [2413], [], [3094, 3386, 1]]]
 h' := ![![[0, 1], [3466], [1541], [2311], [3078], [1392], [566], [1834], [2166], [2406], [2477], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P3467P1 : CertificateIrreducibleZModOfList' 3467 4 2 11 [1090, 2377, 3094, 3386, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2086, 2364, 526, 3066], [3285, 1916, 1727, 413], [1644, 2653, 1214, 3455], [0, 1]]
 g := ![![[2918, 2710, 2251, 711], [431, 2514, 1156, 680], [2932, 1263, 1208], [2827, 2240, 1886, 1034], [3012, 2078, 1211], [2586, 144, 1287], [3222, 930, 2155], [49, 1734, 3451, 1031], [1711, 1612, 3179, 3066], [0, 81, 1], []], ![[825, 535, 2984, 1944, 663, 2316], [2468, 2033, 510, 3283, 3233, 2248], [2903, 1784, 3001], [2967, 1254, 3264, 788, 2286, 1346], [500, 3418, 1094], [639, 1321, 1103], [1815, 127, 271], [1860, 1696, 347, 3334, 3166, 2018], [1289, 307, 300, 572, 1314, 1899], [2974, 2694, 2240], [2459, 2366, 2413, 221, 462, 1532]], ![[2329, 1250, 445, 1606, 1256, 2831], [2232, 1442, 3091, 131, 453, 2937], [1476, 3267, 2057], [93, 1592, 3191, 2169, 1130, 2876], [2798, 211, 2431], [304, 1201, 3036], [859, 813, 334], [214, 3115, 359, 2560, 1284, 3000], [492, 721, 3343, 416, 536, 3207], [897, 3461, 597], [2014, 2306, 2957, 2259, 1176, 2491]], ![[3301, 2318, 1855, 2311, 2070, 1608], [1649, 2006, 2104, 1617, 72, 2224], [152, 1780, 1856], [499, 101, 1725, 1994, 1528, 577], [2695, 3269, 1453], [1904, 322, 1062], [877, 1735, 1986], [328, 796, 2299, 1234, 2283, 3177], [2696, 1451, 275, 2938, 953, 255], [825, 3297, 3401], [1568, 957, 3189, 3435, 3110, 1739]]]
 h' := ![![[2086, 2364, 526, 3066], [1722, 918, 1369, 1983], [598, 1812, 804, 1217], [733, 359, 916, 3208], [3111, 3127, 3303, 461], [2327, 2758, 74, 1483], [1393, 2418, 2450, 1754], [2062, 523, 1400, 2012], [256, 433, 1476, 795], [0, 1852, 525, 100], [0, 0, 0, 1], [0, 1]], ![[3285, 1916, 1727, 413], [2397, 216, 1543, 604], [1971, 2409, 456, 2875], [1313, 2173, 1173, 1607], [50, 1485, 704, 629], [2415, 404, 1561, 870], [522, 1629, 1125, 2528], [639, 192, 3260, 3034], [606, 2882, 1776, 1701], [2655, 2436, 12, 405], [98, 1427, 1326, 3078], [2086, 2364, 526, 3066]], ![[1644, 2653, 1214, 3455], [2522, 2687, 1224, 2078], [2214, 887, 593, 2562], [2700, 727, 2607, 1768], [1871, 3125, 2172, 2633], [2415, 1782, 1220, 573], [1361, 2948, 2858, 2350], [2305, 1536, 1739, 2027], [3090, 104, 2057, 612], [379, 270, 2215, 3155], [3363, 197, 3375, 244], [3285, 1916, 1727, 413]], ![[0, 1], [2210, 3113, 2798, 2269], [3343, 1826, 1614, 280], [153, 208, 2238, 351], [274, 2664, 755, 3211], [2813, 1990, 612, 541], [1273, 3406, 501, 302], [1381, 1216, 535, 3328], [3022, 48, 1625, 359], [291, 2376, 715, 3274], [1296, 1843, 2233, 144], [1644, 2653, 1214, 3455]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [1185, 498, 1630], []]
 b := ![[], [], [944, 2237, 538, 80], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A3467 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 3467 2 where
 D := ![[81, 1], [1090, 2377, 3094, 3386, 1]]; D' := ![[81, 1], [1090, 2377, 3094, 3386, 1]]
 heqm := by decide
 hProd := by decide
 s := ![11, 11]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P3467P0
  | 1 => exact P3467P1

def C34670 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A3467.D 0) 3467 where
  n := 1
  w := ![![3467, 0, 0, 0, 0], ![81, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C34671 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A3467.D 1) 3467 where
  n := 4
  w := ![![3467, 0, 0, 0, 0], ![1738, 7865, 13989, 3734, 22728]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K3467 : KummerData 3467 ![I3467N0, I3467N1] ![3467, 144482539567921] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A3467
  C := by
    intro i
    match i with
    | 0 => exact C34670
    | 1 => exact C34671
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 3467 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


lemma PB18792I53_primes (p : ℕ) :
  p ∈ Set.range ![3391, 3407, 3413, 3433, 3449, 3457, 3461, 3463, 3467] ↔ Nat.Prime p ∧ 3389 < p ∧ p ≤ 3467 := by
  rw [← List.mem_ofFn']
  convert primes_range 3389 3467 (by omega)
  decide

def PB18792I53 : PrimesBelowBoundCertificateInterval O 3389 3467 18792 where
  m := 9
  g := ![3, 4, 2, 2, 3, 2, 3, 2, 2]
  P := ![3391, 3407, 3413, 3433, 3449, 3457, 3461, 3463, 3467]
  hP := PB18792I53_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I3391N0, I3391N1, I3391N2]
    · exact ![I3407N0, I3407N1, I3407N2, I3407N3]
    · exact ![I3413N0, I3413N1]
    · exact ![I3433N0, I3433N1]
    · exact ![I3449N0, I3449N1, I3449N2]
    · exact ![I3457N0, I3457N1]
    · exact ![I3461N0, I3461N1, I3461N2]
    · exact ![I3463N0, I3463N1]
    · exact ![I3467N0, I3467N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · convert (containsPrimesAbove_of_KummerData K3391) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K3407) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K3413) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K3433) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K3449) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K3457) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K3461) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K3463) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K3467) <;> rfl
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![3391, 3391, 38992705471]
    · exact ![3407, 3407, 3407, 11607649]
    · exact ![11648569, 39756565997]
    · exact ![3433, 138897750969121]
    · exact ![3449, 11895601, 11895601]
    · exact ![3457, 142822791820801]
    · exact ![3461, 3461, 41457661181]
    · exact ![11992369, 41529573847]
    · exact ![3467, 144482539567921]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact (card_quot_of_KummerData K3391)
    · exact (card_quot_of_KummerData K3407)
    · exact (card_quot_of_KummerData K3413)
    · exact (card_quot_of_KummerData K3433)
    · exact (card_quot_of_KummerData K3449)
    · exact (card_quot_of_KummerData K3457)
    · exact (card_quot_of_KummerData K3461)
    · exact (card_quot_of_KummerData K3463)
    · exact (card_quot_of_KummerData K3467)
  β := ![I3391N0, I3391N1, I3407N0, I3407N1, I3407N2, I3433N0, I3449N0, I3457N0, I3461N0, I3461N1, I3467N0]
  Il := ![[I3391N0, I3391N1], [I3407N0, I3407N1, I3407N2], [], [I3433N0], [I3449N0], [I3457N0], [I3461N0, I3461N1], [], [I3467N0]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
