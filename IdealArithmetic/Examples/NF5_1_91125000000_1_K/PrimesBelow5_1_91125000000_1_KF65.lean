
import IdealArithmetic.Examples.NF5_1_91125000000_1_K.RI5_1_91125000000_1_K
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 

instance hp4271 : Fact (Nat.Prime 4271) := {out := by norm_num}

def I4271N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4271, 0, 0, 0, 0], ![1754, 1, 0, 0, 0]] i)))

def I4271N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4271, 0, 0, 0, 0], ![2723, 2763, 1, 0, 0]] i)))

def I4271N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4271, 0, 0, 0, 0], ![3553, 4025, 1, 0, 0]] i)))

def P4271P0 : CertificateIrreducibleZModOfList' 4271 1 2 12 [1754, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [1892], [108], [3723], [], [3151], [], [1671], [], [], [], [2517, 1]]]
 h' := ![![[0, 1], [4270], [2763], [217], [2503], [4091], [1847], [3243], [1600], [40], [1240], [1396], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P4271P1 : CertificateIrreducibleZModOfList' 4271 2 2 12 [2723, 2763, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1508, 4270], [0, 1]]
 g := ![![[619, 229], [3601, 1139], [2917, 3156], [4100, 1572], [845], [3664, 1225], [54], [1052, 524], [1576], [203], [1892], [1]], ![[0, 4042], [0, 3132], [0, 1115], [0, 2699], [845], [1621, 3046], [54], [1109, 3747], [1576], [203], [1892], [1]]]
 h' := ![![[1508, 4270], [693, 3520], [1069, 3735], [94, 3257], [1390, 1908], [4255, 1322], [2095, 35], [1245, 1180], [2823, 1647], [3674, 848], [3454, 673], [1548, 1508], [0, 1]], ![[0, 1], [0, 751], [0, 536], [0, 1014], [0, 2363], [3274, 2949], [3623, 4236], [3949, 3091], [777, 2624], [1158, 3423], [1840, 3598], [3440, 2763], [1508, 4270]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1175]]
 b := ![[], [1209, 2723]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P4271P2 : CertificateIrreducibleZModOfList' 4271 2 2 12 [3553, 4025, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [246, 4270], [0, 1]]
 g := ![![[3272, 1088], [1162, 600], [4229, 3504], [1344, 3872], [4054], [907, 2457], [1511], [9, 1279], [2181], [342], [722], [1]], ![[1847, 3183], [3548, 3671], [3471, 767], [1423, 399], [4054], [3118, 1814], [1511], [2860, 2992], [2181], [342], [722], [1]]]
 h' := ![![[246, 4270], [1471, 2140], [4012, 3185], [4017, 234], [778, 1903], [2034, 443], [4212, 373], [2191, 1195], [4047, 3610], [1036, 3247], [338, 1264], [718, 246], [0, 1]], ![[0, 1], [2578, 2131], [1658, 1086], [1787, 4037], [3377, 2368], [4237, 3828], [2008, 3898], [1462, 3076], [3739, 661], [1121, 1024], [3770, 3007], [1440, 4025], [246, 4270]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3760]]
 b := ![[], [3665, 1880]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A4271 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 4271 3 where
 D := ![[1754, 1], [2723, 2763, 1], [3553, 4025, 1]]; D' := ![[1754, 1], [2723, 2763, 1], [3553, 4025, 1]]
 heqm := by decide
 hProd := by decide
 s := ![12, 12, 12]
 n := ![1, 2, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P4271P0
  | 1 => exact P4271P1
  | 2 => exact P4271P2

def C42710 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A4271.D 0) 4271 where
  n := 1
  w := ![![4271, 0, 0, 0, 0], ![1754, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C42711 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A4271.D 1) 4271 where
  n := 2
  w := ![![4271, 0, 0, 0, 0], ![2723, 2763, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C42712 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A4271.D 2) 4271 where
  n := 2
  w := ![![4271, 0, 0, 0, 0], ![3553, 4025, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K4271 : KummerData 4271 ![I4271N0, I4271N1, I4271N2] ![4271, 18241441, 18241441] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A4271
  C := by
    intro i
    match i with
    | 0 => exact C42710
    | 1 => exact C42711
    | 2 => exact C42712
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 4271 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp4273 : Fact (Nat.Prime 4273) := {out := by norm_num}

def I4273N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4273, 0, 0, 0, 0], ![2425, 1, 0, 0, 0]] i)))

def I4273N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4273, 0, 0, 0, 0], ![712, 6140, 11872, 658, 22728]] i)))

def P4273P0 : CertificateIrreducibleZModOfList' 4273 1 2 12 [2425, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [], [406], [1066], [], [69], [], [], [], [1848, 1]]]
 h' := ![![[0, 1], [4272], [3073], [3948], [2513], [115], [2473], [3595], [4142], [599], [1650], [977], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P4273P1 : CertificateIrreducibleZModOfList' 4273 4 2 12 [64, 2190, 977, 1848, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3171, 2972, 3401, 3881], [3460, 2859, 750, 2327], [67, 2714, 122, 2338], [0, 1]]
 g := ![![[1219, 1132, 2527, 1291], [453, 4033, 332], [730, 447, 3935], [3281, 3177, 3947], [4011, 46, 3709, 3036], [378, 3333, 3529, 1348], [2509, 562, 344], [2629, 170, 3909, 3528], [572, 585, 3674], [3801, 2290, 977], [1], []], ![[446, 782, 221, 3641, 1112, 1516], [1950, 545, 132], [1770, 3971, 3485], [129, 3281, 4175], [1628, 800, 3004, 4172, 3096, 3222], [902, 2743, 3899, 3904, 3339, 3117], [3665, 3689, 527], [3649, 3120, 3821, 3468, 3929, 2337], [358, 502, 85], [1068, 3943, 2626], [3232, 817, 3202], [2114, 3930, 4109]], ![[853, 2381, 3659, 1695, 3317, 3222], [3210, 2156, 2096], [3709, 1792, 3879], [2802, 2373, 3675], [1240, 3107, 198, 742, 1058, 2975], [2396, 2777, 2668, 2828, 4165, 3257], [1759, 2034, 1916], [3678, 989, 957, 1094, 1348, 2320], [352, 2056, 1110], [3015, 4010, 3726], [3241, 86, 3599], [2287, 4085, 1038]], ![[1273, 480, 1622, 287, 2865, 3265], [3448, 3038, 216], [3425, 528, 3481], [482, 2302, 3973], [2703, 1357, 3995, 79, 882, 1508], [2281, 818, 3630, 300, 1781, 1090], [305, 768, 1736], [2677, 600, 379, 217, 525, 2377], [1973, 1394, 679], [1595, 403, 3121], [3669, 2268, 698], [4223, 3085, 1077]]]
 h' := ![![[3171, 2972, 3401, 3881], [4231, 2974, 1195, 2957], [3016, 1259, 1173, 4141], [1817, 1818, 831, 2270], [3949, 3946, 1637, 2345], [1446, 3281, 1006, 656], [1241, 3398, 1755, 3266], [2664, 1491, 2900, 3839], [3430, 1043, 4211, 2422], [120, 911, 1289, 2672], [4209, 2083, 3296, 2425], [0, 0, 1], [0, 1]], ![[3460, 2859, 750, 2327], [576, 3558, 305, 2359], [2454, 2506, 2278, 728], [850, 546, 3491, 2882], [1612, 3970, 2428, 2722], [1559, 1063, 881, 4158], [4041, 3484, 4046, 1863], [3021, 1576, 1189, 2314], [3792, 1432, 2147, 3165], [1800, 2055, 2085, 1540], [2350, 1280, 715, 1224], [2312, 3080, 3357, 1698], [3171, 2972, 3401, 3881]], ![[67, 2714, 122, 2338], [3830, 4202, 3406, 784], [1382, 2870, 3122, 3744], [1874, 1323, 2428, 3335], [1690, 3991, 2551, 1180], [2202, 4143, 1658, 3986], [369, 2632, 2665, 1446], [1285, 1657, 2079, 4083], [1004, 2491, 3439, 803], [1051, 3185, 2833, 2836], [2745, 3262, 1288, 2021], [1841, 3202, 1765, 158], [3460, 2859, 750, 2327]], ![[0, 1], [1645, 2085, 3640, 2446], [4262, 1911, 1973, 4206], [885, 586, 1796, 59], [121, 912, 1930, 2299], [2702, 59, 728, 4019], [4123, 3305, 80, 1971], [343, 3822, 2378, 2583], [1796, 3580, 3022, 2156], [1330, 2395, 2339, 1498], [3965, 1921, 3247, 2876], [3416, 2264, 3423, 2417], [67, 2714, 122, 2338]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [1996, 584, 3565], []]
 b := ![[], [], [2743, 2178, 2661, 1686], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A4273 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 4273 2 where
 D := ![[2425, 1], [64, 2190, 977, 1848, 1]]; D' := ![[2425, 1], [64, 2190, 977, 1848, 1]]
 heqm := by decide
 hProd := by decide
 s := ![12, 12]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P4273P0
  | 1 => exact P4273P1

def C42730 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A4273.D 0) 4273 where
  n := 1
  w := ![![4273, 0, 0, 0, 0], ![2425, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C42731 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A4273.D 1) 4273 where
  n := 4
  w := ![![4273, 0, 0, 0, 0], ![712, 6140, 11872, 658, 22728]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K4273 : KummerData 4273 ![I4273N0, I4273N1] ![4273, 333373881243841] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A4273
  C := by
    intro i
    match i with
    | 0 => exact C42730
    | 1 => exact C42731
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 4273 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp4283 : Fact (Nat.Prime 4283) := {out := by norm_num}

def I4283N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4283, 0, 0, 0, 0], ![2770, 1, 0, 0, 0]] i)))

def I4283N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4283, 0, 0, 0, 0], ![4446, 4017, 12942, -12, 22728]] i)))

def P4283P0 : CertificateIrreducibleZModOfList' 4283 1 2 12 [2770, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [2794], [], [301], [2666], [935], [], [912], [], [], [], [1513, 1]]]
 h' := ![![[0, 1], [1], [2064], [1415], [3355], [1265], [1808], [730], [1200], [3385], [1435], [2047], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P4283P1 : CertificateIrreducibleZModOfList' 4283 4 2 12 [3798, 402, 2047, 1513, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3105, 2814, 2387, 2043], [3833, 3804, 2107, 24], [115, 1947, 4072, 2216], [0, 1]]
 g := ![![[3318, 2800, 994, 1021], [1919, 3697, 3245, 1379], [99, 1702, 3094], [559, 3805, 1384, 2391], [1029, 2264, 3746, 4090], [3791, 2758, 2719, 2331], [3220, 264, 2780], [1438, 3699, 1141, 1321], [2042, 2214, 2314], [2928, 502, 2047], [1], []], ![[1812, 2941, 3676, 3693, 2200, 3511], [777, 2319, 2521, 895, 2652, 3802], [1855, 4238, 1396], [3960, 1847, 3178, 2438, 3185, 416], [1391, 3595, 2882, 6, 1992, 3006], [2732, 3227, 2328, 1381, 4055, 1318], [2724, 175, 1364], [3642, 3031, 3924, 3342, 406, 2984], [1275, 1143, 1414], [2896, 3326, 3338], [1421, 1603, 2217], [590, 2440, 2207]], ![[4131, 3739, 632, 3737, 2658, 45], [4085, 1558, 1292, 1771, 1758, 450], [1980, 3398, 3910], [3872, 1147, 2213, 1673, 1459, 1410], [2770, 4156, 1310, 3613, 3879, 3367], [3021, 1785, 1645, 4047, 784, 2336], [1327, 756, 3895], [3112, 2434, 162, 3189, 461, 4035], [2367, 2482, 1798], [1462, 2886, 493], [2189, 4164, 1671], [657, 588, 576]], ![[1275, 1132, 1109, 127, 582, 4132], [1750, 294, 828, 2756, 2033, 1772], [802, 2357, 2359], [1780, 2772, 249, 945, 3908, 1750], [1372, 4275, 2327, 3747, 1872, 2523], [2216, 3780, 321, 863, 2908, 2081], [2036, 3572, 3330], [2843, 1539, 40, 2467, 1908, 2620], [957, 2027, 2793], [4016, 1066, 3795], [3761, 3569, 3095], [759, 3189, 2338]]]
 h' := ![![[3105, 2814, 2387, 2043], [1304, 919, 2881, 1216], [1460, 4131, 2548, 1896], [1286, 3358, 3363, 1710], [2237, 3753, 1345, 2557], [1228, 3492, 899, 2510], [3027, 4167, 4167, 2177], [3584, 3124, 1868, 4102], [3335, 3414, 1710, 3668], [2067, 4204, 1792, 901], [485, 3881, 2236, 2770], [0, 0, 1], [0, 1]], ![[3833, 3804, 2107, 24], [21, 1350, 954, 3708], [3610, 1600, 3049, 1189], [276, 1727, 1704, 1458], [3484, 1582, 2703, 2346], [1591, 42, 151, 3031], [328, 1224, 947, 3175], [1832, 857, 3919, 136], [4237, 2438, 1957, 1475], [983, 688, 1526, 3661], [2235, 4039, 2651, 3501], [3464, 4260, 3067, 191], [3105, 2814, 2387, 2043]], ![[115, 1947, 4072, 2216], [2627, 62, 1316, 706], [3914, 1289, 2395, 1183], [466, 2906, 3200, 1918], [1914, 3460, 1904, 1328], [2737, 322, 3722, 793], [3320, 1173, 1272, 3164], [2713, 1732, 4002, 3360], [1133, 564, 181, 2279], [1113, 3104, 868, 1904], [707, 2045, 1283, 3348], [2902, 2451, 3648, 2117], [3833, 3804, 2107, 24]], ![[0, 1], [1575, 1952, 3415, 2936], [3249, 1546, 574, 15], [2323, 575, 299, 3480], [482, 4054, 2614, 2335], [993, 427, 3794, 2232], [54, 2002, 2180, 50], [2682, 2853, 3060, 968], [3415, 2150, 435, 1144], [3899, 570, 97, 2100], [1521, 2884, 2396, 3230], [153, 1855, 1850, 1975], [115, 1947, 4072, 2216]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [1811, 2099, 147], []]
 b := ![[], [], [2255, 1909, 3296, 1600], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A4283 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 4283 2 where
 D := ![[2770, 1], [3798, 402, 2047, 1513, 1]]; D' := ![[2770, 1], [3798, 402, 2047, 1513, 1]]
 heqm := by decide
 hProd := by decide
 s := ![12, 12]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P4283P0
  | 1 => exact P4283P1

def C42830 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A4283.D 0) 4283 where
  n := 1
  w := ![![4283, 0, 0, 0, 0], ![2770, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C42831 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A4283.D 1) 4283 where
  n := 4
  w := ![![4283, 0, 0, 0, 0], ![4446, 4017, 12942, -12, 22728]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K4283 : KummerData 4283 ![I4283N0, I4283N1] ![4283, 336505601239921] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A4283
  C := by
    intro i
    match i with
    | 0 => exact C42830
    | 1 => exact C42831
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 4283 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp4289 : Fact (Nat.Prime 4289) := {out := by norm_num}

def I4289N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4289, 0, 0, 0, 0], ![747, 1, 0, 0, 0]] i)))

def I4289N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4289, 0, 0, 0, 0], ![295, 3654, 1, 0, 0]] i)))

def I4289N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4289, 0, 0, 0, 0], ![1937, 4177, 1, 0, 0]] i)))

def P4289P0 : CertificateIrreducibleZModOfList' 4289 1 2 12 [747, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [], [], [], [2869], [3499], [], [], [], [3542, 1]]]
 h' := ![![[0, 1], [4288], [528], [4018], [1946], [1468], [1357], [2537], [2407], [3454], [4005], [439], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P4289P1 : CertificateIrreducibleZModOfList' 4289 2 2 12 [295, 3654, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [635, 4288], [0, 1]]
 g := ![![[2106, 2050], [3523], [3518], [2271], [3399], [1630], [1916, 367], [3660, 3021], [3478], [2957], [59], [1]], ![[0, 2239], [3523], [3518], [2271], [3399], [1630], [3355, 3922], [523, 1268], [3478], [2957], [59], [1]]]
 h' := ![![[635, 4288], [884, 1390], [768, 2127], [1017, 596], [3218, 4135], [2902, 2131], [928, 384], [1128, 1466], [1827, 1867], [3898, 1149], [996, 1646], [3994, 635], [0, 1]], ![[0, 1], [0, 2899], [378, 2162], [2045, 3693], [4075, 154], [763, 2158], [295, 3905], [1325, 2823], [3608, 2422], [94, 3140], [3979, 2643], [4053, 3654], [635, 4288]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [352]]
 b := ![[], [4166, 176]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P4289P2 : CertificateIrreducibleZModOfList' 4289 2 2 12 [1937, 4177, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [112, 4288], [0, 1]]
 g := ![![[817, 3694], [3884], [1255], [1912], [80], [114], [1083, 1727], [1503, 3801], [3762], [2510], [3966], [1]], ![[2801, 595], [3884], [1255], [1912], [80], [114], [1502, 2562], [2604, 488], [3762], [2510], [3966], [1]]]
 h' := ![![[112, 4288], [1558, 714], [2852, 3682], [2314, 2367], [2942, 682], [3127, 524], [3839, 2892], [920, 2667], [1981, 589], [4136, 1361], [2840, 1726], [2352, 112], [0, 1]], ![[0, 1], [35, 3575], [3492, 607], [1500, 1922], [2124, 3607], [1769, 3765], [1779, 1397], [3683, 1622], [3614, 3700], [2164, 2928], [3147, 2563], [2029, 4177], [112, 4288]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [626]]
 b := ![[], [3917, 313]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A4289 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 4289 3 where
 D := ![[747, 1], [295, 3654, 1], [1937, 4177, 1]]; D' := ![[747, 1], [295, 3654, 1], [1937, 4177, 1]]
 heqm := by decide
 hProd := by decide
 s := ![12, 12, 12]
 n := ![1, 2, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P4289P0
  | 1 => exact P4289P1
  | 2 => exact P4289P2

def C42890 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A4289.D 0) 4289 where
  n := 1
  w := ![![4289, 0, 0, 0, 0], ![747, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C42891 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A4289.D 1) 4289 where
  n := 2
  w := ![![4289, 0, 0, 0, 0], ![295, 3654, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C42892 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A4289.D 2) 4289 where
  n := 2
  w := ![![4289, 0, 0, 0, 0], ![1937, 4177, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K4289 : KummerData 4289 ![I4289N0, I4289N1, I4289N2] ![4289, 18395521, 18395521] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A4289
  C := by
    intro i
    match i with
    | 0 => exact C42890
    | 1 => exact C42891
    | 2 => exact C42892
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 4289 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp4297 : Fact (Nat.Prime 4297) := {out := by norm_num}

def I4297N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4297, 0, 0, 0, 0], ![1497, 1, 0, 0, 0]] i)))

def I4297N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4297, 0, 0, 0, 0], ![1992, 1, 0, 0, 0]] i)))

def I4297N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4297, 0, 0, 0, 0], ![2206, 1, 0, 0, 0]] i)))

def I4297N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4297, 0, 0, 0, 0], ![2853, 2899, 1, 0, 0]] i)))

def P4297P0 : CertificateIrreducibleZModOfList' 4297 1 2 12 [1497, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [3460], [], [], [1798], [1469], [], [], [], [2800, 1]]]
 h' := ![![[0, 1], [4296], [2325], [2562], [1114], [4133], [2613], [971], [1535], [2024], [1287], [2272], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P4297P1 : CertificateIrreducibleZModOfList' 4297 1 2 12 [1992, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [2073], [], [], [2618], [907], [], [], [], [2305, 1]]]
 h' := ![![[0, 1], [1], [1], [1], [1944], [79], [1502], [2293], [576], [24], [2396], [1933], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P4297P2 : CertificateIrreducibleZModOfList' 4297 1 2 12 [2206, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [1641], [], [], [2672], [2378], [], [], [], [2091, 1]]]
 h' := ![![[0, 1], [1], [4296], [2325], [2961], [2375], [1052], [769], [566], [2189], [1601], [2232], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P4297P3 : CertificateIrreducibleZModOfList' 4297 2 2 12 [2853, 2899, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1398, 4296], [0, 1]]
 g := ![![[1102, 491], [1471], [3353], [3154, 3917], [3091], [1695], [1439, 3581], [411, 3765], [3671], [1972], [3566], [1]], ![[0, 3806], [1471], [3353], [445, 380], [3091], [1695], [1672, 716], [56, 532], [3671], [1972], [3566], [1]]]
 h' := ![![[1398, 4296], [274, 1635], [2784, 902], [3853, 671], [1322, 1356], [2854, 3623], [2465, 1177], [498, 1632], [3605, 490], [2555, 3910], [2589, 3289], [1444, 1398], [0, 1]], ![[0, 1], [0, 2662], [462, 3395], [868, 3626], [2033, 2941], [1645, 674], [2160, 3120], [327, 2665], [1105, 3807], [2951, 387], [2821, 1008], [713, 2899], [1398, 4296]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3217]]
 b := ![[], [3621, 3757]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A4297 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 4297 4 where
 D := ![[1497, 1], [1992, 1], [2206, 1], [2853, 2899, 1]]; D' := ![[1497, 1], [1992, 1], [2206, 1], [2853, 2899, 1]]
 heqm := by decide
 hProd := by decide
 s := ![12, 12, 12, 12]
 n := ![1, 1, 1, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P4297P0
  | 1 => exact P4297P1
  | 2 => exact P4297P2
  | 3 => exact P4297P3

def C42970 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A4297.D 0) 4297 where
  n := 1
  w := ![![4297, 0, 0, 0, 0], ![1497, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C42971 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A4297.D 1) 4297 where
  n := 1
  w := ![![4297, 0, 0, 0, 0], ![1992, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C42972 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A4297.D 2) 4297 where
  n := 1
  w := ![![4297, 0, 0, 0, 0], ![2206, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C42973 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A4297.D 3) 4297 where
  n := 2
  w := ![![4297, 0, 0, 0, 0], ![2853, 2899, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K4297 : KummerData 4297 ![I4297N0, I4297N1, I4297N2, I4297N3] ![4297, 4297, 4297, 18464209] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A4297
  C := by
    intro i
    match i with
    | 0 => exact C42970
    | 1 => exact C42971
    | 2 => exact C42972
    | 3 => exact C42973
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 4297 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp4327 : Fact (Nat.Prime 4327) := {out := by norm_num}

def I4327N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4327, 0, 0, 0, 0], ![558, 1, 0, 0, 0]] i)))

def I4327N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4327, 0, 0, 0, 0], ![1376, 1, 0, 0, 0]] i)))

def I4327N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4327, 0, 0, 0, 0], ![3552, 1, 0, 0, 0]] i)))

def I4327N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4327, 0, 0, 0, 0], ![1690, 3168, 1, 0, 0]] i)))

def P4327P0 : CertificateIrreducibleZModOfList' 4327 1 2 12 [558, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [3032], [3033], [], [], [4286], [3528], [1050], [], [], [], [3769, 1]]]
 h' := ![![[0, 1], [1], [3770], [906], [310], [1243], [161], [2572], [1136], [3838], [2111], [4147], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P4327P1 : CertificateIrreducibleZModOfList' 4327 1 2 12 [1376, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [2544], [2819], [], [], [1727], [1152], [193], [], [], [], [2951, 1]]]
 h' := ![![[0, 1], [4326], [2375], [2994], [3575], [3498], [2857], [2706], [1823], [3014], [4170], [2477], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P4327P2 : CertificateIrreducibleZModOfList' 4327 1 2 12 [3552, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [4260], [1773], [], [], [3743], [806], [3394], [], [], [], [775, 1]]]
 h' := ![![[0, 1], [4326], [2416], [3752], [2960], [1735], [1562], [3861], [1950], [774], [1918], [3499], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P4327P3 : CertificateIrreducibleZModOfList' 4327 2 2 12 [1690, 3168, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1159, 4326], [0, 1]]
 g := ![![[1195, 1700], [680, 2351], [1313, 3159], [3724], [4037], [2648, 3926], [2685, 3286], [1845, 1428], [4290], [3140], [1911], [1]], ![[2710, 2627], [3806, 1976], [1952, 1168], [3724], [4037], [878, 401], [3399, 1041], [3983, 2899], [4290], [3140], [1911], [1]]]
 h' := ![![[1159, 4326], [1782, 3783], [781, 763], [2178, 3455], [1289, 2921], [3325, 2424], [1373, 405], [1717, 3409], [3373, 3894], [462, 2659], [2959, 2267], [2637, 1159], [0, 1]], ![[0, 1], [3028, 544], [2390, 3564], [4048, 872], [3014, 1406], [191, 1903], [3452, 3922], [2197, 918], [3458, 433], [1419, 1668], [3923, 2060], [221, 3168], [1159, 4326]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [315]]
 b := ![[], [2841, 2321]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A4327 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 4327 4 where
 D := ![[558, 1], [1376, 1], [3552, 1], [1690, 3168, 1]]; D' := ![[558, 1], [1376, 1], [3552, 1], [1690, 3168, 1]]
 heqm := by decide
 hProd := by decide
 s := ![12, 12, 12, 12]
 n := ![1, 1, 1, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P4327P0
  | 1 => exact P4327P1
  | 2 => exact P4327P2
  | 3 => exact P4327P3

def C43270 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A4327.D 0) 4327 where
  n := 1
  w := ![![4327, 0, 0, 0, 0], ![558, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C43271 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A4327.D 1) 4327 where
  n := 1
  w := ![![4327, 0, 0, 0, 0], ![1376, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C43272 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A4327.D 2) 4327 where
  n := 1
  w := ![![4327, 0, 0, 0, 0], ![3552, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C43273 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A4327.D 3) 4327 where
  n := 2
  w := ![![4327, 0, 0, 0, 0], ![1690, 3168, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K4327 : KummerData 4327 ![I4327N0, I4327N1, I4327N2, I4327N3] ![4327, 4327, 4327, 18722929] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A4327
  C := by
    intro i
    match i with
    | 0 => exact C43270
    | 1 => exact C43271
    | 2 => exact C43272
    | 3 => exact C43273
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 4327 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp4337 : Fact (Nat.Prime 4337) := {out := by norm_num}

def I4337N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4337, 0, 0, 0, 0], ![3048, 1, 0, 0, 0]] i)))

def I4337N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4337, 0, 0, 0, 0], ![4331, 6520, 11345, -460, 22728]] i)))

def P4337P0 : CertificateIrreducibleZModOfList' 4337 1 2 12 [3048, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [], [], [1849], [3294], [464], [1092], [], [], [], [1289, 1]]]
 h' := ![![[0, 1], [4336], [886], [777], [2348], [43], [3927], [2400], [374], [1740], [2998], [450], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P4337P1 : CertificateIrreducibleZModOfList' 4337 4 2 12 [3683, 3129, 450, 1289, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1095, 3138, 3518, 3029], [4237, 1012, 820, 4185], [2053, 186, 4336, 1460], [0, 1]]
 g := ![![[3523, 817, 3529, 111], [4108, 2480, 910], [2940, 3008, 2712], [2706, 991, 682], [1167, 3383, 3759, 3529], [1922, 1326, 1018, 3937], [44, 1805, 51, 3884], [115, 3342, 771, 646], [2554, 2474, 1614], [1081, 3229, 450], [1], []], ![[3324, 3920, 1137, 3305, 3767, 1336], [417, 424, 1933], [2030, 1713, 1546], [1278, 2036, 448], [1076, 66, 2658, 3631, 2592, 3395], [4170, 4117, 3811, 287, 2936, 482], [3818, 990, 751, 4134, 2648, 2944], [2579, 1464, 1876, 1451, 2653, 3392], [3519, 2971, 3900], [2852, 2287, 686], [1312, 4092, 644], [641, 112, 2086]], ![[3276, 4212, 447, 2247, 1406, 4003], [3860, 1885, 1088], [72, 2201, 2119], [608, 3815, 3423], [557, 2376, 3931, 1597, 4146, 3722], [1679, 1433, 3996, 1212, 2781, 3559], [3522, 2264, 502, 925, 1367, 291], [244, 3357, 1435, 2435, 3529, 3793], [4230, 788, 1700], [2794, 1363, 2261], [1074, 307, 1862], [2708, 3389, 1419]], ![[966, 3609, 3926, 2142, 2136, 1119], [1206, 1290, 2769], [549, 3054, 2888], [1903, 3215, 700], [270, 1495, 3619, 2746, 725, 3552], [3563, 1652, 3695, 2501, 381, 1920], [3466, 1632, 714, 216, 3976, 634], [1030, 743, 2873, 3721, 1465, 2944], [2095, 2993, 3778], [618, 2252, 3833], [98, 3813, 2598], [360, 1638, 2133]]]
 h' := ![![[1095, 3138, 3518, 3029], [443, 1873, 3911, 846], [1774, 2016, 2204, 3606], [390, 2869, 4214, 234], [4243, 588, 1173, 2466], [3595, 388, 3181, 492], [2754, 753, 3548, 3965], [1481, 385, 974, 3356], [1546, 4100, 4105, 1578], [2733, 1454, 3611, 2556], [654, 1208, 3887, 3048], [0, 0, 1], [0, 1]], ![[4237, 1012, 820, 4185], [4112, 1404, 2986, 1278], [2766, 1703, 2111, 1448], [3272, 74, 2996, 626], [3394, 3401, 716, 1919], [1583, 2061, 2124, 1941], [712, 2551, 3276, 3269], [1740, 1934, 3429, 608], [161, 310, 1756, 873], [4158, 4314, 2898, 1129], [2524, 2658, 1599, 4027], [538, 4273, 692, 1054], [1095, 3138, 3518, 3029]], ![[2053, 186, 4336, 1460], [4251, 3967, 3672, 1493], [1039, 4192, 2209, 1542], [3929, 1621, 4297, 3562], [646, 2030, 4230, 806], [1166, 108, 89, 277], [816, 2978, 2285, 814], [4280, 223, 3594, 4302], [3329, 3509, 2217, 487], [160, 1122, 221, 4096], [2590, 764, 3168, 3472], [2862, 2804, 1207, 1934], [4237, 1012, 820, 4185]], ![[0, 1], [2417, 1430, 2442, 720], [750, 763, 2150, 2078], [2792, 4110, 1504, 4252], [513, 2655, 2555, 3483], [898, 1780, 3280, 1627], [3685, 2392, 3902, 626], [2905, 1795, 677, 408], [306, 755, 596, 1399], [3822, 1784, 1944, 893], [2008, 4044, 20, 2464], [487, 1597, 2437, 1349], [2053, 186, 4336, 1460]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [4104, 716, 132], []]
 b := ![[], [], [960, 31, 3913, 115], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A4337 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 4337 2 where
 D := ![[3048, 1], [3683, 3129, 450, 1289, 1]]; D' := ![[3048, 1], [3683, 3129, 450, 1289, 1]]
 heqm := by decide
 hProd := by decide
 s := ![12, 12]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P4337P0
  | 1 => exact P4337P1

def C43370 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A4337.D 0) 4337 where
  n := 1
  w := ![![4337, 0, 0, 0, 0], ![3048, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C43371 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A4337.D 1) 4337 where
  n := 4
  w := ![![4337, 0, 0, 0, 0], ![4331, 6520, 11345, -460, 22728]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K4337 : KummerData 4337 ![I4337N0, I4337N1] ![4337, 353799885965761] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A4337
  C := by
    intro i
    match i with
    | 0 => exact C43370
    | 1 => exact C43371
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 4337 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp4339 : Fact (Nat.Prime 4339) := {out := by norm_num}

def I4339N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4339, 0, 0, 0, 0], ![771, 1, 0, 0, 0]] i)))

def I4339N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4339, 0, 0, 0, 0], ![3432, 1, 0, 0, 0]] i)))

def I4339N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4339, 0, 0, 0, 0], ![3116, 1859, 136, 2, 0]] i)))

def P4339P0 : CertificateIrreducibleZModOfList' 4339 1 2 12 [771, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [2555], [], [], [2357], [766], [1064], [451], [], [], [], [3568, 1]]]
 h' := ![![[0, 1], [1], [819], [1281], [794], [3857], [4066], [3738], [256], [16], [4], [4337], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P4339P1 : CertificateIrreducibleZModOfList' 4339 1 2 12 [3432, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [3210], [], [], [990], [24], [752], [2701], [], [], [], [907, 1]]]
 h' := ![![[0, 1], [1], [3052], [2642], [4096], [73], [841], [2611], [1641], [944], [3075], [2578], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P4339P2 : CertificateIrreducibleZModOfList' 4339 3 2 12 [3116, 1858, 136, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1693, 1160, 3382], [2510, 3178, 957], [0, 1]]
 g := ![![[3496, 2719, 96], [1406, 3044, 1947], [2836, 1889], [904, 1059], [2763, 1388, 2180], [2104, 1911, 1920], [1923, 1754, 448], [3490, 2783, 2734], [2573, 4198], [1289, 3522], [4203, 1], []], ![[2895, 2222, 2146, 1014], [1945, 4124, 717, 2906], [2940, 1310], [4326, 2805], [1323, 2160, 2439, 3982], [1315, 3897, 3725, 2270], [939, 876, 1038, 592], [1208, 2002, 711, 2179], [3456, 3721], [4223, 151], [2895, 2831], [1198, 320]], ![[3504, 98, 94, 2486], [2382, 1580, 1894, 4243], [2945, 783], [3460, 779], [527, 1566, 968, 3475], [866, 1631, 2749, 795], [2949, 458, 1564, 1691], [2074, 552, 918, 461], [4252, 871], [1605, 1618], [1141, 510], [3623, 320]]]
 h' := ![![[1693, 1160, 3382], [1294, 1240, 2657], [2408, 3369, 2689], [4310, 4134, 3388], [3407, 1549, 3467], [165, 2581, 557], [91, 148, 3278], [3033, 4120, 3126], [1058, 470, 3662], [908, 3337, 3072], [2893, 2249, 3621], [0, 0, 1], [0, 1]], ![[2510, 3178, 957], [337, 43, 2458], [19, 3201, 1895], [338, 1524, 2935], [4039, 3188, 2950], [3760, 4151, 3047], [1887, 552, 1096], [206, 2713, 3768], [4185, 3792, 2104], [2568, 1829, 61], [1331, 473, 361], [1081, 1838, 3178], [1693, 1160, 3382]], ![[0, 1], [1003, 3056, 3563], [388, 2108, 4094], [4030, 3020, 2355], [3392, 3941, 2261], [2729, 1946, 735], [3767, 3639, 4304], [1540, 1845, 1784], [3109, 77, 2912], [1875, 3512, 1206], [3475, 1617, 357], [682, 2501, 1160], [2510, 3178, 957]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [629, 2558], []]
 b := ![[], [3963, 846, 2850], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A4339 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 4339 3 where
 D := ![[771, 1], [3432, 1], [3116, 1858, 136, 1]]; D' := ![[771, 1], [3432, 1], [3116, 1858, 136, 1]]
 heqm := by decide
 hProd := by decide
 s := ![12, 12, 12]
 n := ![1, 1, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P4339P0
  | 1 => exact P4339P1
  | 2 => exact P4339P2

def C43390 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A4339.D 0) 4339 where
  n := 1
  w := ![![4339, 0, 0, 0, 0], ![771, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C43391 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A4339.D 1) 4339 where
  n := 1
  w := ![![4339, 0, 0, 0, 0], ![3432, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C43392 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A4339.D 2) 4339 where
  n := 3
  w := ![![4339, 0, 0, 0, 0], ![3116, 1859, 136, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K4339 : KummerData 4339 ![I4339N0, I4339N1, I4339N2] ![4339, 4339, 81690010219] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A4339
  C := by
    intro i
    match i with
    | 0 => exact C43390
    | 1 => exact C43391
    | 2 => exact C43392
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 4339 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp4349 : Fact (Nat.Prime 4349) := {out := by norm_num}

def I4349N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4349, 0, 0, 0, 0], ![896, 1, 0, 0, 0]] i)))

def I4349N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4349, 0, 0, 0, 0], ![2778, 1022, 1, 0, 0]] i)))

def I4349N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4349, 0, 0, 0, 0], ![2968, 2431, 1, 0, 0]] i)))

def P4349P0 : CertificateIrreducibleZModOfList' 4349 1 2 12 [896, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [156], [3302], [589], [20], [3770], [1642], [], [], [], [3453, 1]]]
 h' := ![![[0, 1], [4348], [3741], [3077], [2834], [3825], [1253], [3079], [3233], [195], [1654], [2600], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P4349P1 : CertificateIrreducibleZModOfList' 4349 2 2 12 [2778, 1022, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3327, 4348], [0, 1]]
 g := ![![[1497, 227], [904], [1553, 1014], [1191, 1172], [201, 245], [347, 2191], [264, 1280], [2187, 2391], [2837], [3472], [724], [1]], ![[0, 4122], [904], [307, 3335], [3731, 3177], [2053, 4104], [880, 2158], [1153, 3069], [2723, 1958], [2837], [3472], [724], [1]]]
 h' := ![![[3327, 4348], [3086, 1569], [4323, 686], [991, 3058], [2643, 4083], [1512, 2138], [1589, 1612], [67, 1326], [124, 2830], [3195, 3996], [124, 2189], [1571, 3327], [0, 1]], ![[0, 1], [0, 2780], [3420, 3663], [2646, 1291], [508, 266], [4023, 2211], [2396, 2737], [1783, 3023], [4298, 1519], [2994, 353], [2701, 2160], [2295, 1022], [3327, 4348]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2455]]
 b := ![[], [3171, 3402]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P4349P2 : CertificateIrreducibleZModOfList' 4349 2 2 12 [2968, 2431, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1918, 4348], [0, 1]]
 g := ![![[1661, 3779], [3554], [1547, 2029], [601, 1735], [3537, 4146], [2262, 2869], [2518, 24], [3277, 4167], [1946], [2509], [3819], [1]], ![[0, 570], [3554], [814, 2320], [1346, 2614], [1244, 203], [3519, 1480], [711, 4325], [2121, 182], [1946], [2509], [3819], [1]]]
 h' := ![![[1918, 4348], [409, 3630], [1048, 1111], [3671, 922], [670, 4271], [1240, 3457], [2507, 492], [2577, 3544], [202, 2024], [507, 2806], [1001, 1560], [1381, 1918], [0, 1]], ![[0, 1], [0, 719], [936, 3238], [2024, 3427], [3281, 78], [3890, 892], [2430, 3857], [2482, 805], [2926, 2325], [2702, 1543], [969, 2789], [851, 2431], [1918, 4348]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [681]]
 b := ![[], [1810, 2515]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A4349 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 4349 3 where
 D := ![[896, 1], [2778, 1022, 1], [2968, 2431, 1]]; D' := ![[896, 1], [2778, 1022, 1], [2968, 2431, 1]]
 heqm := by decide
 hProd := by decide
 s := ![12, 12, 12]
 n := ![1, 2, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P4349P0
  | 1 => exact P4349P1
  | 2 => exact P4349P2

def C43490 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A4349.D 0) 4349 where
  n := 1
  w := ![![4349, 0, 0, 0, 0], ![896, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C43491 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A4349.D 1) 4349 where
  n := 2
  w := ![![4349, 0, 0, 0, 0], ![2778, 1022, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C43492 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A4349.D 2) 4349 where
  n := 2
  w := ![![4349, 0, 0, 0, 0], ![2968, 2431, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K4349 : KummerData 4349 ![I4349N0, I4349N1, I4349N2] ![4349, 18913801, 18913801] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A4349
  C := by
    intro i
    match i with
    | 0 => exact C43490
    | 1 => exact C43491
    | 2 => exact C43492
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 4349 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


lemma PB18792I65_primes (p : ℕ) :
  p ∈ Set.range ![4271, 4273, 4283, 4289, 4297, 4327, 4337, 4339, 4349] ↔ Nat.Prime p ∧ 4261 < p ∧ p ≤ 4349 := by
  rw [← List.mem_ofFn']
  convert primes_range 4261 4349 (by omega)
  decide

def PB18792I65 : PrimesBelowBoundCertificateInterval O 4261 4349 18792 where
  m := 9
  g := ![3, 2, 2, 3, 4, 4, 2, 3, 3]
  P := ![4271, 4273, 4283, 4289, 4297, 4327, 4337, 4339, 4349]
  hP := PB18792I65_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I4271N0, I4271N1, I4271N2]
    · exact ![I4273N0, I4273N1]
    · exact ![I4283N0, I4283N1]
    · exact ![I4289N0, I4289N1, I4289N2]
    · exact ![I4297N0, I4297N1, I4297N2, I4297N3]
    · exact ![I4327N0, I4327N1, I4327N2, I4327N3]
    · exact ![I4337N0, I4337N1]
    · exact ![I4339N0, I4339N1, I4339N2]
    · exact ![I4349N0, I4349N1, I4349N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · convert (containsPrimesAbove_of_KummerData K4271) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K4273) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K4283) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K4289) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K4297) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K4327) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K4337) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K4339) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K4349) <;> rfl
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![4271, 18241441, 18241441]
    · exact ![4273, 333373881243841]
    · exact ![4283, 336505601239921]
    · exact ![4289, 18395521, 18395521]
    · exact ![4297, 4297, 4297, 18464209]
    · exact ![4327, 4327, 4327, 18722929]
    · exact ![4337, 353799885965761]
    · exact ![4339, 4339, 81690010219]
    · exact ![4349, 18913801, 18913801]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact (card_quot_of_KummerData K4271)
    · exact (card_quot_of_KummerData K4273)
    · exact (card_quot_of_KummerData K4283)
    · exact (card_quot_of_KummerData K4289)
    · exact (card_quot_of_KummerData K4297)
    · exact (card_quot_of_KummerData K4327)
    · exact (card_quot_of_KummerData K4337)
    · exact (card_quot_of_KummerData K4339)
    · exact (card_quot_of_KummerData K4349)
  β := ![I4271N0, I4273N0, I4283N0, I4289N0, I4297N0, I4297N1, I4297N2, I4327N0, I4327N1, I4327N2, I4337N0, I4339N0, I4339N1, I4349N0]
  Il := ![[I4271N0], [I4273N0], [I4283N0], [I4289N0], [I4297N0, I4297N1, I4297N2], [I4327N0, I4327N1, I4327N2], [I4337N0], [I4339N0, I4339N1], [I4349N0]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
