
import IdealArithmetic.Examples.NF5_1_91125000000_1_K.RI5_1_91125000000_1_K
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 

instance hp14831 : Fact (Nat.Prime 14831) := {out := by norm_num}

def I14831N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14831, 0, 0, 0, 0], ![10291, 1, 0, 0, 0]] i)))

def I14831N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14831, 0, 0, 0, 0], ![14429, 1, 0, 0, 0]] i)))

def I14831N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14831, 0, 0, 0, 0], ![13222, 10672, 4942, 2, 0]] i)))

def P14831P0 : CertificateIrreducibleZModOfList' 14831 1 2 13 [10291, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [2976], [10059], [6239], [], [14609], [2165], [8591], [4557], [], [], [3876], [11341, 4540, 1]]]
 h' := ![![[0, 1], [14830], [3211], [12681], [8778], [628], [10978], [12441], [14366], [11063], [7130], [7474], [9739], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P14831P1 : CertificateIrreducibleZModOfList' 14831 1 2 13 [14429, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [7932], [7789], [7269], [], [996], [1113], [4107], [4228], [], [], [8760], [13294, 402, 1]]]
 h' := ![![[0, 1], [14830], [1837], [431], [2025], [14786], [2496], [4773], [8922], [3958], [1626], [6573], [5028], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P14831P2 : CertificateIrreducibleZModOfList' 14831 3 2 13 [13222, 10671, 4942, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [170, 678, 12735], [9719, 14152, 2096], [0, 1]]
 g := ![![[7623, 12207, 3972], [10059, 298, 2480], [9625, 5337, 10588], [4506, 5238, 4262], [2460, 11444], [7737, 3251, 11329], [14754, 5237, 10374], [11333, 7383, 12114], [10500, 10804, 4783], [10936, 14704], [14411, 5526], [10579, 13322, 11538], [1]], ![[13794, 11673, 14765, 12777], [7414, 498, 12656, 1597], [9662, 10710, 4259, 12775], [11966, 5628, 805, 5002], [3881, 10384], [7587, 3226, 11194, 6685], [13727, 8973, 8857, 5749], [10548, 1868, 10201, 10406], [2595, 13934, 512, 5069], [1925, 3427], [8638, 4842], [5024, 13995, 13774, 14686], [10461, 10737, 2849, 1558]], ![[1330, 14210, 5056, 536], [3930, 14465, 10575, 3517], [10515, 13433, 6833, 14086], [4551, 2145, 1496, 11019], [14300, 2348], [11681, 10434, 1881, 11106], [437, 11080, 11847, 354], [1524, 11310, 10068, 3638], [3622, 5358, 10820, 10433], [1031, 997], [301, 10035], [13637, 6079, 902, 6003], [3279, 9085, 2262, 13273]]]
 h' := ![![[170, 678, 12735], [4310, 8608, 6426], [3061, 8672, 6872], [12626, 6921, 5376], [7947, 2766, 11181], [5624, 11517, 12393], [9586, 3970, 1450], [7498, 1351, 10891], [1991, 3840, 13549], [7731, 3605, 6674], [2923, 250, 487], [10454, 2822, 14309], [1609, 4160, 9889], [0, 1]], ![[9719, 14152, 2096], [13444, 11666, 4019], [1090, 12363, 11971], [215, 5235, 11255], [14570, 7490, 2958], [6421, 7767, 14397], [8863, 3052, 8198], [3614, 7042, 6705], [644, 5321, 42], [2889, 4228, 14370], [9479, 541, 5525], [8479, 11713, 1151], [2503, 8671, 5080], [170, 678, 12735]], ![[0, 1], [6163, 9388, 4386], [13743, 8627, 10819], [9980, 2675, 13031], [3331, 4575, 692], [3771, 10378, 2872], [4280, 7809, 5183], [1695, 6438, 12066], [1778, 5670, 1240], [11170, 6998, 8618], [7705, 14040, 8819], [8238, 296, 14202], [11083, 2000, 14693], [9719, 14152, 2096]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2604, 4630], []]
 b := ![[], [8332, 556, 4460], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A14831 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 14831 3 where
 D := ![[10291, 1], [14429, 1], [13222, 10671, 4942, 1]]; D' := ![[10291, 1], [14429, 1], [13222, 10671, 4942, 1]]
 heqm := by decide
 hProd := by decide
 s := ![13, 13, 13]
 n := ![1, 1, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P14831P0
  | 1 => exact P14831P1
  | 2 => exact P14831P2

def C148310 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A14831.D 0) 14831 where
  n := 1
  w := ![![14831, 0, 0, 0, 0], ![10291, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C148311 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A14831.D 1) 14831 where
  n := 1
  w := ![![14831, 0, 0, 0, 0], ![14429, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C148312 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A14831.D 2) 14831 where
  n := 3
  w := ![![14831, 0, 0, 0, 0], ![13222, 10672, 4942, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K14831 : KummerData 14831 ![I14831N0, I14831N1, I14831N2] ![14831, 14831, 3262205418191] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A14831
  C := by
    intro i
    match i with
    | 0 => exact C148310
    | 1 => exact C148311
    | 2 => exact C148312
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 14831 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp14843 : Fact (Nat.Prime 14843) := {out := by norm_num}

def I14843N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14843, 0, 0, 0, 0], ![1729, 1, 0, 0, 0]] i)))

def I14843N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14843, 0, 0, 0, 0], ![2250, 1, 0, 0, 0]] i)))

def I14843N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14843, 0, 0, 0, 0], ![13253, 1, 0, 0, 0]] i)))

def I14843N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14843, 0, 0, 0, 0], ![9717, 12454, 1, 0, 0]] i)))

def P14843P0 : CertificateIrreducibleZModOfList' 14843 1 2 13 [1729, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [4610], [], [7056], [1322], [8947], [4983], [10146], [508], [], [], [11254], [5998, 13114, 1]]]
 h' := ![![[0, 1], [1], [12072], [1122], [84], [11886], [8176], [1992], [12248], [1753], [4725], [1007], [4715], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P14843P1 : CertificateIrreducibleZModOfList' 14843 1 2 13 [2250, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [10179], [], [12445], [1655], [11839], [2735], [1047], [5944], [], [], [3063], [1037, 12593, 1]]]
 h' := ![![[0, 1], [14842], [8541], [7491], [1843], [5435], [6095], [4287], [14386], [2498], [5172], [10245], [11944], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P14843P2 : CertificateIrreducibleZModOfList' 14843 1 2 13 [13253, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [6600], [], [10737], [13745], [13486], [14697], [10279], [5443], [], [], [6298], [4790, 1590, 1]]]
 h' := ![![[0, 1], [14842], [9217], [2380], [5654], [9448], [5348], [1467], [901], [793], [3550], [9638], [1641], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P14843P3 : CertificateIrreducibleZModOfList' 14843 2 2 13 [9717, 12454, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2389, 14842], [0, 1]]
 g := ![![[7532, 6825], [7851, 4700], [14414], [225, 8638], [9013, 10466], [5361, 3371], [6057, 798], [8031, 558], [8822, 3882], [10920], [8981], [5292, 5607], [2389, 1]], ![[0, 8018], [0, 10143], [14414], [4637, 6205], [1832, 4377], [13774, 11472], [12575, 14045], [5223, 14285], [6045, 10961], [10920], [8981], [12029, 9236], [4778, 14842]]]
 h' := ![![[2389, 14842], [4853, 2011], [7968, 8434], [10439, 14633], [9222, 3284], [6093, 14552], [11469, 4866], [7267, 11482], [9794, 6953], [3942, 5866], [5607, 7273], [8631, 10290], [539, 12735], [0, 1]], ![[0, 1], [0, 12832], [0, 6409], [13411, 210], [2751, 11559], [8515, 291], [14274, 9977], [7901, 3361], [11194, 7890], [6024, 8977], [14494, 7570], [11433, 4553], [11147, 2108], [2389, 14842]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13588]]
 b := ![[], [3688, 6794]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A14843 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 14843 4 where
 D := ![[1729, 1], [2250, 1], [13253, 1], [9717, 12454, 1]]; D' := ![[1729, 1], [2250, 1], [13253, 1], [9717, 12454, 1]]
 heqm := by decide
 hProd := by decide
 s := ![13, 13, 13, 13]
 n := ![1, 1, 1, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P14843P0
  | 1 => exact P14843P1
  | 2 => exact P14843P2
  | 3 => exact P14843P3

def C148430 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A14843.D 0) 14843 where
  n := 1
  w := ![![14843, 0, 0, 0, 0], ![1729, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C148431 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A14843.D 1) 14843 where
  n := 1
  w := ![![14843, 0, 0, 0, 0], ![2250, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C148432 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A14843.D 2) 14843 where
  n := 1
  w := ![![14843, 0, 0, 0, 0], ![13253, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C148433 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A14843.D 3) 14843 where
  n := 2
  w := ![![14843, 0, 0, 0, 0], ![9717, 12454, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K14843 : KummerData 14843 ![I14843N0, I14843N1, I14843N2, I14843N3] ![14843, 14843, 14843, 220314649] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A14843
  C := by
    intro i
    match i with
    | 0 => exact C148430
    | 1 => exact C148431
    | 2 => exact C148432
    | 3 => exact C148433
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 14843 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp14851 : Fact (Nat.Prime 14851) := {out := by norm_num}

def I14851N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14851, 0, 0, 0, 0], ![1816, 1, 0, 0, 0]] i)))

def I14851N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14851, 0, 0, 0, 0], ![4274, 2793, 1, 0, 0]] i)))

def I14851N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14851, 0, 0, 0, 0], ![8631, 10242, 1, 0, 0]] i)))

def P14851P0 : CertificateIrreducibleZModOfList' 14851 1 2 13 [1816, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [12782], [], [], [], [], [], [], [], [198], [], [10091], [934, 13035, 1]]]
 h' := ![![[0, 1], [1], [3686], [14391], [2149], [7185], [603], [5652], [8821], [11707], [13483], [878], [11721], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P14851P1 : CertificateIrreducibleZModOfList' 14851 2 2 13 [4274, 2793, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12058, 14850], [0, 1]]
 g := ![![[3597, 824], [14340, 11070], [5412], [8008], [7778], [7767], [749], [8357], [1450], [521, 14233], [10081], [14495, 10298], [12058, 1]], ![[4070, 14027], [761, 3781], [5412], [8008], [7778], [7767], [749], [8357], [1450], [3879, 618], [10081], [3717, 4553], [9265, 14850]]]
 h' := ![![[12058, 14850], [917, 5751], [10844, 14690], [5958, 9119], [12558, 4606], [4057, 6236], [7870, 11930], [8720, 7719], [11280, 7947], [896, 1013], [7061, 12614], [6742, 2762], [11929, 14651], [0, 1]], ![[0, 1], [7156, 9100], [136, 161], [6056, 5732], [8966, 10245], [7132, 8615], [13024, 2921], [13205, 7132], [2703, 6904], [8128, 13838], [2731, 2237], [145, 12089], [6191, 200], [12058, 14850]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9833]]
 b := ![[], [8443, 12342]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P14851P2 : CertificateIrreducibleZModOfList' 14851 2 2 13 [8631, 10242, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4609, 14850], [0, 1]]
 g := ![![[7357, 4706], [11823, 14204], [671], [951], [1227], [7687], [9500], [13692], [12140], [14383, 4088], [13513], [14050, 9367], [4609, 1]], ![[0, 10145], [0, 647], [671], [951], [1227], [7687], [9500], [13692], [12140], [10056, 10763], [13513], [14696, 5484], [9218, 14850]]]
 h' := ![![[4609, 14850], [11759, 281], [3830, 3869], [2750, 8268], [12215, 8399], [117, 9632], [12973, 2578], [13262, 11674], [5510, 14508], [14687, 3924], [8048, 5860], [7716, 9883], [5550, 12171], [0, 1]], ![[0, 1], [0, 14570], [0, 10982], [2296, 6583], [6649, 6452], [4366, 5219], [14175, 12273], [13555, 3177], [13680, 343], [11885, 10927], [2819, 8991], [10446, 4968], [9462, 2680], [4609, 14850]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [171]]
 b := ![[], [14592, 7511]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A14851 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 14851 3 where
 D := ![[1816, 1], [4274, 2793, 1], [8631, 10242, 1]]; D' := ![[1816, 1], [4274, 2793, 1], [8631, 10242, 1]]
 heqm := by decide
 hProd := by decide
 s := ![13, 13, 13]
 n := ![1, 2, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P14851P0
  | 1 => exact P14851P1
  | 2 => exact P14851P2

def C148510 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A14851.D 0) 14851 where
  n := 1
  w := ![![14851, 0, 0, 0, 0], ![1816, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C148511 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A14851.D 1) 14851 where
  n := 2
  w := ![![14851, 0, 0, 0, 0], ![4274, 2793, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C148512 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A14851.D 2) 14851 where
  n := 2
  w := ![![14851, 0, 0, 0, 0], ![8631, 10242, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K14851 : KummerData 14851 ![I14851N0, I14851N1, I14851N2] ![14851, 220552201, 220552201] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A14851
  C := by
    intro i
    match i with
    | 0 => exact C148510
    | 1 => exact C148511
    | 2 => exact C148512
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 14851 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp14867 : Fact (Nat.Prime 14867) := {out := by norm_num}

def I14867N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14867, 0, 0, 0, 0], ![13493, 2311, 1, 0, 0]] i)))

def I14867N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14867, 0, 0, 0, 0], ![11113, 4843, 12556, 2, 0]] i)))

def P14867P0 : CertificateIrreducibleZModOfList' 14867 2 2 13 [13493, 2311, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12556, 14866], [0, 1]]
 g := ![![[10310, 12911], [13483, 12781], [6262], [13974], [12222, 1938], [9421], [6788], [6200], [219], [1180, 7814], [7069], [261, 14572], [12556, 1]], ![[11058, 1956], [2454, 2086], [6262], [13974], [8471, 12929], [9421], [6788], [6200], [219], [6431, 7053], [7069], [12991, 295], [10245, 14866]]]
 h' := ![![[12556, 14866], [1360, 4562], [4593, 1278], [10502, 6244], [8185, 6574], [2826, 1489], [6741, 8968], [13716, 4884], [2040, 2449], [817, 1767], [10418, 13880], [1806, 12096], [6224, 4842], [0, 1]], ![[0, 1], [14148, 10305], [9668, 13589], [1608, 8623], [9745, 8293], [10891, 13378], [6291, 5899], [10845, 9983], [6728, 12418], [5705, 13100], [1857, 987], [12777, 2771], [11213, 10025], [12556, 14866]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2919]]
 b := ![[], [10198, 8893]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P14867P1 : CertificateIrreducibleZModOfList' 14867 3 2 13 [11113, 4842, 12556, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3942, 14147, 12532], [13236, 719, 2335], [0, 1]]
 g := ![![[8587, 8429, 12627], [13746, 14223, 14489], [13194, 2121], [5273, 11882], [9844, 11528, 6319], [787, 3048], [7005, 770], [6764, 9183], [8196, 11092], [4612, 2767, 1107], [12474, 925], [8620, 11213, 3468], [1]], ![[10364, 6199, 5433, 5462], [10257, 10893, 10361, 14064], [4865, 9319], [2671, 12413], [9886, 12307, 2442, 6755], [5984, 3676], [1822, 4747], [6742, 4738], [3733, 2822], [11973, 13125, 3421, 4595], [13544, 629], [9789, 7435, 10061, 6478], [9354, 4244, 125, 8666]], ![[6478, 5153, 653, 2374], [1627, 13583, 4804, 10091], [9100, 3173], [1536, 5306], [9645, 6887, 3851, 5178], [7766, 11488], [12527, 13200], [10781, 10882], [3554, 9576], [4279, 12956, 2203, 2849], [8396, 1015], [9338, 4293, 9562, 10382], [10457, 10254, 11767, 6201]]]
 h' := ![![[3942, 14147, 12532], [13994, 7954, 6409], [11938, 2476, 13320], [9437, 8143, 1364], [9881, 1153, 14663], [4908, 11218, 10590], [12253, 13060, 10057], [8028, 6113, 8828], [10898, 8646, 3188], [8260, 3185, 687], [4519, 2977, 2702], [8888, 12221, 6304], [3754, 10025, 2311], [0, 1]], ![[13236, 719, 2335], [3860, 12034, 10461], [5659, 8949, 4535], [9003, 9496, 482], [7137, 6012, 666], [1309, 3795, 3930], [5054, 6095, 2738], [6481, 12860, 12455], [11046, 3260, 3630], [10085, 10363, 14734], [5107, 1641, 1622], [3679, 12130, 6746], [13791, 8622, 3655], [3942, 14147, 12532]], ![[0, 1], [5692, 9746, 12864], [13661, 3442, 11879], [2288, 12095, 13021], [5517, 7702, 14405], [8893, 14721, 347], [7658, 10579, 2072], [12317, 10761, 8451], [11511, 2961, 8049], [4242, 1319, 14313], [4435, 10249, 10543], [13276, 5383, 1817], [9919, 11087, 8901], [13236, 719, 2335]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5291, 11659], []]
 b := ![[], [1271, 12632, 4290], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A14867 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 14867 2 where
 D := ![[13493, 2311, 1], [11113, 4842, 12556, 1]]; D' := ![[13493, 2311, 1], [11113, 4842, 12556, 1]]
 heqm := by decide
 hProd := by decide
 s := ![13, 13]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P14867P0
  | 1 => exact P14867P1

def C148670 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A14867.D 0) 14867 where
  n := 2
  w := ![![14867, 0, 0, 0, 0], ![13493, 2311, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C148671 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A14867.D 1) 14867 where
  n := 3
  w := ![![14867, 0, 0, 0, 0], ![11113, 4843, 12556, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K14867 : KummerData 14867 ![I14867N0, I14867N1] ![221027689, 3286018652363] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A14867
  C := by
    intro i
    match i with
    | 0 => exact C148670
    | 1 => exact C148671
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 14867 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp14869 : Fact (Nat.Prime 14869) := {out := by norm_num}

def I14869N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14869, 0, 0, 0, 0], ![2124, 1, 0, 0, 0]] i)))

def I14869N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14869, 0, 0, 0, 0], ![3061, 1, 0, 0, 0]] i)))

def I14869N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14869, 0, 0, 0, 0], ![3259, 1, 0, 0, 0]] i)))

def I14869N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14869, 0, 0, 0, 0], ![9408, 1, 0, 0, 0]] i)))

def I14869N4 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14869, 0, 0, 0, 0], ![11886, 1, 0, 0, 0]] i)))

def P14869P0 : CertificateIrreducibleZModOfList' 14869 1 2 13 [2124, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [14862], [], [4459], [], [], [], [], [5688], [], [8239], [6069, 12745, 1]]]
 h' := ![![[0, 1], [1], [14868], [4306], [637], [13790], [1503], [11978], [13926], [7185], [2512], [1177], [867], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P14869P1 : CertificateIrreducibleZModOfList' 14869 1 2 13 [3061, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [11561], [], [1500], [], [], [], [], [14796], [], [2648], [2251, 11808, 1]]]
 h' := ![![[0, 1], [1], [14868], [11744], [3021], [1220], [5905], [10398], [11165], [418], [10417], [12946], [8905], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P14869P2 : CertificateIrreducibleZModOfList' 14869 1 2 13 [3259, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [4932], [], [13878], [], [], [], [], [5325], [], [6910], [4615, 11610, 1]]]
 h' := ![![[0, 1], [1], [1], [9580], [3096], [13894], [5280], [9587], [2777], [12817], [1806], [6845], [7143], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P14869P3 : CertificateIrreducibleZModOfList' 14869 1 2 13 [9408, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [2524], [], [12414], [], [], [], [], [2949], [], [1021], [10176, 5461, 1]]]
 h' := ![![[0, 1], [1], [1], [9436], [5083], [4278], [9495], [6483], [11288], [1362], [7898], [14675], [5683], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P14869P4 : CertificateIrreducibleZModOfList' 14869 1 2 13 [11886, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [], [10667], [], [9281], [], [], [], [], [11576], [], [11182], [6627, 2983, 1]]]
 h' := ![![[0, 1], [1], [1], [2444], [14014], [11802], [7460], [7095], [12943], [5390], [5931], [4739], [7440], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A14869 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 14869 5 where
 D := ![[2124, 1], [3061, 1], [3259, 1], [9408, 1], [11886, 1]]; D' := ![[2124, 1], [3061, 1], [3259, 1], [9408, 1], [11886, 1]]
 heqm := by decide
 hProd := by decide
 s := ![13, 13, 13, 13, 13]
 n := ![1, 1, 1, 1, 1]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P14869P0
  | 1 => exact P14869P1
  | 2 => exact P14869P2
  | 3 => exact P14869P3
  | 4 => exact P14869P4

def C148690 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A14869.D 0) 14869 where
  n := 1
  w := ![![14869, 0, 0, 0, 0], ![2124, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C148691 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A14869.D 1) 14869 where
  n := 1
  w := ![![14869, 0, 0, 0, 0], ![3061, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C148692 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A14869.D 2) 14869 where
  n := 1
  w := ![![14869, 0, 0, 0, 0], ![3259, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C148693 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A14869.D 3) 14869 where
  n := 1
  w := ![![14869, 0, 0, 0, 0], ![9408, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C148694 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A14869.D 4) 14869 where
  n := 1
  w := ![![14869, 0, 0, 0, 0], ![11886, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K14869 : KummerData 14869 ![I14869N0, I14869N1, I14869N2, I14869N3, I14869N4] ![14869, 14869, 14869, 14869, 14869] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A14869
  C := by
    intro i
    match i with
    | 0 => exact C148690
    | 1 => exact C148691
    | 2 => exact C148692
    | 3 => exact C148693
    | 4 => exact C148694
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 14869 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp14879 : Fact (Nat.Prime 14879) := {out := by norm_num}

def I14879N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14879, 0, 0, 0, 0], ![14738, 1, 0, 0, 0]] i)))

def I14879N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14879, 0, 0, 0, 0], ![14846, 2812, 1, 0, 0]] i)))

def I14879N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14879, 0, 0, 0, 0], ![1992, 12208, 1, 0, 0]] i)))

def P14879P0 : CertificateIrreducibleZModOfList' 14879 1 2 13 [14738, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [10658], [640], [5507], [10884], [], [], [], [], [13580], [], [8635], [5002, 141, 1]]]
 h' := ![![[0, 1], [14878], [966], [2779], [2107], [6460], [4103], [12619], [14109], [10268], [9363], [12336], [5969], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P14879P1 : CertificateIrreducibleZModOfList' 14879 2 2 13 [14846, 2812, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12067, 14878], [0, 1]]
 g := ![![[10285, 11981], [13070, 4425], [4240, 1520], [13229, 784], [2109, 7961], [11126], [14463], [10632], [10150], [11180, 10619], [9637], [5686, 7576], [12067, 1]], ![[5769, 2898], [8814, 10454], [273, 13359], [10713, 14095], [8672, 6918], [11126], [14463], [10632], [10150], [12705, 4260], [9637], [8702, 7303], [9255, 14878]]]
 h' := ![![[12067, 14878], [14698, 7152], [6009, 13682], [5066, 11536], [10081, 14851], [5860, 9478], [435, 12371], [11944, 12620], [8736, 6491], [11844, 9438], [10575, 14285], [9090, 13235], [11357, 6628], [0, 1]], ![[0, 1], [4803, 7727], [9319, 1197], [2054, 3343], [14422, 28], [2013, 5401], [285, 2508], [10919, 2259], [12577, 8388], [1445, 5441], [14455, 594], [4649, 1644], [1929, 8251], [12067, 14878]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6505]]
 b := ![[], [5162, 10692]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P14879P2 : CertificateIrreducibleZModOfList' 14879 2 2 13 [1992, 12208, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2671, 14878], [0, 1]]
 g := ![![[4428, 366], [5474, 5360], [7386, 12526], [726, 9074], [2056, 8196], [10569], [1426], [5603], [13934], [2208, 9669], [13380], [4525, 13726], [2671, 1]], ![[0, 14513], [8436, 9519], [1461, 2353], [14368, 5805], [6563, 6683], [10569], [1426], [5603], [13934], [13042, 5210], [13380], [4815, 1153], [5342, 14878]]]
 h' := ![![[2671, 14878], [2099, 5113], [2419, 7480], [11950, 12446], [11052, 3147], [3026, 5696], [10024, 12611], [13914, 3239], [14848, 12384], [5848, 4490], [12239, 8078], [2874, 10097], [6050, 5208], [0, 1]], ![[0, 1], [0, 9766], [13881, 7399], [651, 2433], [10054, 11732], [10704, 9183], [7949, 2268], [5705, 11640], [1616, 2495], [6164, 10389], [14027, 6801], [11213, 4782], [4753, 9671], [2671, 14878]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7517]]
 b := ![[], [13345, 11198]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A14879 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 14879 3 where
 D := ![[14738, 1], [14846, 2812, 1], [1992, 12208, 1]]; D' := ![[14738, 1], [14846, 2812, 1], [1992, 12208, 1]]
 heqm := by decide
 hProd := by decide
 s := ![13, 13, 13]
 n := ![1, 2, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P14879P0
  | 1 => exact P14879P1
  | 2 => exact P14879P2

def C148790 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A14879.D 0) 14879 where
  n := 1
  w := ![![14879, 0, 0, 0, 0], ![14738, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C148791 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A14879.D 1) 14879 where
  n := 2
  w := ![![14879, 0, 0, 0, 0], ![14846, 2812, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C148792 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A14879.D 2) 14879 where
  n := 2
  w := ![![14879, 0, 0, 0, 0], ![1992, 12208, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K14879 : KummerData 14879 ![I14879N0, I14879N1, I14879N2] ![14879, 221384641, 221384641] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A14879
  C := by
    intro i
    match i with
    | 0 => exact C148790
    | 1 => exact C148791
    | 2 => exact C148792
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 14879 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp14887 : Fact (Nat.Prime 14887) := {out := by norm_num}

def I14887N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14887, 0, 0, 0, 0], ![14853, 1, 0, 0, 0]] i)))

def I14887N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14887, 0, 0, 0, 0], ![8116, 11566, 12051, -2970, 22728]] i)))

def P14887P0 : CertificateIrreducibleZModOfList' 14887 1 2 13 [14853, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [11822], [6809], [], [], [8690], [], [], [], [3547], [], [10200], [1156, 34, 1]]]
 h' := ![![[0, 1], [14886], [8201], [9589], [2837], [12607], [7015], [5412], [8067], [1502], [12988], [4399], [9530], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P14887P1 : CertificateIrreducibleZModOfList' 14887 4 2 13 [7468, 9430, 1156, 34, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [14489, 3103, 12830, 4446], [2362, 11341, 6724, 11388], [12889, 442, 10220, 13940], [0, 1]]
 g := ![![[10346, 13454, 1837, 13137], [14385, 6002, 9453, 11505], [3629, 3389, 7559, 14326], [7282, 8732, 11585], [9885, 12622, 9079], [11328, 8748, 13503, 2602], [13408, 2371, 2461], [790, 14322, 5233], [9267, 5654, 2374], [9359, 13111, 3679, 3766], [8596, 4850, 3340], [100, 0, 14853, 1], []], ![[5809, 12957, 7764, 11177, 3199, 11646], [2812, 4092, 2194, 10075, 617, 3248], [5196, 11794, 10230, 1235, 12537, 8386], [3848, 7845, 2854], [1208, 4169, 2808], [10005, 11743, 9739, 12553, 4421, 10320], [9496, 4543, 13493], [4318, 5020, 3081], [2332, 9608, 14016], [13419, 2178, 9485, 1824, 10124, 10838], [13972, 581, 6878], [6242, 9771, 2972, 5853, 11478, 10983], [8733, 14012, 11275, 10931, 3321, 1154]], ![[12555, 10196, 9086, 13647, 10033, 6931], [5457, 8875, 7469, 13182, 2148, 5318], [7399, 7191, 9330, 5666, 14734, 7658], [1009, 3205, 8560], [8377, 9571, 5240], [14866, 13467, 9632, 11914, 12423, 12591], [5439, 3719, 3482], [9701, 11787, 2296], [9778, 10156, 3749], [4788, 14696, 4661, 1925, 9710, 6907], [56, 11594, 3799], [4167, 7438, 11710, 333, 1917, 131], [5407, 10943, 2217, 13214, 7779, 4995]], ![[3815, 14656, 8433, 4293, 14759, 3660], [12045, 3716, 13125, 9487, 4519, 13190], [1719, 5231, 9520, 11740, 11858, 1286], [6875, 5598, 9013], [6746, 3106, 2387], [3521, 3488, 9367, 12683, 4216, 12244], [7078, 3989, 3087], [3184, 7684, 534], [2491, 1531, 2258], [3759, 7069, 602, 4339, 9522, 2013], [3722, 7534, 6424], [2983, 5985, 14219, 11329, 4193, 144], [8335, 8706, 13929, 11388, 14651, 10340]]]
 h' := ![![[14489, 3103, 12830, 4446], [12299, 10912, 6408, 2515], [7855, 11566, 10158, 13757], [8544, 6413, 13619, 210], [3529, 5194, 9424, 3394], [5317, 8094, 13598, 9519], [7191, 10595, 12558, 10950], [12869, 10777, 1919, 2501], [962, 8068, 3507, 12741], [1453, 10066, 2925, 6733], [855, 13098, 2425, 3775], [12437, 9768, 4329, 12012], [0, 0, 0, 1], [0, 1]], ![[2362, 11341, 6724, 11388], [13348, 7050, 7130, 11865], [1243, 13144, 4269, 11273], [12357, 115, 14289, 10567], [4844, 6423, 6736, 11846], [10644, 9575, 1196, 10653], [12933, 7272, 14155, 6597], [376, 10504, 125, 960], [9089, 3900, 3420, 12374], [10245, 5482, 2566, 3889], [6015, 14185, 2711, 2660], [5468, 2009, 14490, 14423], [3556, 12400, 1211, 14718], [14489, 3103, 12830, 4446]], ![[12889, 442, 10220, 13940], [6843, 7843, 5220, 5834], [11949, 12617, 3147, 2675], [14090, 4631, 8805, 3938], [7763, 13541, 1759, 6867], [2763, 12100, 11439, 13109], [3520, 944, 2271, 5424], [9969, 2735, 983, 9853], [348, 579, 6523, 3210], [7557, 13478, 14771, 8262], [7204, 7853, 13403, 77], [8641, 11792, 13884, 11032], [6449, 6116, 2098, 7812], [2362, 11341, 6724, 11388]], ![[0, 1], [4447, 3969, 11016, 9560], [1499, 7334, 12200, 2069], [8340, 3728, 7948, 172], [13683, 4616, 11855, 7667], [14289, 5, 3541, 11380], [14185, 10963, 790, 6803], [9551, 5758, 11860, 1573], [5032, 2340, 1437, 1449], [7285, 748, 9512, 10890], [8184, 9525, 11235, 8375], [9041, 6205, 11958, 7194], [10539, 11258, 11578, 7243], [12889, 442, 10220, 13940]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [4971, 5790, 5865], []]
 b := ![[], [], [4395, 1190, 12408, 5337], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A14887 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 14887 2 where
 D := ![[14853, 1], [7468, 9430, 1156, 34, 1]]; D' := ![[14853, 1], [7468, 9430, 1156, 34, 1]]
 heqm := by decide
 hProd := by decide
 s := ![13, 13]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P14887P0
  | 1 => exact P14887P1

def C148870 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A14887.D 0) 14887 where
  n := 1
  w := ![![14887, 0, 0, 0, 0], ![14853, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C148871 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A14887.D 1) 14887 where
  n := 4
  w := ![![14887, 0, 0, 0, 0], ![8116, 11566, 12051, -2970, 22728]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K14887 : KummerData 14887 ![I14887N0, I14887N1] ![14887, 49116651739227361] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A14887
  C := by
    intro i
    match i with
    | 0 => exact C148870
    | 1 => exact C148871
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 14887 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp14891 : Fact (Nat.Prime 14891) := {out := by norm_num}

def I14891N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14891, 0, 0, 0, 0], ![5427, 1, 0, 0, 0]] i)))

def I14891N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14891, 0, 0, 0, 0], ![9723, 1, 0, 0, 0]] i)))

def I14891N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14891, 0, 0, 0, 0], ![5037, 14501, 14632, 2, 0]] i)))

def P14891P0 : CertificateIrreducibleZModOfList' 14891 1 2 13 [5427, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [5710], [], [9372], [], [8797], [], [], [], [11193], [], [4253], [12822, 9464, 1]]]
 h' := ![![[0, 1], [1], [6556], [5812], [1889], [14118], [433], [12820], [4858], [10869], [361], [19], [649], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P14891P1 : CertificateIrreducibleZModOfList' 14891 1 2 13 [9723, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [11563], [], [5475], [], [12337], [], [], [], [2263], [], [9390], [8661, 5168, 1]]]
 h' := ![![[0, 1], [1], [6378], [1900], [10576], [9245], [13232], [6933], [7872], [5749], [9952], [12642], [12593], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P14891P2 : CertificateIrreducibleZModOfList' 14891 3 2 13 [5037, 14500, 14632, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9985, 7866, 3327], [5165, 7024, 11564], [0, 1]]
 g := ![![[1556, 8197, 107], [7489, 12086, 13482], [5763, 12420], [5990, 4897, 11537], [5173, 5262], [12213, 12410, 12637], [10663, 13385], [11340, 11385], [3588, 2878], [8517, 9120, 10106], [8585, 11237], [11534, 5137, 7517], [1]], ![[7752, 4645, 4140, 3137], [2960, 14278, 5577, 12275], [10337, 5498], [5060, 9527, 6065, 1499], [9703, 3551], [71, 9390, 10633, 13199], [788, 3958], [1224, 4553], [13319, 6103], [14227, 3883, 5369, 12388], [296, 12509], [536, 7288, 10333, 13991], [14615, 5287, 2223, 5214]], ![[6621, 4127, 3257, 11496], [1962, 13632, 1405, 13559], [11464, 4328], [11310, 3996, 3331, 9779], [3031, 13519], [12856, 5971, 6050, 2452], [14348, 504], [13570, 12151], [7659, 14331], [5847, 4734, 207, 10409], [2369, 6824], [6872, 8091, 788, 7347], [1656, 4126, 12811, 9677]]]
 h' := ![![[9985, 7866, 3327], [11701, 8988, 10135], [4987, 13233, 14683], [12427, 862, 5177], [7566, 9025, 10350], [12731, 2314, 9176], [8317, 6962, 4188], [12960, 8120, 14029], [14005, 6161, 11490], [842, 2606, 3349], [10139, 1280, 4065], [7924, 415, 4362], [9854, 391, 259], [0, 1]], ![[5165, 7024, 11564], [9010, 5397, 11208], [13028, 5341, 6721], [9535, 6566, 8228], [6038, 5112, 6457], [7018, 11221, 4007], [3280, 7300, 13856], [6192, 14127, 8915], [14516, 11617, 4171], [6900, 8661, 14087], [6844, 5799, 6247], [2212, 9909, 3743], [9600, 3969, 7854], [9985, 7866, 3327]], ![[0, 1], [10394, 506, 8439], [527, 11208, 8378], [3709, 7463, 1486], [12044, 754, 12975], [6289, 1356, 1708], [428, 629, 11738], [2228, 7535, 6838], [9402, 12004, 14121], [6388, 3624, 12346], [9781, 7812, 4579], [2210, 4567, 6786], [12277, 10531, 6778], [5165, 7024, 11564]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [214, 13866], []]
 b := ![[], [12467, 13502, 3017], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A14891 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 14891 3 where
 D := ![[5427, 1], [9723, 1], [5037, 14500, 14632, 1]]; D' := ![[5427, 1], [9723, 1], [5037, 14500, 14632, 1]]
 heqm := by decide
 hProd := by decide
 s := ![13, 13, 13]
 n := ![1, 1, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P14891P0
  | 1 => exact P14891P1
  | 2 => exact P14891P2

def C148910 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A14891.D 0) 14891 where
  n := 1
  w := ![![14891, 0, 0, 0, 0], ![5427, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C148911 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A14891.D 1) 14891 where
  n := 1
  w := ![![14891, 0, 0, 0, 0], ![9723, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C148912 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A14891.D 2) 14891 where
  n := 3
  w := ![![14891, 0, 0, 0, 0], ![5037, 14501, 14632, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K14891 : KummerData 14891 ![I14891N0, I14891N1, I14891N2] ![14891, 14891, 3301958349971] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A14891
  C := by
    intro i
    match i with
    | 0 => exact C148910
    | 1 => exact C148911
    | 2 => exact C148912
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 14891 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp14897 : Fact (Nat.Prime 14897) := {out := by norm_num}

def I14897N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14897, 0, 0, 0, 0], ![4121, 7309, 1, 0, 0]] i)))

def I14897N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14897, 0, 0, 0, 0], ![2523, 11616, 7588, 2, 0]] i)))

def P14897P0 : CertificateIrreducibleZModOfList' 14897 2 2 13 [4121, 7309, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [7588, 14896], [0, 1]]
 g := ![![[4618, 4466], [13265], [5194], [4118], [3858, 1754], [10715, 6541], [9328], [10751], [6540], [9289, 9385], [13674], [6558, 993], [7588, 1]], ![[1951, 10431], [13265], [5194], [4118], [10189, 13143], [7019, 8356], [9328], [10751], [6540], [112, 5512], [13674], [3560, 13904], [279, 14896]]]
 h' := ![![[7588, 14896], [5390, 7539], [7856, 6156], [3950, 9396], [11178, 1516], [13090, 8051], [8754, 12278], [7311, 12867], [6074, 2023], [5321, 3729], [2919, 4040], [12537, 2237], [13552, 11615], [0, 1]], ![[0, 1], [6842, 7358], [2592, 8741], [3756, 5501], [14102, 13381], [11481, 6846], [8380, 2619], [7169, 2030], [12688, 12874], [11570, 11168], [413, 10857], [4313, 12660], [2623, 3282], [7588, 14896]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7568]]
 b := ![[], [4212, 3784]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P14897P1 : CertificateIrreducibleZModOfList' 14897 3 2 13 [2523, 11615, 7588, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8545, 12705, 7287], [13661, 2191, 7610], [0, 1]]
 g := ![![[8812, 12792, 1546], [7811, 8895], [3269, 3280], [2719, 7551], [10775, 492, 5147], [371, 3964, 12875], [8119, 5491], [14839, 64], [8197, 13532], [10885, 7571, 501], [2443, 2192], [1472, 2623, 839], [1]], ![[8970, 9481, 758, 11630], [7312, 12344], [2588, 12194], [8330, 9014], [195, 9291, 10954, 4786], [4330, 1829, 2995, 5998], [5155, 2760], [8287, 6875], [2183, 10264], [13381, 14889, 10632, 2378], [10189, 14246], [606, 3604, 13737, 10425], [4988, 13271, 11341, 9154]], ![[9911, 1092, 12544, 9742], [5776, 4041], [8274, 6909], [709, 5905], [13303, 14890, 683, 5662], [9512, 6570, 5794, 13826], [4431, 11176], [11784, 1951], [6179, 11926], [7434, 7185, 5837, 5966], [13139, 12882], [13321, 535, 6359, 8226], [12489, 885, 10967, 5743]]]
 h' := ![![[8545, 12705, 7287], [2447, 12832, 12847], [1709, 9839, 512], [7462, 3293, 882], [1700, 11024, 7867], [2478, 13491, 11794], [3878, 13080, 2737], [4136, 13217, 9814], [3050, 9865, 8], [7213, 11621, 11495], [5861, 4321, 12840], [10394, 5425, 4503], [12374, 3282, 7309], [0, 1]], ![[13661, 2191, 7610], [10138, 6692, 5659], [2093, 8812, 2049], [4376, 10590, 7773], [5438, 7046, 8032], [5775, 1571, 12870], [1810, 4746, 11127], [12800, 10535, 9277], [9298, 9236, 10861], [12545, 874, 2397], [34, 9247, 1773], [1940, 3907, 14493], [11849, 3166, 5993], [8545, 12705, 7287]], ![[0, 1], [11122, 10270, 11288], [13255, 11143, 12336], [10093, 1014, 6242], [1533, 11724, 13895], [1322, 14732, 5130], [811, 11968, 1033], [6750, 6042, 10703], [13140, 10693, 4028], [2897, 2402, 1005], [9000, 1329, 284], [10582, 5565, 10798], [4593, 8449, 1595], [13661, 2191, 7610]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1983, 350], []]
 b := ![[], [8208, 943, 4522], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A14897 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 14897 2 where
 D := ![[4121, 7309, 1], [2523, 11615, 7588, 1]]; D' := ![[4121, 7309, 1], [2523, 11615, 7588, 1]]
 heqm := by decide
 hProd := by decide
 s := ![13, 13]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P14897P0
  | 1 => exact P14897P1

def C148970 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A14897.D 0) 14897 where
  n := 2
  w := ![![14897, 0, 0, 0, 0], ![4121, 7309, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C148971 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A14897.D 1) 14897 where
  n := 3
  w := ![![14897, 0, 0, 0, 0], ![2523, 11616, 7588, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K14897 : KummerData 14897 ![I14897N0, I14897N1] ![221920609, 3305951312273] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A14897
  C := by
    intro i
    match i with
    | 0 => exact C148970
    | 1 => exact C148971
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 14897 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


lemma PB18792I193_primes (p : ℕ) :
  p ∈ Set.range ![14831, 14843, 14851, 14867, 14869, 14879, 14887, 14891, 14897] ↔ Nat.Prime p ∧ 14827 < p ∧ p ≤ 14897 := by
  rw [← List.mem_ofFn']
  convert primes_range 14827 14897 (by omega)
  decide

def PB18792I193 : PrimesBelowBoundCertificateInterval O 14827 14897 18792 where
  m := 9
  g := ![3, 4, 3, 2, 5, 3, 2, 3, 2]
  P := ![14831, 14843, 14851, 14867, 14869, 14879, 14887, 14891, 14897]
  hP := PB18792I193_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I14831N0, I14831N1, I14831N2]
    · exact ![I14843N0, I14843N1, I14843N2, I14843N3]
    · exact ![I14851N0, I14851N1, I14851N2]
    · exact ![I14867N0, I14867N1]
    · exact ![I14869N0, I14869N1, I14869N2, I14869N3, I14869N4]
    · exact ![I14879N0, I14879N1, I14879N2]
    · exact ![I14887N0, I14887N1]
    · exact ![I14891N0, I14891N1, I14891N2]
    · exact ![I14897N0, I14897N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · convert (containsPrimesAbove_of_KummerData K14831) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K14843) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K14851) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K14867) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K14869) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K14879) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K14887) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K14891) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K14897) <;> rfl
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![14831, 14831, 3262205418191]
    · exact ![14843, 14843, 14843, 220314649]
    · exact ![14851, 220552201, 220552201]
    · exact ![221027689, 3286018652363]
    · exact ![14869, 14869, 14869, 14869, 14869]
    · exact ![14879, 221384641, 221384641]
    · exact ![14887, 49116651739227361]
    · exact ![14891, 14891, 3301958349971]
    · exact ![221920609, 3305951312273]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact (card_quot_of_KummerData K14831)
    · exact (card_quot_of_KummerData K14843)
    · exact (card_quot_of_KummerData K14851)
    · exact (card_quot_of_KummerData K14867)
    · exact (card_quot_of_KummerData K14869)
    · exact (card_quot_of_KummerData K14879)
    · exact (card_quot_of_KummerData K14887)
    · exact (card_quot_of_KummerData K14891)
    · exact (card_quot_of_KummerData K14897)
  β := ![I14831N0, I14831N1, I14843N0, I14843N1, I14843N2, I14851N0, I14869N0, I14869N1, I14869N2, I14869N3, I14869N4, I14879N0, I14887N0, I14891N0, I14891N1]
  Il := ![[I14831N0, I14831N1], [I14843N0, I14843N1, I14843N2], [I14851N0], [], [I14869N0, I14869N1, I14869N2, I14869N3, I14869N4], [I14879N0], [I14887N0], [I14891N0, I14891N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
