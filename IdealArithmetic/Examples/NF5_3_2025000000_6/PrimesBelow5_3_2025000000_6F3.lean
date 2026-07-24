
import IdealArithmetic.Examples.NF5_3_2025000000_6.RI5_3_2025000000_6
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![32789, -4483, 1673, 6380, -27514]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![32789, -4483, 1673, 6380, -27514]] 
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![0, 0, 107, 0, 0], ![99, 56, 71, 1, 0], ![61, 14, 13, 0, 1]] where
  M :=![![![32789, -4483, 1673, 6380, -27514], ![153924, -47373, 13861, 42751, -181060], ![945472, -208040, 55714, 199871, -849654], ![4502356, -914054, 292851, 1010562, -4319474], ![1143542, -227895, 72664, 253011, -1081677]]]
  hmulB := by decide  
  f := ![![![1572643, -280981, 113833, 338676, -1434824]], ![![7501936, -1319013, 538415, 1599721, -6781144]], ![![35534296, -6358960, 2574268, 7659993, -32450274]], ![![30545447, -5448035, 2208940, 6571077, -27840508]], ![![6589255, -1174604, 476373, 1417032, -6003833]]]
  g := ![![![10089, 219, -875, 6380, -27514], ![65105, 873, -6240, 42751, -181060], ![308291, 4620, -28875, 199871, -849654], ![1569576, 27730, -143027, 1010562, -4319474], ![393250, 6981, -35788, 253011, -1081677]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [27, 37, 67, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 19, 73], [34, 87, 34], [0, 1]]
 g := ![![[83, 89, 14], [83, 81, 79], [103, 83], [97, 25, 9], [50, 102], [1]], ![[51, 22, 8, 91], [54, 22, 88, 82], [48, 79], [89, 40, 82, 84], [82, 44], [58, 64, 78, 72]], ![[0, 103, 3, 23], [48, 4, 37, 100], [1, 76], [15, 87, 30, 100], [47, 85], [34, 62, 92, 35]]]
 h' := ![![[6, 19, 73], [6, 71, 11], [34, 85, 87], [56, 29, 46], [21, 69, 3], [80, 70, 40], [0, 1]], ![[34, 87, 34], [57, 97, 41], [78, 88, 78], [82, 72, 20], [2, 26, 55], [41, 104, 30], [6, 19, 73]], ![[0, 1], [0, 46, 55], [48, 41, 49], [17, 6, 41], [102, 12, 49], [80, 40, 37], [34, 87, 34]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [72, 28], []]
 b := ![[], [15, 27, 26], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [27, 37, 67, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5641487913, -2310873060, 513312729, 1900108143, -7976934561]
  a := ![220, -541, 57, 274, -1115]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2842278411, 27664998, -286861833, 1900108143, -7976934561]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 1225043 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1572643, -280981, 113833, 338676, -1434824]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![1572643, -280981, 113833, 338676, -1434824]] 
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![28, 36, 1, 0, 0], ![62, 16, 0, 1, 0], ![52, 44, 0, 0, 1]] where
  M :=![![![1572643, -280981, 113833, 338676, -1434824], ![7501936, -1319013, 538415, 1599721, -6781144], ![35534296, -6358960, 2574268, 7659993, -32450274], ![169627740, -29771738, 12162845, 36132436, -153173262], ![42146110, -7410125, 3024804, 8987185, -38096289]]]
  hmulB := by decide  
  f := ![![![32789, -4483, 1673, 6380, -27514]], ![![153924, -47373, 13861, 42751, -181060]], ![![69204, -19056, 5622, 17921, -76058]], ![![84094, -18224, 5779, 19534, -83386]], ![![89918, -23789, 7192, 23045, -97935]]]
  g := ![![![485965, 498453, 113833, 338676, -1434824], ![2297786, 2355821, 538415, 1599721, -6781144], ![10990182, 11273080, 2574268, 7659993, -32450274], ![51905296, 53213742, 12162845, 36132436, -153173262], ![12908908, 13234941, 3024804, 8987185, -38096289]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P1 : CertificateIrreducibleZModOfList' 107 2 2 6 [53, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [103, 106], [0, 1]]
 g := ![![[99, 105], [34, 62], [52], [3, 56], [85], [103, 1]], ![[0, 2], [0, 45], [52], [100, 51], [85], [99, 106]]]
 h' := ![![[103, 106], [17, 31], [55, 94], [55, 65], [100, 22], [105, 70], [0, 1]], ![[0, 1], [0, 76], [0, 13], [9, 42], [12, 85], [39, 37], [103, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [83]]
 b := ![[], [83, 95]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N1 : CertifiedPrimeIdeal' SI107N1 107 where
  n := 2
  hpos := by decide
  P := [53, 4, 1]
  hirr := P107P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2499268, 2319414, -446132, -1761358, 7257907]
  a := ![-351, 800, -91, -439, 1779]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2413220, -2549402, -446132, -1761358, 7257907]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N1 B_one_repr
lemma NI107N1 : Nat.card (O ⧸ I107N1) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![32789, -4483, 1673, 6380, -27514]] ![![1572643, -280981, 113833, 338676, -1434824]]
  ![![107, 0, 0, 0, 0]] where
 M := ![![![107, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0)
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2011, 461, -136, -461, 1962]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![-2011, 461, -136, -461, 1962]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![0, 0, 109, 0, 0], ![63, 108, 97, 1, 0], ![84, 92, 91, 0, 1]] where
  M :=![![![-2011, 461, -136, -461, 1962], ![-10444, 2399, -708, -2400, 10214], ![-54364, 12498, -3685, -12486, 53140], ![-282872, 65080, -19164, -65005, 276644], ![-71210, 16383, -4824, -16363, 69637]]]
  hmulB := by decide  
  f := ![![![-27, 5, 0, -1, 4]], ![![-16, -31, 4, 2, -6]], ![![-20, 98, -41, -54, 232]], ![![-61, 65, -33, -50, 216]], ![![-54, 61, -31, -45, 195]]]
  g := ![![![-1264, -1195, -1229, -461, 1962], ![-6580, -6221, -6398, -2400, 10214], ![-34234, -32366, -33287, -12486, 53140], ![-178217, -168492, -173287, -65005, 276644], ![-44861, -42413, -43620, -16363, 69637]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [73, 77, 36, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [69, 91, 73], [4, 17, 36], [0, 1]]
 g := ![![[11, 40, 71], [30, 81], [67, 82, 35], [9, 29, 74], [90, 97], [1]], ![[53, 91, 61, 78], [55, 27], [6, 77, 6, 64], [47, 35, 99, 63], [101, 73], [41, 47, 29, 105]], ![[20, 108, 80, 89], [0, 29], [55, 51, 96, 81], [11, 30, 6, 34], [74, 84], [18, 97, 7, 4]]]
 h' := ![![[69, 91, 73], [77, 102, 17], [14, 91, 9], [106, 44, 97], [67, 65, 40], [36, 32, 73], [0, 1]], ![[4, 17, 36], [107, 56, 105], [31, 101, 38], [10, 14, 65], [59, 31, 84], [42, 98, 89], [69, 91, 73]], ![[0, 1], [93, 60, 96], [23, 26, 62], [65, 51, 56], [33, 13, 94], [58, 88, 56], [4, 17, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [107, 89], []]
 b := ![[], [59, 27, 60], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [73, 77, 36, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9167239, -2500324, 581601, 2220415, -9485520]
  a := ![15, -39, 4, 18, -76]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![6110686, 5783144, 5948474, 2220415, -9485520]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 1295029 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![26207, -5939, 1752, 5983, -25478]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![26207, -5939, 1752, 5983, -25478]] 
 ![![109, 0, 0, 0, 0], ![18, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![55, 0, 0, 1, 0], ![39, 0, 0, 0, 1]] where
  M :=![![![26207, -5939, 1752, 5983, -25478], ![135924, -31799, 9320, 31528, -134162], ![713748, -164614, 48029, 163614, -696332], ![3706600, -851224, 250256, 851453, -3624676], ![933638, -214265, 62976, 214341, -912465]]]
  hmulB := by decide  
  f := ![![![81078703, 54177037, -8928288, -33549757, 129856848]], ![![9500158, 6347989, -1046136, -3931060, 15215458]], ![![22564637, 15077781, -2484795, -9337093, 36139920]], ![![-65395507, -43698621, 7201520, 27061018, -104741804]], ![![7115655, 4754446, -783512, -2944214, 11395777]]]
  g := ![![![7270, -5939, 1752, 5983, -25478], ![38336, -31799, 9320, 31528, -134162], ![198999, -164614, 48029, 163614, -696332], ![1034957, -851224, 250256, 851453, -3624676], ![260540, -214265, 62976, 214341, -912465]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1

def I109N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-37963, -10579, 4445, 6218, -25474]] i)))

def SI109N2: IdealEqSpanCertificate' Table ![![-37963, -10579, 4445, 6218, -25474]] 
 ![![109, 0, 0, 0, 0], ![103, 1, 0, 0, 0], ![73, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![83, 0, 0, 0, 1]] where
  M :=![![![-37963, -10579, 4445, 6218, -25474], ![115140, -44997, -749, 8263, -28912], ![24568, 367612, -61574, -129055, 504978], ![-1772588, -1087478, 306009, 500070, -2010950], ![-480610, -230307, 72364, 112995, -456861]]]
  hmulB := by decide  
  f := ![![![-17254891, -10841699, 1751807, 6628770, -25593112]], ![![-15551969, -9711656, 1565976, 5929949, -22889004]], ![![-15847919, -9986131, 1615099, 6109407, -23590750]], ![![20437942, 14347900, -2399557, -8970568, 34785586]], ![![-8898771, -5253584, 830665, 3167705, -12196379]]]
  g := ![![![25955, -10579, 4445, 6218, -25474], ![65942, -44997, -749, 8263, -28912], ![-688070, 367612, -61574, -129055, 504978], ![2328511, -1087478, 306009, 500070, -2010950], ![510568, -230307, 72364, 112995, -456861]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N2 : Nat.card (O ⧸ I109N2) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N2)

lemma isPrimeI109N2 : Ideal.IsPrime I109N2 := prime_ideal_of_norm_prime hp109.out _ NI109N2
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![-2011, 461, -136, -461, 1962]] ![![26207, -5939, 1752, 5983, -25478]]
  ![![35944115, -8302172, 2432200, 8268300, -35191966]] where
 M := ![![![35944115, -8302172, 2432200, 8268300, -35191966]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI109N1 : IdealMulLeCertificate' Table 
  ![![35944115, -8302172, 2432200, 8268300, -35191966]] ![![-37963, -10579, 4445, 6218, -25474]]
  ![![109, 0, 0, 0, 0]] where
 M := ![![![-3382813365, 787713461, -227577721, -775328336, 3298396680]]]
 hmul := by decide  
 g := ![![![![-31034985, 7226729, -2087869, -7113104, 30260520]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N1, I109N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N1
    exact isPrimeI109N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 109 (by decide) (𝕀 ⊙ MulI109N0 ⊙ MulI109N1)
instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-139, -95, 15, 58, -224]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![-139, -95, 15, 58, -224]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![66, 45, 1, 0, 0], ![81, 75, 0, 1, 0], ![81, 39, 0, 0, 1]] where
  M :=![![![-139, -95, 15, 58, -224], ![720, 517, -85, -317, 1228], ![-4032, -2668, 440, 1629, -6302], ![20500, 13826, -2323, -8596, 33314], ![4226, 2845, -480, -1773, 6873]]]
  hmulB := by decide  
  f := ![![![3689, -859, 249, 850, -3618]], ![![19268, -4465, 1299, 4435, -18880]], ![![10718, -2487, 723, 2468, -10506]], ![![20089, -4660, 1355, 4625, -19688]], ![![10467, -2429, 706, 2410, -10259]]]
  g := ![![![109, 32, 15, 58, -224], ![-597, -175, -85, -317, 1228], ![3057, 895, 440, 1629, -6302], ![-16180, -4745, -2323, -8596, 33314], ![-3338, -979, -480, -1773, 6873]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [79, 44, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [69, 112], [0, 1]]
 g := ![![[12, 2], [104], [31], [31], [77, 28], [69, 1]], ![[37, 111], [104], [31], [31], [88, 85], [25, 112]]]
 h' := ![![[69, 112], [32, 51], [15, 45], [59, 101], [19, 101], [86, 49], [0, 1]], ![[0, 1], [48, 62], [69, 68], [22, 12], [95, 12], [77, 64], [69, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [101]]
 b := ![[], [94, 107]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [79, 44, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4074790, 2558438, -473617, -2026790, 8443743]
  a := ![-381, 955, -99, -477, 1931]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4359197, -1357748, -473617, -2026790, 8443743]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-20285, -13435, 2208, 8305, -32134]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![-20285, -13435, 2208, 8305, -32134]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![30, 70, 1, 0, 0], ![47, 102, 0, 1, 0], ![0, 6, 0, 0, 1]] where
  M :=![![![-20285, -13435, 2208, 8305, -32134], ![104644, 70493, -11646, -43724, 169290], ![-553828, -367370, 60405, 227164, -879004], ![2863672, 1926384, -318118, -1194527, 4624704], ![589134, 396859, -65564, -246155, 953059]]]
  hmulB := by decide  
  f := ![![![1591, -711, 156, 469, -1952]], ![![9480, -561, 214, 1270, -5546]], ![![6582, -626, 205, 1002, -4340]], ![![11273, -1379, 398, 1816, -7820]], ![![1010, -179, 48, 189, -807]]]
  g := ![![![-4220, -7277, 2208, 8305, -32134], ![22204, 38317, -11646, -43724, 169290], ![-115422, -199048, 60405, 227164, -879004], ![606637, 1046798, -318118, -1194527, 4624704], ![125003, 215715, -65564, -246155, 953059]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P1 : CertificateIrreducibleZModOfList' 113 2 2 6 [30, 54, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [59, 112], [0, 1]]
 g := ![![[47, 49], [26], [60], [9], [96, 105], [59, 1]], ![[0, 64], [26], [60], [9], [76, 8], [5, 112]]]
 h' := ![![[59, 112], [39, 7], [49, 34], [43, 88], [58, 3], [38, 61], [0, 1]], ![[0, 1], [0, 106], [21, 79], [37, 25], [9, 110], [21, 52], [59, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43]]
 b := ![[], [72, 78]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N1 : CertifiedPrimeIdeal' SI113N1 113 where
  n := 2
  hpos := by decide
  P := [30, 54, 1]
  hirr := P113P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4974593, 3687658, -703835, -2924534, 12126199]
  a := ![469, -1152, 123, 588, -2377]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1359235, 2464614, -703835, -2924534, 12126199]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N1 B_one_repr
lemma NI113N1 : Nat.card (O ⧸ I113N1) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N1

def I113N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![35689, -8212, 2409, 8197, -34892]] i)))

def SI113N2: IdealEqSpanCertificate' Table ![![35689, -8212, 2409, 8197, -34892]] 
 ![![113, 0, 0, 0, 0], ![111, 1, 0, 0, 0], ![109, 0, 1, 0, 0], ![105, 0, 0, 1, 0], ![32, 0, 0, 0, 1]] where
  M :=![![![35689, -8212, 2409, 8197, -34892], ![185856, -43035, 12609, 42823, -182258], ![970284, -224050, 65584, 223045, -949322], ![5054412, -1166062, 341847, 1162328, -4947350], ![1272744, -293586, 86064, 292650, -1245641]]]
  hmulB := by decide  
  f := ![![![-18697975, -12493936, 2058975, 7737001, -29946632]], ![![-17501937, -11694727, 1927266, 7242080, -28031002]], ![![-22559231, -15074026, 2484169, 9334750, -36130838]], ![![6273621, 4192510, -690942, -2596317, 10049282]], ![![-424672, -283654, 46740, 175642, -679825]]]
  g := ![![![8323, -8212, 2409, 8197, -34892], ![43577, -43035, 12609, 42823, -182258], ![226989, -224050, 65584, 223045, -949322], ![1181387, -1166062, 341847, 1162328, -4947350], ![297452, -293586, 86064, 292650, -1245641]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N2 : Nat.card (O ⧸ I113N2) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N2)

lemma isPrimeI113N2 : Ideal.IsPrime I113N2 := prime_ideal_of_norm_prime hp113.out _ NI113N2
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![-139, -95, 15, 58, -224]] ![![-20285, -13435, 2208, 8305, -32134]]
  ![![18697975, 12493936, -2058975, -7737001, 29946632]] where
 M := ![![![18697975, 12493936, -2058975, -7737001, 29946632]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI113N1 : IdealMulLeCertificate' Table 
  ![![18697975, 12493936, -2058975, -7737001, 29946632]] ![![35689, -8212, 2409, 8197, -34892]]
  ![![113, 0, 0, 0, 0]] where
 M := ![![![-113, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC113 : ContainsPrimesAboveP 113 ![I113N0, I113N1, I113N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
    exact isPrimeI113N1
    exact isPrimeI113N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 113 (by decide) (𝕀 ⊙ MulI113N0 ⊙ MulI113N1)
instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11395, -2507, 779, 2644, -11282]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![11395, -2507, 779, 2644, -11282]] 
 ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![0, 0, 127, 0, 0], ![0, 0, 0, 127, 0], ![83, 56, 25, 11, 1]] where
  M :=![![![11395, -2507, 779, 2644, -11282], ![60660, -15447, 4373, 14553, -61796], ![326032, -71080, 20610, 72035, -306922], ![1640892, -381274, 113647, 383654, -1633810], ![413934, -95383, 28468, 96351, -410387]]]
  hmulB := by decide  
  f := ![![![65353, 43671, -7197, -27044, 104676]], ![![-341704, -228323, 37627, 141391, -547264]], ![![1786456, 1193760, -196732, -739255, 2861346]], ![![-9340556, -6241286, 1028549, 3864976, -14959670]], ![![-580469, -387850, 63916, 240178, -929625]]]
  g := ![![![7463, 4955, 2227, 998, -11282], ![40864, 27127, 12199, 5467, -61796], ![203154, 134776, 60580, 27151, -306922], ![1080686, 717418, 322511, 144532, -1633810], ![271465, 180207, 81009, 36304, -410387]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 4 2 6 [125, 122, 20, 83, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [35, 90, 47, 62], [114, 76, 35, 41], [22, 87, 45, 24], [0, 1]]
 g := ![![[81, 119, 71, 74], [46, 101, 61, 98], [45, 86, 98, 74], [34, 97, 95, 74], [117, 11, 44, 1], []], ![[32, 5, 30, 32, 86, 98], [93, 40, 9, 122, 48, 115], [92, 106, 84, 5, 111, 81], [52, 125, 121, 0, 75, 35], [67, 63, 17, 109, 39, 26], [71, 22, 78, 1, 10, 76]], ![[84, 59, 84, 15, 44, 31], [83, 56, 3, 3, 95, 69], [125, 76, 91, 49, 116, 104], [50, 107, 53, 65, 120, 99], [52, 104, 110, 97, 115, 52], [109, 36, 119, 19, 120, 87]], ![[111, 65, 108, 28, 48, 48], [10, 14, 114, 47, 109, 20], [112, 110, 120, 78, 73, 77], [43, 83, 77, 112, 24, 97], [120, 50, 16, 84, 28, 40], [6, 86, 105, 77, 89, 108]]]
 h' := ![![[35, 90, 47, 62], [92, 23, 9, 70], [90, 68, 125, 15], [68, 2, 99, 70], [107, 99, 89, 70], [0, 0, 0, 1], [0, 1]], ![[114, 76, 35, 41], [70, 22, 81, 72], [58, 97, 72, 32], [112, 41, 117, 33], [28, 64, 75, 107], [91, 60, 102, 122], [35, 90, 47, 62]], ![[22, 87, 45, 24], [23, 106, 15, 96], [97, 36, 107, 108], [16, 11, 57, 120], [36, 76, 106, 104], [53, 33, 15, 71], [114, 76, 35, 41]], ![[0, 1], [93, 103, 22, 16], [85, 53, 77, 99], [30, 73, 108, 31], [124, 15, 111, 100], [119, 34, 10, 60], [22, 87, 45, 24]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [35, 101, 56], []]
 b := ![[], [], [102, 71, 124, 42], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 4
  hpos := by decide
  P := [125, 122, 20, 83, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![29399258945981, 19573543899760, -3282676006600, -12280085884728, 47601844742924]
  a := ![-264, 648, -68, -340, 1338]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-30878376808793, -20835667414992, -9396289721100, -4219688016196, 47601844742924]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 260144641 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-65353, -43671, 7197, 27044, -104676]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![-65353, -43671, 7197, 27044, -104676]] 
 ![![127, 0, 0, 0, 0], ![64, 1, 0, 0, 0], ![95, 0, 1, 0, 0], ![16, 0, 0, 1, 0], ![81, 0, 0, 0, 1]] where
  M :=![![![-65353, -43671, 7197, 27044, -104676], ![341704, 228323, -37627, -141391, 547264], ![-1786456, -1193760, 196732, 739255, -2861346], ![9340556, 6241286, -1028549, -3864976, 14959670], ![1923722, 1285409, -211832, -796001, 3080979]]]
  hmulB := by decide  
  f := ![![![-11395, 2507, -779, -2644, 11282]], ![![-6220, 1385, -427, -1447, 6172]], ![![-11091, 2435, -745, -2545, 10856]], ![![-14356, 3318, -993, -3354, 14286]], ![![-10527, 2350, -721, -2445, 10427]]]
  g := ![![![79464, -43671, 7197, 27044, -104676], ![-415453, 228323, -37627, -141391, 547264], ![2172170, -1193760, 196732, 739255, -2861346], ![-11356561, 6241286, -1028549, -3864976, 14959670], ![-2338911, 1285409, -211832, -796001, 3080979]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![11395, -2507, 779, 2644, -11282]] ![![-65353, -43671, 7197, 27044, -104676]]
  ![![127, 0, 0, 0, 0]] where
 M := ![![![-127, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC127 : ContainsPrimesAboveP 127 ![I127N0, I127N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
    exact isPrimeI127N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 127 (by decide) (𝕀 ⊙ MulI127N0)
instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![56358671, -9968702, 4057703, 12062225, -51120464]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![56358671, -9968702, 4057703, 12062225, -51120464]] 
 ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![0, 0, 131, 0, 0], ![38, 119, 25, 1, 0], ![84, 77, 121, 0, 1]] where
  M :=![![![56358671, -9968702, 4057703, 12062225, -51120464], ![267656264, -47585321, 19322907, 57465481, -243498690], ![1274003612, -225230410, 91700756, 272584627, -1155251374], ![6049088548, -1076039778, 436831413, 1299178884, -5504907498], ![1503693916, -267336012, 108556488, 322842404, -1367981015]]]
  hmulB := by decide  
  f := ![![![10797, 5910, -453, -37, -924]], ![![27280, -46167, 12305, 28565, -118142]], ![![557972, -64206, 5690, 59989, -255630]], ![![144834, -52727, 12818, 39744, -166786]], ![![541188, -82631, 12341, 72726, -308595]]]
  g := ![![![29710787, 19014521, 44947162, 12062225, -51120464], ![141510366, 90560470, 214091812, 57465481, -243498690], ![671426742, 429706525, 1015744285, 272584627, -1155251374], ![3199179548, 2047324812, 4840085241, 1299178884, -5504907498], ![795008304, 508770657, 1202772513, 322842404, -1367981015]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [99, 121, 19, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [52, 85, 11], [60, 45, 120], [0, 1]]
 g := ![![[18, 103, 94], [101, 118, 46], [27, 5], [28, 101], [114, 91], [112, 1], []], ![[22, 79, 79, 102], [43, 122, 88, 129], [46, 62], [90, 59], [110, 5], [53, 60], [95, 121]], ![[117, 48, 120, 19], [12, 76, 31, 32], [26, 25], [118, 13], [84, 1], [103, 20], [117, 121]]]
 h' := ![![[52, 85, 11], [88, 20, 116], [9, 104, 35], [113, 60, 108], [93, 73, 25], [47, 104, 109], [0, 0, 1], [0, 1]], ![[60, 45, 120], [118, 82, 69], [1, 83, 99], [25, 34, 18], [114, 81, 94], [0, 13, 23], [111, 38, 45], [52, 85, 11]], ![[0, 1], [120, 29, 77], [110, 75, 128], [123, 37, 5], [88, 108, 12], [85, 14, 130], [8, 93, 85], [60, 45, 120]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [128, 102], []]
 b := ![[], [41, 1, 86], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [99, 121, 19, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-164055286076, 62216781433, -13901519688, -51794334203, 218135932145]
  a := ![-641, 1583, -166, -797, 3249]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-126101441882, -80692551325, -191706037818, -51794334203, 218135932145]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 2248091 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10797, -5910, 453, 37, 924]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![-10797, -5910, 453, 37, 924]] 
 ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![78, 106, 1, 0, 0], ![116, 108, 0, 1, 0], ![114, 53, 0, 0, 1]] where
  M :=![![![-10797, -5910, 453, 37, 924], ![-27280, 46167, -12305, -28565, 118142], ![-557972, 64206, -5690, -59989, 255630], ![-1367348, 32794, -89827, -308910, 1364206], ![-373508, -2684, -18748, -72040, 320165]]]
  hmulB := by decide  
  f := ![![![-56358671, 9968702, -4057703, -12062225, 51120464]], ![![-267656264, 47585321, -19322907, -57465481, 243498690]], ![![-259859114, 46159032, -18751372, -55761673, 236286326]], ![![-316744816, 56271938, -22858007, -67974572, 288036182]], ![![-168811942, 29967863, -12177471, -36210737, 153443851]]]
  g := ![![![-1189, -816, 453, 37, 924], ![-70398, -13939, -12305, -28565, 118142], ![-170208, -48872, -5690, -59989, 255630], ![-870586, -224322, -89827, -308910, 1364206], ![-206514, -54991, -18748, -72040, 320165]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P1 : CertificateIrreducibleZModOfList' 131 2 2 7 [55, 92, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 130], [0, 1]]
 g := ![![[116, 81], [127, 74], [74], [52], [81], [80], [1]], ![[0, 50], [0, 57], [74], [52], [81], [80], [1]]]
 h' := ![![[39, 130], [89, 122], [126, 27], [129, 27], [32, 24], [66, 9], [76, 39], [0, 1]], ![[0, 1], [0, 9], [0, 104], [3, 104], [51, 107], [24, 122], [25, 92], [39, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [83, 73]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N1 : CertifiedPrimeIdeal' SI131N1 131 where
  n := 2
  hpos := by decide
  P := [55, 92, 1]
  hirr := P131P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![21826, 77146, -13973, -53858, 216131]
  a := ![-59, 141, -15, -75, 299]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-131906, -31145, -13973, -53858, 216131]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N1 B_one_repr
lemma NI131N1 : Nat.card (O ⧸ I131N1) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![56358671, -9968702, 4057703, 12062225, -51120464]] ![![-10797, -5910, 453, 37, 924]]
  ![![131, 0, 0, 0, 0]] where
 M := ![![![-131, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC131 : ContainsPrimesAboveP 131 ![I131N0, I131N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
    exact isPrimeI131N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 131 (by decide) (𝕀 ⊙ MulI131N0)
instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7281, -3286, 1056, 1626, -6578]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![-7281, -3286, 1056, 1626, -6578]] 
 ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![83, 12, 1, 0, 0], ![100, 76, 0, 1, 0], ![53, 34, 0, 0, 1]] where
  M :=![![![-7281, -3286, 1056, 1626, -6578], ![27940, -4699, -1216, -198, 1616], ![-24592, 70820, -9841, -23068, 89452], ![-295768, -266324, 64672, 112435, -448608], ![-85216, -59926, 15880, 26530, -106319]]]
  hmulB := by decide  
  f := ![![![19535, 3582, -112, -1050, 3182]], ![![9668, -38619, 8640, 29474, -118280]], ![![16197, -430, 639, 1654, -7450]], ![![19732, -26192, 6304, 21075, -85240]], ![![10355, -9786, 2456, 8120, -32985]]]
  g := ![![![665, 614, 1056, 1626, -6578], ![460, -219, -1216, -198, 1616], ![-11985, -8024, -9841, -23068, 89452], ![50140, 41352, 64672, 112435, -448608], ![11523, 9840, 15880, 26530, -106319]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [55, 36, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [101, 136], [0, 1]]
 g := ![![[43, 87], [60], [87], [20, 60], [112], [63], [1]], ![[62, 50], [60], [87], [52, 77], [112], [63], [1]]]
 h' := ![![[101, 136], [116, 19], [26, 34], [133, 118], [24, 34], [108, 48], [82, 101], [0, 1]], ![[0, 1], [117, 118], [35, 103], [132, 19], [33, 103], [24, 89], [8, 36], [101, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55]]
 b := ![[], [84, 96]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [55, 36, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5376554, 4987202, -944036, -3870912, 15985319]
  a := ![-527, 1296, -134, -662, 2671]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2825929, -1700700, -944036, -3870912, 15985319]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-693, 167, -50, -167, 708]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![-693, 167, -50, -167, 708]] 
 ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![54, 2, 1, 0, 0], ![29, 50, 0, 1, 0], ![0, 53, 0, 0, 1]] where
  M :=![![![-693, 167, -50, -167, 708], ![-3712, 759, -240, -796, 3398], ![-18300, 4446, -1321, -4426, 18764], ![-98376, 20176, -6340, -21089, 90044], ![-24634, 5137, -1604, -5341, 22789]]]
  hmulB := by decide  
  f := ![![![-865, 43, 54, 41, -186]], ![![1228, -1867, 216, 566, -2174]], ![![-274, 50, 11, 0, -8]], ![![-109, -755, 130, 268, -1050]], ![![382, -734, 92, 229, -883]]]
  g := ![![![50, -211, -50, -167, 708], ![236, -1015, -240, -796, 3398], ![1324, -5592, -1321, -4426, 18764], ![6245, -26898, -6340, -21089, 90044], ![1583, -6806, -1604, -5341, 22789]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P1 : CertificateIrreducibleZModOfList' 137 2 2 7 [97, 121, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 136], [0, 1]]
 g := ![![[110, 59], [115], [50], [17, 15], [130], [119], [1]], ![[95, 78], [115], [50], [120, 122], [130], [119], [1]]]
 h' := ![![[16, 136], [20, 123], [107, 72], [132, 18], [70, 17], [58, 33], [40, 16], [0, 1]], ![[0, 1], [70, 14], [26, 65], [9, 119], [68, 120], [38, 104], [22, 121], [16, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54]]
 b := ![[], [58, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N1 : CertifiedPrimeIdeal' SI137N1 137 where
  n := 2
  hpos := by decide
  P := [97, 121, 1]
  hirr := P137P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2166645, 1557031, -286734, -1206789, 5007500]
  a := ![-293, 721, -77, -367, 1485]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![352656, -1481223, -286734, -1206789, 5007500]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N1 B_one_repr
lemma NI137N1 : Nat.card (O ⧸ I137N1) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N1

def I137N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-83, 89, -22, -73, 296]] i)))

def SI137N2: IdealEqSpanCertificate' Table ![![-83, 89, -22, -73, 296]] 
 ![![137, 0, 0, 0, 0], ![123, 1, 0, 0, 0], ![78, 0, 1, 0, 0], ![133, 0, 0, 1, 0], ![74, 0, 0, 0, 1]] where
  M :=![![![-83, 89, -22, -73, 296], ![-1272, -163, -8, 16, 2], ![-1460, 2290, -543, -1822, 7356], ![-30920, -5144, 60, 1265, -3452], ![-7150, -921, -44, 93, -1]]]
  hmulB := by decide  
  f := ![![![1641, -35, -14, 111, -490]], ![![1495, -34, -10, 107, -472]], ![![1122, -112, 13, 124, -532]], ![![2821, -123, 14, 272, -1190]], ![![1200, -47, 0, 103, -451]]]
  g := ![![![-157, 89, -22, -73, 296], ![125, -163, -8, 16, 2], ![-3962, 2290, -543, -1822, 7356], ![4995, -5144, 60, 1265, -3452], ![710, -921, -44, 93, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N2 : Nat.card (O ⧸ I137N2) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N2)

lemma isPrimeI137N2 : Ideal.IsPrime I137N2 := prime_ideal_of_norm_prime hp137.out _ NI137N2
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![-7281, -3286, 1056, 1626, -6578]] ![![-693, 167, -50, -167, 708]]
  ![![1641, -35, -14, 111, -490]] where
 M := ![![![1641, -35, -14, 111, -490]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI137N1 : IdealMulLeCertificate' Table 
  ![![1641, -35, -14, 111, -490]] ![![-83, 89, -22, -73, 296]]
  ![![137, 0, 0, 0, 0]] where
 M := ![![![137, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC137 : ContainsPrimesAboveP 137 ![I137N0, I137N1, I137N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
    exact isPrimeI137N1
    exact isPrimeI137N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 137 (by decide) (𝕀 ⊙ MulI137N0 ⊙ MulI137N1)
instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3023969, -698370, 204610, 695588, -2960610]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![3023969, -698370, 204610, 695588, -2960610]] 
 ![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![0, 0, 139, 0, 0], ![0, 0, 0, 139, 0], ![130, 117, 34, 127, 1]] where
  M :=![![![3023969, -698370, 204610, 695588, -2960610], ![15764116, -3641353, 1066766, 3626400, -15434852], ![82182952, -18980640, 5560559, 18903770, -80459320], ![428410560, -98946688, 28988570, 98547499, -419443780], ![107869480, -24913598, 7298976, 24813154, -105611249]]]
  hmulB := by decide  
  f := ![![![22963, 15406, -2542, -9548, 36962]], ![![-120788, -80419, 13238, 49764, -192588]], ![![628056, 421072, -69463, -260926, 1010064]], ![![-3300176, -2198568, 361986, 1360669, -5265956]], ![![-2946730, -1962307, 323046, 1214351, -4699613]]]
  g := ![![![2790671, 2487000, 725650, 2710022, -2960610], ![14548884, 12965729, 3783106, 14128436, -15434852], ![75840968, 67588200, 19720701, 73649190, -80459320], ![395367640, 352345148, 102806310, 383941781, -419443780], ![99549150, 88716565, 25885478, 96672243, -105611249]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 4 2 7 [96, 15, 31, 59, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 47, 1, 95], [30, 100, 20, 50], [32, 130, 118, 133], [0, 1]]
 g := ![![[78, 68, 2, 38], [3, 80, 88, 118], [10, 100, 99], [95, 110, 117, 36], [124, 107, 6], [1], []], ![[124, 110, 4, 7, 67, 62], [79, 16, 119, 94, 95, 93], [41, 29, 127], [70, 51, 20, 45, 53, 17], [100, 115, 67], [123, 86, 99], [56, 85, 129]], ![[70, 55, 70, 71, 74, 48], [45, 29, 136, 119, 7, 108], [76, 11, 45], [76, 126, 50, 80, 86, 53], [61, 119, 46], [138, 2, 81], [36, 33, 137]], ![[43, 45, 44, 6, 84, 85], [32, 37, 53, 77, 63, 53], [59, 74, 117], [39, 19, 68, 88, 72, 33], [117, 29, 77], [44, 79, 125], [71, 74, 36]]]
 h' := ![![[18, 47, 1, 95], [129, 20, 31, 90], [10, 16, 55, 102], [54, 93, 123, 88], [92, 61, 13, 6], [43, 124, 108, 80], [0, 0, 1], [0, 1]], ![[30, 100, 20, 50], [78, 64, 111, 84], [74, 51, 72, 24], [37, 118, 72, 31], [54, 25, 29, 66], [87, 81, 135, 117], [91, 59, 55, 88], [18, 47, 1, 95]], ![[32, 130, 118, 133], [132, 36, 20, 107], [75, 132, 50, 91], [137, 113, 10, 36], [13, 22, 75, 75], [93, 124, 98, 18], [85, 68, 51, 130], [30, 100, 20, 50]], ![[0, 1], [95, 19, 116, 136], [116, 79, 101, 61], [9, 93, 73, 123], [0, 31, 22, 131], [116, 88, 76, 63], [46, 12, 32, 60], [32, 130, 118, 133]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [84, 89, 64], []]
 b := ![[], [], [88, 50, 75, 71], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 4
  hpos := by decide
  P := [96, 15, 31, 59, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-30943580040190, 9387046732932, -2316046028752, -8389984555564, 35503396348568]
  a := ![-248, 612, -65, -308, 1257]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-33427230973770, -29816621050716, -8700946200576, -32498714538300, 35503396348568]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 373301041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-22963, -15406, 2542, 9548, -36962]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![-22963, -15406, 2542, 9548, -36962]] 
 ![![139, 0, 0, 0, 0], ![99, 1, 0, 0, 0], ![68, 0, 1, 0, 0], ![79, 0, 0, 1, 0], ![96, 0, 0, 0, 1]] where
  M :=![![![-22963, -15406, 2542, 9548, -36962], ![120788, 80419, -13238, -49764, 192588], ![-628056, -421072, 69463, 260926, -1010064], ![3300176, 2198568, -361986, -1360669, 5265956], ![680016, 452742, -74528, -280162, 1084235]]]
  hmulB := by decide  
  f := ![![![-3023969, 698370, -204610, -695588, 2960610]], ![![-2267173, 523597, -153404, -521508, 2219678]], ![![-2070596, 478200, -140101, -476286, 2027200]], ![![-4800749, 1108762, -324840, -1104309, 4700230]], ![![-2864536, 661562, -193824, -658918, 2804531]]]
  g := ![![![29665, -15406, 2542, 9548, -36962], ![-154659, 80419, -13238, -49764, 192588], ![810702, -421072, 69463, 260926, -1010064], ![-4228647, 2198568, -361986, -1360669, 5265956], ![-870700, 452742, -74528, -280162, 1084235]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![3023969, -698370, 204610, 695588, -2960610]] ![![-22963, -15406, 2542, 9548, -36962]]
  ![![139, 0, 0, 0, 0]] where
 M := ![![![-139, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC139 : ContainsPrimesAboveP 139 ![I139N0, I139N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
    exact isPrimeI139N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 139 (by decide) (𝕀 ⊙ MulI139N0)
instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-433, 66, -29, -91, 386]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![-433, 66, -29, -91, 386]] 
 ![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![35, 104, 1, 0, 0], ![85, 96, 0, 1, 0], ![147, 9, 0, 0, 1]] where
  M :=![![![-433, 66, -29, -91, 386], ![-2028, 369, -157, -441, 1874], ![-9916, 2038, -732, -2245, 9454], ![-48244, 6226, -3051, -9040, 38670], ![-11984, 1584, -760, -2268, 9691]]]
  hmulB := by decide  
  f := ![![![450003, -103934, 30449, 103513, -440578]], ![![2345884, -541823, 158735, 539625, -2296782]], ![![1825177, -421556, 123501, 419846, -1786972]], ![![2196023, -507208, 148594, 505151, -2150052]], ![![693393, -160149, 46918, 159500, -678873]]]
  g := ![![![-325, 56, -29, -91, 386], ![-1574, 283, -157, -441, 1874], ![-7941, 1400, -732, -2245, 9454], ![-32601, 5660, -3051, -9040, 38670], ![-8169, 1417, -760, -2268, 9691]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [108, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [133, 148], [0, 1]]
 g := ![![[105, 4], [19], [39, 63], [37], [48, 148], [107], [1]], ![[41, 145], [19], [74, 86], [37], [64, 1], [107], [1]]]
 h' := ![![[133, 148], [144, 147], [109, 67], [94, 130], [31, 127], [108, 105], [41, 133], [0, 1]], ![[0, 1], [27, 2], [80, 82], [100, 19], [85, 22], [67, 44], [148, 16], [133, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [105]]
 b := ![[], [122, 127]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [108, 16, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5936153, 5126530, -966249, -3924566, 16241025]
  a := ![501, -1222, 119, 628, -2539]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-13597047, 2256413, -966249, -3924566, 16241025]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5291, -1266, 367, 1249, -5308]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![5291, -1266, 367, 1249, -5308]] 
 ![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![145, 97, 1, 0, 0], ![90, 123, 0, 1, 0], ![69, 36, 0, 0, 1]] where
  M :=![![![5291, -1266, 367, 1249, -5308], ![28096, -6249, 1855, 6293, -26826], ![143692, -34394, 9968, 33927, -144182], ![763156, -169722, 50377, 170912, -728578], ![191820, -42952, 12720, 43168, -183967]]]
  hmulB := by decide  
  f := ![![![927, 1294, -275, -507, 2008]], ![![-7592, -2161, 907, 1279, -5242]], ![![-3881, -209, 322, 351, -1500]], ![![-5662, -505, 500, 577, -2440]], ![![-1365, 202, 69, 29, -159]]]
  g := ![![![1382, 4, 367, 1249, -5308], ![7005, 37, 1855, 6293, -26826], ![37540, 109, 9968, 33927, -144182], ![190257, 1009, 50377, 170912, -728578], ![48027, 244, 12720, 43168, -183967]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P1 : CertificateIrreducibleZModOfList' 149 2 2 7 [1, 115, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 148], [0, 1]]
 g := ![![[115, 1], [29], [130, 5], [7], [32, 17], [113], [1]], ![[0, 148], [29], [2, 144], [7], [14, 132], [113], [1]]]
 h' := ![![[34, 148], [34, 148], [19, 25], [123, 81], [117, 56], [37, 49], [148, 34], [0, 1]], ![[0, 1], [0, 1], [124, 124], [46, 68], [84, 93], [64, 100], [112, 115], [34, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [96, 82]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N1 : CertifiedPrimeIdeal' SI149N1 149 where
  n := 2
  hpos := by decide
  P := [1, 115, 1]
  hirr := P149P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2580457, 1452603, -277093, -1156876, 4833806]
  a := ![279, -681, 70, 348, -1414]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1287354, -22756, -277093, -1156876, 4833806]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N1 B_one_repr
lemma NI149N1 : Nat.card (O ⧸ I149N1) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N1

def I149N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-151, 40, -8, -30, 126]] i)))

def SI149N2: IdealEqSpanCertificate' Table ![![-151, 40, -8, -30, 126]] 
 ![![149, 0, 0, 0, 0], ![97, 1, 0, 0, 0], ![127, 0, 1, 0, 0], ![48, 0, 0, 1, 0], ![62, 0, 0, 0, 1]] where
  M :=![![![-151, 40, -8, -30, 126], ![-636, 47, -26, -110, 480], ![-2800, 1044, -303, -886, 3740], ![-19272, 4044, -1018, -3823, 16244], ![-4812, 1072, -268, -984, 4175]]]
  hmulB := by decide  
  f := ![![![-8411, -1600, 60, 494, -1538]], ![![-5499, -929, 14, 236, -658]], ![![-8561, -1684, 73, 544, -1730]], ![![-2632, 2436, -614, -2027, 8236]], ![![-3630, -32, -116, -276, 1291]]]
  g := ![![![-63, 40, -8, -30, 126], ![-177, 47, -26, -110, 480], ![-1711, 1044, -303, -886, 3740], ![-7422, 4044, -1018, -3823, 16244], ![-1922, 1072, -268, -984, 4175]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N2 : Nat.card (O ⧸ I149N2) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N2)

lemma isPrimeI149N2 : Ideal.IsPrime I149N2 := prime_ideal_of_norm_prime hp149.out _ NI149N2
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![-433, 66, -29, -91, 386]] ![![5291, -1266, 367, 1249, -5308]]
  ![![-8411, -1600, 60, 494, -1538]] where
 M := ![![![-8411, -1600, 60, 494, -1538]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI149N1 : IdealMulLeCertificate' Table 
  ![![-8411, -1600, 60, 494, -1538]] ![![-151, 40, -8, -30, 126]]
  ![![149, 0, 0, 0, 0]] where
 M := ![![![149, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC149 : ContainsPrimesAboveP 149 ![I149N0, I149N1, I149N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
    exact isPrimeI149N1
    exact isPrimeI149N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 149 (by decide) (𝕀 ⊙ MulI149N0 ⊙ MulI149N1)
instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6255, 839, -392, -1139, 4876]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![-6255, 839, -392, -1139, 4876]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![0, 0, 151, 0, 0], ![0, 0, 0, 151, 0], ![26, 98, 46, 5, 1]] where
  M :=![![![-6255, 839, -392, -1139, 4876], ![-26544, 6149, -2220, -6754, 28366], ![-143164, 17990, -8705, -25162, 107976], ![-593120, 144572, -51140, -156237, 655108], ![-149410, 34625, -12496, -38025, 159703]]]
  hmulB := by decide  
  f := ![![![35, -19, 0, 3, -10]], ![![-4, 153, -28, -60, 238]], ![![-908, -350, 105, 146, -580]], ![![2232, -112, -228, -295, 1316]], ![![-196, -15, 6, -4, 21]]]
  g := ![![![-881, -3159, -1488, -169, 4876], ![-5060, -18369, -8656, -984, 28366], ![-19540, -69958, -32951, -3742, 107976], ![-116728, -424212, -199908, -22727, 655108], ![-28488, -103419, -48734, -5540, 159703]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 4 2 7 [111, 148, 127, 4, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [42, 136, 15, 88], [82, 99, 88, 29], [23, 66, 48, 34], [0, 1]]
 g := ![![[69, 68, 126, 103], [126, 145, 90, 128], [85, 120, 39, 105], [85, 20, 103], [82, 148, 46, 16], [1], []], ![[82, 36, 62, 26, 128, 139], [143, 48, 47, 99, 103, 124], [114, 147, 96, 139, 38, 85], [59, 80, 43], [105, 89, 133, 57, 80, 138], [14, 49, 88], [70, 52, 43]], ![[38, 124, 60, 36, 118, 58], [8, 119, 53, 146, 12, 68], [97, 41, 80, 148, 17, 62], [84, 114, 55], [3, 138, 44, 19, 45, 22], [54, 112, 127], [134, 79, 86]], ![[124, 4, 18, 32, 136, 62], [148, 46, 22, 130, 77, 37], [108, 89, 14, 134, 29, 128], [118, 106, 100], [126, 98, 43, 127, 119, 32], [82, 95, 123], [112, 150, 99]]]
 h' := ![![[42, 136, 15, 88], [57, 31, 141, 109], [78, 66, 135, 85], [30, 125, 47, 135], [109, 65, 113, 42], [40, 3, 24, 147], [0, 0, 1], [0, 1]], ![[82, 99, 88, 29], [119, 142, 17, 139], [72, 101, 140, 133], [150, 141, 35, 108], [31, 16, 149, 88], [55, 15, 69, 96], [34, 124, 58, 36], [42, 136, 15, 88]], ![[23, 66, 48, 34], [105, 139, 69, 46], [146, 5, 6, 73], [128, 21, 9, 7], [40, 93, 20, 31], [62, 97, 64, 33], [4, 17, 20, 91], [82, 99, 88, 29]], ![[0, 1], [150, 141, 75, 8], [75, 130, 21, 11], [107, 15, 60, 52], [70, 128, 20, 141], [30, 36, 145, 26], [26, 10, 72, 24], [23, 66, 48, 34]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [150, 1, 60], []]
 b := ![[], [], [145, 131, 17, 50], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 4
  hpos := by decide
  P := [111, 148, 127, 4, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-199852025803601, 54231042774868, -13705240532592, -49598533247650, 210927814883136]
  a := ![-351, 864, -91, -433, 1779]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-37642219952087, -136534402753460, -64346918709648, -7312831838830, 210927814883136]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 519885601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-35, 19, 0, -3, 10]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![-35, 19, 0, -3, 10]] 
 ![![151, 0, 0, 0, 0], ![76, 1, 0, 0, 0], ![113, 0, 1, 0, 0], ![19, 0, 0, 1, 0], ![39, 0, 0, 0, 1]] where
  M :=![![![-35, 19, 0, -3, 10], ![4, -153, 28, 60, -238], ![908, 350, -105, -146, 580], ![-2232, 112, 228, 295, -1316], ![-494, 105, 40, 43, -207]]]
  hmulB := by decide  
  f := ![![![6255, -839, 392, 1139, -4876]], ![![3324, -463, 212, 618, -2642]], ![![5629, -747, 351, 1019, -4364]], ![![4715, -1063, 388, 1178, -4952]], ![![2605, -446, 184, 546, -2317]]]
  g := ![![![-12, 19, 0, -3, 10], ![110, -153, 28, 60, -238], ![-223, 350, -105, -146, 580], ![61, 112, 228, 295, -1316], ![-38, 105, 40, 43, -207]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![-6255, 839, -392, -1139, 4876]] ![![-35, 19, 0, -3, 10]]
  ![![151, 0, 0, 0, 0]] where
 M := ![![![-151, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC151 : ContainsPrimesAboveP 151 ![I151N0, I151N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
    exact isPrimeI151N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 151 (by decide) (𝕀 ⊙ MulI151N0)


lemma PB2201I3_primes (p : ℕ) :
  p ∈ Set.range ![107, 109, 113, 127, 131, 137, 139, 149, 151] ↔ Nat.Prime p ∧ 103 < p ∧ p ≤ 151 := by
  rw [← List.mem_ofFn']
  convert primes_range 103 151 (by omega)

def PB2201I3 : PrimesBelowBoundCertificateInterval O 103 151 2201 where
  m := 9
  g := ![2, 3, 3, 2, 2, 3, 2, 3, 2]
  P := ![107, 109, 113, 127, 131, 137, 139, 149, 151]
  hP := PB2201I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1, I109N2]
    · exact ![I113N0, I113N1, I113N2]
    · exact ![I127N0, I127N1]
    · exact ![I131N0, I131N1]
    · exact ![I137N0, I137N1, I137N2]
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1, I149N2]
    · exact ![I151N0, I151N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC107
    · exact PBC109
    · exact PBC113
    · exact PBC127
    · exact PBC131
    · exact PBC137
    · exact PBC139
    · exact PBC149
    · exact PBC151
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![1225043, 11449]
    · exact ![1295029, 109, 109]
    · exact ![12769, 12769, 113]
    · exact ![260144641, 127]
    · exact ![2248091, 17161]
    · exact ![18769, 18769, 137]
    · exact ![373301041, 139]
    · exact ![22201, 22201, 149]
    · exact ![519885601, 151]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
      exact NI109N2
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
      exact NI113N2
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
      exact NI137N2
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
      exact NI139N1
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
      exact NI149N2
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
  β := ![I109N1, I109N2, I113N2, I127N1, I137N2, I139N1, I149N2, I151N1]
  Il := ![[], [I109N1, I109N2], [I113N2], [I127N1], [], [I137N2], [I139N1], [I149N2], [I151N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
