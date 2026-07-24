
import IdealArithmetic.Examples.NF5_3_6075000000_7.RI5_3_6075000000_7
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1052, -131, 124, -165, -517]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![-1052, -131, 124, -165, -517]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![0, 0, 0, 29, 0], ![10, 26, 19, 25, 1]] where
  M :=![![![-1052, -131, 124, -165, -517], ![10857, 3642, -214, -741, 1309], ![-27489, 31, 4811, -7953, -19537], ![61026, 25865, 1295, -9893, -2058], ![-37332, -10069, 1865, -66, -8843]]]
  hmulB := by decide  
  f := ![![![42932, 28557, 5610, -7305, -8977]], ![![188517, 125420, 24642, -32085, -39431]], ![![828051, 550839, 108221, -140913, -173173]], ![![913542, 607733, 119399, -155467, -191058]], ![![1506007, 1001863, 196833, -256292, -314966]]]
  g := ![![![142, 459, 343, 440, -517], ![-77, -1048, -865, -1154, 1309], ![5789, 17517, 12966, 16568, -19537], ![2814, 2737, 1393, 1433, -2058], ![1762, 7581, 5858, 7621, -8843]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 4 2 4 [1, 27, 3, 4, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [28, 24, 7, 12], [27, 28], [28, 5, 22, 17], [0, 1]]
 g := ![![[1, 23], [27, 28, 28], [20, 13, 25, 1], []], ![[25, 25, 21, 24, 18, 15], [28, 13, 16], [27, 10, 10, 26, 2, 11], [23, 4, 28, 25, 27, 17]], ![[13, 6], [25, 26, 28], [28, 17, 19, 28], []], ![[23, 17, 8, 13, 13, 14], [8, 22, 16], [12, 4, 8, 14, 8, 18], [18, 8, 7, 4, 2, 12]]]
 h' := ![![[28, 24, 7, 12], [25, 19, 20], [9, 27, 28, 17], [0, 0, 0, 1], [0, 1]], ![[27, 28], [8, 7, 7, 9], [6, 26, 6, 4], [5, 27, 2, 19], [28, 24, 7, 12]], ![[28, 5, 22, 17], [9, 3, 20], [18, 26, 13, 12], [21, 17, 23, 28], [27, 28]], ![[0, 1], [8, 0, 11, 20], [4, 8, 11, 25], [10, 14, 4, 10], [28, 5, 22, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [10], []]
 b := ![[], [], [19, 0, 15, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 4
  hpos := by decide
  P := [1, 27, 3, 4, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-384701680509085, -236863581439692, -42249010004131, 141013444890133, 142712941711745]
  a := ![0, 14, 13, -137, -247]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-62476934400915, -136117243653278, -94958444914734, -118165865444948, 142712941711745]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 707281 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-42932, -28557, -5610, 7305, 8977]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![-42932, -28557, -5610, 7305, 8977]] 
 ![![29, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![23, 0, 0, 1, 0], ![17, 0, 0, 0, 1]] where
  M :=![![![-42932, -28557, -5610, 7305, 8977], ![-188517, -125420, -24642, 32085, 39431], ![-828051, -550839, -108221, 140913, 173173], ![-913542, -607733, -119399, 155467, 191058], ![228078, 151729, 29809, -38814, -47699]]]
  hmulB := by decide  
  f := ![![![1052, 131, -124, 165, 517]], ![![-193, -103, -14, 54, 44]], ![![1093, 17, -183, 297, 745]], ![![-1270, -788, -143, 472, 481]], ![![1904, 424, -137, 99, 608]]]
  g := ![![![-6839, -28557, -5610, 7305, 8977], ![-30039, -125420, -24642, 32085, 39431], ![-131928, -550839, -108221, 140913, 173173], ![-145552, -607733, -119399, 155467, 191058], ![36338, 151729, 29809, -38814, -47699]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![-1052, -131, 124, -165, -517]] ![![-42932, -28557, -5610, 7305, 8977]]
  ![![29, 0, 0, 0, 0]] where
 M := ![![![-29, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC29 : ContainsPrimesAboveP 29 ![I29N0, I29N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 29 (by decide) (𝕀 ⊙ MulI29N0)
instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-49298, -32724, -6419, 8365, 10273]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![-49298, -32724, -6419, 8365, 10273]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![25, 11, 1, 0, 0], ![9, 3, 0, 1, 0], ![15, 17, 0, 0, 1]] where
  M :=![![![-49298, -32724, -6419, 8365, 10273], ![-215733, -143701, -28251, 36771, 45199], ![-949179, -631044, -123970, 161433, 198401], ![-1046752, -696340, -136788, 178119, 218876], ![261390, 173882, 34142, -44466, -54625]]]
  hmulB := by decide  
  f := ![![![-11070, -2482, 787, -559, -3517]], ![![73857, 20355, -3497, -309, 16793]], ![![5904, 2851, 286, -1327, -809]], ![![14299, 4549, -396, -707, 2182]], ![![25473, 7501, -984, -618, 4947]]]
  g := ![![![-3813, -5221, -6419, 8365, 10273], ![-16722, -22956, -28251, 36771, 45199], ![-73511, -100790, -123970, 161433, 198401], ![-81073, -111191, -136788, 178119, 218876], ![20239, 27753, 34142, -44466, -54625]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [12, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [14, 30], [0, 1]]
 g := ![![[4, 8], [9, 7], [15, 4], [14, 1]], ![[23, 23], [14, 24], [9, 27], [28, 30]]]
 h' := ![![[14, 30], [16, 16], [6, 21], [18, 29], [0, 1]], ![[0, 1], [23, 15], [21, 10], [21, 2], [14, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [29, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [12, 17, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-939515488, -711729303, -166581705, 523030114, 623736368]
  a := ![3, 252, 254, -2387, -4062]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-349622239, -356514166, -166581705, 523030114, 623736368]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2541, -1685, -327, 428, 522]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![-2541, -1685, -327, 428, 522]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![2, 12, 1, 0, 0], ![7, 6, 0, 1, 0], ![28, 10, 0, 0, 1]] where
  M :=![![![-2541, -1685, -327, 428, 522], ![-10962, -7340, -1459, 1890, 2338], ![-49098, -32435, -6312, 8256, 10094], ![-53522, -35683, -7025, 9139, 11242], ![13254, 8897, 1763, -2286, -2821]]]
  hmulB := by decide  
  f := ![![![48349, 12031, -2887, 1174, 13266]], ![![-278586, -69332, 16631, -6756, -76426]], ![![-52948, -13179, 3160, -1282, -14522]], ![![-76965, -19156, 4594, -1865, -21112]], ![![-7334, -1827, 437, -176, -2009]]]
  g := ![![![-629, -179, -327, 428, 522], ![-2798, -792, -1459, 1890, 2338], ![-12158, -3457, -6312, 8256, 10094], ![-13491, -3827, -7025, 9139, 11242], ![3378, 957, 1763, -2286, -2821]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P1 : CertificateIrreducibleZModOfList' 31 2 2 4 [24, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 30], [0, 1]]
 g := ![![[14, 25], [21, 25], [13, 1], [5, 1]], ![[15, 6], [22, 6], [18, 30], [10, 30]]]
 h' := ![![[5, 30], [23, 5], [29, 26], [4, 1], [0, 1]], ![[0, 1], [17, 26], [4, 5], [9, 30], [5, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [27, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N1 : CertifiedPrimeIdeal' SI31N1 31 where
  n := 2
  hpos := by decide
  P := [24, 26, 1]
  hirr := P31P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4199880, -3245281, -774808, 2406321, 2900982]
  a := ![1, 17, 17, -162, -279]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3249097, -1206301, -774808, 2406321, 2900982]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N1 B_one_repr
lemma NI31N1 : Nat.card (O ⧸ I31N1) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N1

def I31N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![18560958, 4619191, -1108146, 450389, 5092413]] i)))

def SI31N2: IdealEqSpanCertificate' Table ![![18560958, 4619191, -1108146, 450389, 5092413]] 
 ![![31, 0, 0, 0, 0], ![8, 1, 0, 0, 0], ![29, 0, 1, 0, 0], ![24, 0, 0, 1, 0], ![20, 0, 0, 0, 1]] where
  M :=![![![18560958, 4619191, -1108146, 450389, 5092413], ![-106940673, -26613002, 6385094, -2595375, -29341445], ![616170345, 153342613, -36787815, 14952189, 169054865], ![-404125358, -100569265, 24129253, -9808031, -110880854], ![462489702, 115095293, -27613267, 11223738, 126892475]]]
  hmulB := by decide  
  f := ![![![20626, -31211, 3056, -413, -12477]], ![![13775, -3852, -402, 365, -589]], ![![-35953, -43704, 8971, -3286, -23486]], ![![40310, -20321, 233, 555, -6142]], ![![-10960, -23775, 4211, -1354, -11851]]]
  g := ![![![-3190772, 4619191, -1108146, 450389, 5092413], ![18384307, -26613002, 6385094, -2595375, -29341445], ![-105924960, 153342613, -36787815, 14952189, 169054865], ![69473879, -100569265, 24129253, -9808031, -110880854], ![-79506681, 115095293, -27613267, 11223738, 126892475]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N2 : Nat.card (O ⧸ I31N2) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N2)

lemma isPrimeI31N2 : Ideal.IsPrime I31N2 := prime_ideal_of_norm_prime hp31.out _ NI31N2
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![-49298, -32724, -6419, 8365, 10273]] ![![-2541, -1685, -327, 428, 522]]
  ![![487593580, 324372141, 63728664, -82979511, -101976457]] where
 M := ![![![487593580, 324372141, 63728664, -82979511, -101976457]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI31N1 : IdealMulLeCertificate' Table 
  ![![487593580, 324372141, 63728664, -82979511, -101976457]] ![![18560958, 4619191, -1108146, 450389, 5092413]]
  ![![31, 0, 0, 0, 0]] where
 M := ![![![405162321951, 269533788044, 52954654150, -68950983184, -84736303526]]]
 hmul := by decide  
 g := ![![![![13069752321, 8694638324, 1708214650, -2224225264, -2733429146]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N1, I31N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N1
    exact isPrimeI31N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0 ⊙ MulI31N1)
instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1582028, -392758, 94889, -38885, -435207]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![-1582028, -392758, 94889, -38885, -435207]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![30, 26, 1, 1, 0], ![26, 27, 27, 0, 1]] where
  M :=![![![-1582028, -392758, 94889, -38885, -435207], ![9139347, 2278831, -543651, 219369, 2502059], ![-52543239, -13054902, 3146764, -1287585, -14443247], ![34560176, 8625972, -2051828, 822753, 9448684], ![-39490560, -9832766, 2355460, -955656, -10828685]]]
  hmulB := by decide  
  f := ![![![-827820, 499200, -12467, -14791, 152337]], ![![-3199077, -2171595, 538925, -207921, -1273433]], ![![26742093, 7930816, -3041524, 1362261, 6003137]], ![![-2537801, -960562, 318408, -136922, -664115]], ![![16945770, 4608917, -1867685, 847912, 3614839]]]
  g := ![![![294592, 334293, 321199, -38885, -435207], ![-1689061, -1918388, -1846449, 219369, 2502059], ![9773209, 11091621, 10659514, -1287585, -14443247], ![-6372654, -7240002, -6972677, 822753, 9448684], ![7316890, 8307805, 7991503, -955656, -10828685]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [21, 1, 34, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 5, 36], [17, 31, 1], [0, 1]]
 g := ![![[13, 19, 9], [18, 33], [1, 30, 27], [3, 1], []], ![[30, 28, 17, 10], [21, 26], [22, 2, 7, 16], [32, 36], [30, 1]], ![[20, 6, 27, 10], [20, 3], [7, 18, 11, 34], [24, 25], [28, 1]]]
 h' := ![![[23, 5, 36], [26, 26, 34], [16, 8, 25], [11, 13, 8], [0, 0, 1], [0, 1]], ![[17, 31, 1], [2, 0, 29], [6, 1, 27], [20, 17, 13], [10, 31, 31], [23, 5, 36]], ![[0, 1], [33, 11, 11], [3, 28, 22], [23, 7, 16], [34, 6, 5], [17, 31, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26, 20], []]
 b := ![[], [31, 9, 20], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [21, 1, 34, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9486806970077, -6107839068034, -1165414564626, 3790913870756, 4017291882478]
  a := ![1, -88, -84, 851, 1501]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6153076001005, -5760499473908, -3065492142224, 3790913870756, 4017291882478]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 50653 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-316, -139, -32, 41, 59]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-316, -139, -32, 41, 59]] 
 ![![37, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![30, 0, 1, 0, 0], ![22, 0, 0, 1, 0], ![30, 0, 0, 0, 1]] where
  M :=![![![-316, -139, -32, 41, 59], ![-1239, -856, -116, 177, 161], ![-3381, -2749, -801, 897, 1351], ![-6062, -3665, -627, 873, 994], ![2076, 1009, 103, -192, -155]]]
  hmulB := by decide  
  f := ![![![299268, 74489, -17862, 7249, 82087]], ![![26205, 6527, -1562, 630, 7180]], ![![511179, 127241, -30507, 12375, 140201]], ![![1934, 517, -99, 9, 468]], ![![444162, 110543, -26515, 10770, 121849]]]
  g := ![![![-21, -139, -32, 41, 59], ![33, -856, -116, 177, 161], ![-402, -2749, -801, 897, 1351], ![-89, -3665, -627, 873, 994], ![-33, 1009, 103, -192, -155]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7255, 3549, 9, -160, 960]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![-7255, 3549, 9, -160, 960]] 
 ![![37, 0, 0, 0, 0], ![20, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![35, 0, 0, 0, 1]] where
  M :=![![![-7255, 3549, 9, -160, 960], ![-20160, -15744, 3691, -1386, -8960], ![188160, 58175, -21740, 9672, 43316], ![-92246, -14835, 8699, -4239, -15022], ![93834, 15317, -8881, 4320, 15383]]]
  hmulB := by decide  
  f := ![![![2040561, 1357459, 266691, -347258, -426744]], ![![1345212, 894892, 175815, -228928, -281332]], ![![1449903, 964522, 189491, -246740, -303212]], ![![1559705, 1037598, 203856, -265443, -326214]], ![![1637277, 1089162, 213976, -278620, -342385]]]
  g := ![![![-2994, 3549, 9, -160, 960], ![16005, -15744, 3691, -1386, -8960], ![-65052, 58175, -21740, 9672, 43316], ![18892, -14835, 8699, -4239, -15022], ![-19432, 15317, -8881, 4320, 15383]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![-1582028, -392758, 94889, -38885, -435207]] ![![-316, -139, -32, 41, 59]]
  ![![-2040561, -1357459, -266691, 347258, 426744]] where
 M := ![![![-2040561, -1357459, -266691, 347258, 426744]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![-2040561, -1357459, -266691, 347258, 426744]] ![![-7255, 3549, 9, -160, 960]]
  ![![37, 0, 0, 0, 0]] where
 M := ![![![-37, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1, I37N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
    exact isPrimeI37N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0 ⊙ MulI37N1)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1307411, -869769, -170885, 222454, 273402]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![-1307411, -869769, -170885, 222454, 273402]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![10, 18, 15, 1, 0], ![23, 7, 16, 0, 1]] where
  M :=![![![-1307411, -869769, -170885, 222454, 273402], ![-5741442, -3819598, -750453, 976776, 1200542], ![-25211382, -16772643, -3295468, 4288266, 5271070], ![-27809446, -18501449, -3635227, 4729149, 5813486], ![6946356, 4621147, 907927, -1181880, -1452577]]]
  hmulB := by decide  
  f := ![![![-21147, -4583, 2165, -1016, -3978]], ![![83538, 13506, -7897, 3846, 13622]], ![![-286062, -35009, 25454, -12768, -41510]], ![![-71582, -7922, 6251, -3165, -10004]], ![![-110847, -14008, 9927, -4964, -16285]]]
  g := ![![![-239517, -165555, -192247, 222454, 273402], ![-1051748, -726960, -844165, 976776, 1200542], ![-4617772, -3191681, -3706258, 4288266, 5271070], ![-5092954, -3520013, -4087518, 4729149, 5813486], ![1272547, 879586, 1021399, -1181880, -1452577]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [36, 4, 18, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 10, 39], [18, 30, 2], [0, 1]]
 g := ![![[1, 1, 16], [8, 21], [14, 10], [33, 23, 1], []], ![[29, 11, 37, 37], [20, 8], [2, 33], [22, 39, 13, 4], [11, 4]], ![[31, 13, 38, 21], [32, 25], [19, 9], [39, 10, 9, 36], [7, 4]]]
 h' := ![![[5, 10, 39], [38, 10, 37], [30, 1, 29], [1, 24, 16], [0, 0, 1], [0, 1]], ![[18, 30, 2], [14, 1, 24], [18, 0, 7], [7, 21, 22], [39, 35, 30], [5, 10, 39]], ![[0, 1], [12, 30, 21], [4, 40, 5], [27, 37, 3], [31, 6, 10], [18, 30, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 36], []]
 b := ![[], [35, 37, 18], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [36, 4, 18, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![68700654085, 58580071747, 15082537982, -42743187867, -54334179214]
  a := ![-1, 17, 10, -189, -406]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![42580942797, 29470651411, 37209200571, -42743187867, -54334179214]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 68921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![21147, 4583, -2165, 1016, 3978]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![21147, 4583, -2165, 1016, 3978]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![13, 31, 1, 0, 0], ![26, 23, 0, 1, 0], ![39, 32, 0, 0, 1]] where
  M :=![![![21147, 4583, -2165, 1016, 3978], ![-83538, -13506, 7897, -3846, -13622], ![286062, 35009, -25454, 12768, 41510], ![-63854, -3055, 5023, -2687, -7070], ![66120, 3317, -5227, 2790, 7385]]]
  hmulB := by decide  
  f := ![![![1307411, 869769, 170885, -222454, -273402]], ![![5741442, 3819598, 750453, -976776, -1200542]], ![![5370547, 3572858, 701976, -913664, -1122978]], ![![4728178, 3145517, 618016, -804361, -988644]], ![![5555337, 3695780, 726124, -945138, -1161645]]]
  g := ![![![-3226, -1926, -2165, 1016, 3978], ![10855, 6489, 7897, -3846, -13622], ![-32534, -19461, -25454, 12768, 41510], ![5279, 3153, 5023, -2687, -7070], ![-5524, -3296, -5227, 2790, 7385]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P1 : CertificateIrreducibleZModOfList' 41 2 2 5 [12, 35, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 40], [0, 1]]
 g := ![![[20, 10], [33], [31], [31, 36], [1]], ![[39, 31], [33], [31], [1, 5], [1]]]
 h' := ![![[6, 40], [9, 16], [6, 19], [38, 21], [29, 6], [0, 1]], ![[0, 1], [23, 25], [38, 22], [0, 20], [24, 35], [6, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [20, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N1 : CertifiedPrimeIdeal' SI41N1 41 where
  n := 2
  hpos := by decide
  P := [12, 35, 1]
  hirr := P41P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3852588, 878260, -304232, 281274, 1471316]
  a := ![0, 0, 12, 42, 196]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1387484, -1054682, -304232, 281274, 1471316]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N1 B_one_repr
lemma NI41N1 : Nat.card (O ⧸ I41N1) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![-1307411, -869769, -170885, 222454, 273402]] ![![21147, 4583, -2165, 1016, 3978]]
  ![![41, 0, 0, 0, 0]] where
 M := ![![![-41, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0, 0, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0, 0, 0]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![0, 0, 0, 0, 43]] where
  M :=![![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![0, 0, 0, 0, 43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 5 2 5 [35, 26, 20, 3, 24, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 35, 4, 4, 2], [34, 31, 32, 2, 26], [2, 9, 8, 42, 26], [42, 10, 42, 38, 32], [0, 1]]
 g := ![![[41, 23, 32, 2, 23], [31, 25, 39, 11, 13], [25, 30, 37, 17], [1], []], ![[35, 20, 14, 1, 25, 21, 0, 42], [18, 27, 4, 37, 1, 3, 41, 34], [21, 28, 0, 14], [30, 21, 30, 10, 12, 30, 35, 22], [40, 5, 6, 4]], ![[31, 14, 15, 35, 4, 16, 8, 42], [19, 9, 39, 21, 41, 40, 40, 33], [41, 2, 28, 35], [11, 14, 20, 10, 18, 41, 12, 3], [26, 36, 5, 31]], ![[42, 8, 26, 1, 1, 37, 3, 3], [36, 31, 11, 21, 6, 31, 27, 19], [25, 2, 40, 40], [17, 16, 35, 11, 36, 33, 17, 8], [4, 35, 21, 31]], ![[26, 24, 15, 14, 34, 10, 32, 26], [29, 15, 23, 41, 7, 42, 33, 20], [14, 21, 39, 6], [1, 40, 34, 8, 39, 28, 9, 29], [23, 4, 1, 35]]]
 h' := ![![[27, 35, 4, 4, 2], [33, 32, 9, 13, 18], [6, 34, 17, 7, 20], [8, 17, 23, 40, 19], [0, 0, 1], [0, 1]], ![[34, 31, 32, 2, 26], [15, 6, 34, 2, 8], [0, 16, 11, 20, 19], [2, 20, 7, 9, 33], [17, 30, 0, 23, 22], [27, 35, 4, 4, 2]], ![[2, 9, 8, 42, 26], [23, 8, 18, 16, 34], [0, 19, 28, 13, 37], [39, 33, 14, 16, 11], [31, 0, 1, 21, 31], [34, 31, 32, 2, 26]], ![[42, 10, 42, 38, 32], [38, 26, 24, 35, 31], [2, 31, 14, 23, 3], [19, 39, 40, 31, 30], [36, 40, 22, 33, 13], [2, 9, 8, 42, 26]], ![[0, 1], [37, 14, 1, 20, 38], [18, 29, 16, 23, 7], [11, 20, 2, 33, 36], [13, 16, 19, 9, 20], [42, 10, 42, 38, 32]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27, 19, 31, 37], [], [], []]
 b := ![[], [16, 20, 15, 29, 3], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 5
  hpos := by decide
  P := [35, 26, 20, 3, 24, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![18007300080065690839, 11145478837961926276, 2004487498293594568, -6655257264622538412, -6775291003473420372]
  a := ![13, 18, 13, -191, -387]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![418774420466643973, 259197182278184332, 46615988332409176, -154773424758663684, -157564907057521404]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 147008443 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def PBC43 : ContainsPrimesAboveP 43 ![I43N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![43, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 43 (by decide) 𝕀

instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17535, 38020, 20388, -15266, -49078]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-17535, 38020, 20388, -15266, -49078]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![38, 5, 1, 32, 1]] where
  M :=![![![-17535, 38020, 20388, -15266, -49078], ![1030638, 419045, 12510, -15066, 129822], ![-2726262, -135204, 409091, -60534, -1119678], ![3181892, 1191820, -10360, 295601, 813456], ![-3386802, -1061928, 102270, -9840, -704767]]]
  hmulB := by decide  
  f := ![![![12542467, 524972, -969136, 521470, 1364858]], ![![-28662018, 706411, 1941774, -1121586, -2253426]], ![![47321946, -9201372, -2055551, 1556370, 71778]], ![![10745756, 4913132, -1469328, 610863, 3196144]], ![![15194052, 3542741, -1590185, 738580, 2973365]]]
  g := ![![![39307, 6030, 1478, 33090, -49078], ![-83034, -4895, -2496, -88710, 129822], ![847266, 116238, 32527, 761046, -1119678], ![-589988, -61180, -17528, -547553, 813456], ![497752, 52381, 17171, 479632, -704767]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 4 2 5 [42, 12, 14, 38, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 20, 29, 30], [27, 12, 1, 32], [22, 14, 17, 32], [0, 1]]
 g := ![![[39, 41, 20, 24], [28, 45, 37, 36], [21, 34, 7, 24], [9, 1], []], ![[3, 11, 21, 21, 39, 11], [19, 45, 1, 23, 38, 5], [37, 12, 4, 12, 32, 23], [29, 15, 41, 8, 29, 46], [28, 17, 7]], ![[11, 12, 19, 17, 10, 34], [7, 29, 10, 1, 18, 21], [12, 38, 21, 9, 17, 36], [27, 0, 24, 25, 7, 27], [17, 21, 37]], ![[29, 4, 10, 19, 2, 18], [30, 45, 27, 28, 13, 24], [16, 11, 22, 16, 5, 18], [32, 2, 22, 9, 19, 34], [14, 11, 37]]]
 h' := ![![[7, 20, 29, 30], [46, 10, 28, 20], [11, 16, 27, 6], [45, 38, 3, 20], [0, 0, 1], [0, 1]], ![[27, 12, 1, 32], [29, 36, 22, 36], [45, 30, 15, 33], [11, 12, 20, 21], [1, 29, 10, 6], [7, 20, 29, 30]], ![[22, 14, 17, 32], [2, 43, 5, 2], [45, 45, 3, 14], [6, 2, 29, 17], [15, 32, 34, 39], [27, 12, 1, 32]], ![[0, 1], [38, 5, 39, 36], [24, 3, 2, 41], [10, 42, 42, 36], [37, 33, 2, 2], [22, 14, 17, 32]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [39, 32, 2], []]
 b := ![[], [], [9, 18, 7, 44], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 4
  hpos := by decide
  P := [42, 12, 14, 38, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-25058854833008, -15068256380256, -2585432673605, 8806907186484, 8667462185050]
  a := ![-1, 8, 10, -69, -97]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-7540902507764, -1242671644798, -239423294865, -5713869845428, 8667462185050]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 4879681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-12542467, -524972, 969136, -521470, -1364858]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-12542467, -524972, 969136, -521470, -1364858]] 
 ![![47, 0, 0, 0, 0], ![29, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![45, 0, 0, 1, 0], ![28, 0, 0, 0, 1]] where
  M :=![![![-12542467, -524972, 969136, -521470, -1364858], ![28662018, -706411, -1941774, 1121586, 2253426], ![-47321946, 9201372, 2055551, -1556370, -71778], ![-10745756, -4913132, 1469328, -610863, -3196144], ![10369350, 4991016, -1453650, 598656, 3197705]]]
  hmulB := by decide  
  f := ![![![17535, -38020, -20388, 15266, 49078]], ![![-11109, -32375, -12846, 9740, 27520]], ![![59871, -1168, -10873, 2912, 29044]], ![![-50911, -61760, -19300, 8327, 29682]], ![![82506, -56, -14322, 9304, 44233]]]
  g := ![![![1266345, -524972, 969136, -521470, -1364858], ![-1164053, -706411, -1941774, 1121586, 2253426], ![-5370065, 9201372, 2055551, -1556370, -71778], ![5135517, -4913132, 1469328, -610863, -3196144], ![-5182492, 4991016, -1453650, 598656, 3197705]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-17535, 38020, 20388, -15266, -49078]] ![![-12542467, -524972, 969136, -521470, -1364858]]
  ![![47, 0, 0, 0, 0]] where
 M := ![![![-47, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3712, -125, 282, -153, -391]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-3712, -125, 282, -153, -391]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![9, 45, 7, 1, 0], ![24, 33, 41, 0, 1]] where
  M :=![![![-3712, -125, 282, -153, -391], ![8211, -322, -536, 315, 595], ![-12495, 3077, 435, -381, 245], ![-3654, -1487, 487, -211, -994], ![3534, 1511, -481, 204, 985]]]
  hmulB := by decide  
  f := ![![![-25616, -17041, -3348, 4359, 5357]], ![![-112497, -74840, -14704, 19143, 23527]], ![![-494067, -328679, -64575, 84063, 103313]], ![![-175404, -116689, -22926, 29846, 36681]], ![![-461280, -306868, -60290, 78486, 96459]]]
  g := ![![![133, 371, 328, -153, -391], ![-168, -644, -512, 315, 595], ![-282, 229, -131, -381, 245], ![417, 770, 806, -211, -994], ![-414, -758, -798, 204, 985]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [17, 52, 33, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [33, 43, 21], [40, 9, 32], [0, 1]]
 g := ![![[23, 29, 6], [51, 44], [19, 24, 44], [37, 29], [1]], ![[25, 19, 4, 34], [38, 43], [22, 21, 42, 22], [24, 15], [5, 13, 5, 39]], ![[13, 3, 37, 20], [6, 6], [4, 11, 43, 48], [4, 28], [8, 18, 50, 14]]]
 h' := ![![[33, 43, 21], [6, 49, 18], [48, 42, 16], [31, 40, 37], [36, 1, 20], [0, 1]], ![[40, 9, 32], [19, 15, 25], [20, 23, 19], [9, 5, 7], [24, 27, 42], [33, 43, 21]], ![[0, 1], [47, 42, 10], [34, 41, 18], [39, 8, 9], [52, 25, 44], [40, 9, 32]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39, 3], []]
 b := ![[], [49, 24, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [17, 52, 33, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![13364561, -401666276, -188781468, 435023916, 720871088]
  a := ![3, -3, 1, 39, 98]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-400052015, -825782800, -618672896, 435023916, 720871088]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 148877 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![25616, 17041, 3348, -4359, -5357]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![25616, 17041, 3348, -4359, -5357]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![15, 9, 1, 0, 0], ![9, 36, 0, 1, 0], ![40, 42, 0, 0, 1]] where
  M :=![![![25616, 17041, 3348, -4359, -5357], ![112497, 74840, 14704, -19143, -23527], ![494067, 328679, 64575, -84063, -103313], ![545034, 362595, 71241, -92731, -113974], ![-136092, -90539, -17789, 23160, 28465]]]
  hmulB := by decide  
  f := ![![![3712, 125, -282, 153, 391]], ![![-8211, 322, 536, -315, -595]], ![![-108, 32, 3, -3, 5]], ![![-4878, 268, 307, -184, -319]], ![![-3772, 321, 221, -138, -195]]]
  g := ![![![4319, 6959, 3348, -4359, -5357], ![18968, 30562, 14704, -19143, -23527], ![83293, 134206, 64575, -84063, -103313], ![91886, 148050, 71241, -92731, -113974], ![-22949, -36976, -17789, 23160, 28465]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P1 : CertificateIrreducibleZModOfList' 53 2 2 5 [13, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [38, 52], [0, 1]]
 g := ![![[46, 49], [49], [], [], [38, 1]], ![[0, 4], [49], [], [], [23, 52]]]
 h' := ![![[38, 52], [52, 7], [0, 46], [24], [36], [0, 1]], ![[0, 1], [0, 46], [52, 7], [24], [36], [38, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [33, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N1 : CertifiedPrimeIdeal' SI53N1 53 where
  n := 2
  hpos := by decide
  P := [13, 15, 1]
  hirr := P53P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1518170, -2251640, -797731, 2118477, 3116735]
  a := ![1, -14, -10, 149, 303]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2514866, -3815851, -797731, 2118477, 3116735]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N1 B_one_repr
lemma NI53N1 : Nat.card (O ⧸ I53N1) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-3712, -125, 282, -153, -391]] ![![25616, 17041, 3348, -4359, -5357]]
  ![![53, 0, 0, 0, 0]] where
 M := ![![![-53, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9874, 5283, 578, -699, 237]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-9874, 5283, 578, -699, 237]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![38, 32, 47, 9, 1]] where
  M :=![![![-9874, 5283, 578, -699, 237], ![-4977, -11886, 4826, -2823, -11445], ![240345, 96025, -18715, 3549, 40593], ![-62790, 11723, 16217, -12679, -27454], ![98358, 11385, -11991, 7002, 20779]]]
  hmulB := by decide  
  f := ![![![2362, 2477, 732, -1953, -2673]], ![![56133, 27640, 2966, -13185, -8631]], ![![181251, 144031, 34893, -100869, -124173]], ![![504378, 280081, 41311, -152231, -133322]], ![![251473, 173401, 36197, -111822, -125816]]]
  g := ![![![-320, -39, -179, -48, 237], ![7287, 6006, 9199, 1698, -11445], ![-22071, -20389, -32654, -6132, 40593], ![16618, 15089, 22145, 3973, -27454], ![-11716, -11077, -16756, -3051, 20779]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 4 2 5 [28, 44, 24, 43, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [47, 45, 22, 2], [45, 34, 16, 13], [42, 38, 21, 44], [0, 1]]
 g := ![![[51, 38, 53, 1], [44, 21, 18, 17], [14, 26, 26], [39, 55, 16, 1], []], ![[38, 26, 8, 24, 46, 33], [25, 1, 18, 34, 53, 13], [10, 47, 35], [44, 1, 31, 19, 20, 54], [40, 19, 44, 25, 38, 8]], ![[37, 16, 20, 19, 56, 13], [35, 14, 33, 11, 47, 33], [16, 0, 21], [43, 24, 40, 2, 44, 8], [3, 13, 49, 18, 17, 14]], ![[14, 49, 20, 2, 10, 18], [25, 30, 48, 51, 3, 58], [49, 34, 25], [37, 36, 4, 23, 13, 32], [25, 6, 28, 16, 0, 47]]]
 h' := ![![[47, 45, 22, 2], [7, 11, 11, 58], [36, 24, 6, 28], [29, 48, 31, 47], [0, 0, 0, 1], [0, 1]], ![[45, 34, 16, 13], [58, 43, 30, 20], [24, 57, 22, 6], [3, 17, 2, 34], [43, 38, 10, 26], [47, 45, 22, 2]], ![[42, 38, 21, 44], [10, 48, 48, 1], [50, 18, 25, 23], [47, 24, 39, 32], [4, 26, 22, 39], [45, 34, 16, 13]], ![[0, 1], [18, 16, 29, 39], [44, 19, 6, 2], [0, 29, 46, 5], [51, 54, 27, 52], [42, 38, 21, 44]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [56, 8, 34], []]
 b := ![[], [], [15, 4, 5, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 4
  hpos := by decide
  P := [28, 44, 24, 43, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2026181918, 469716832, -136581480, 85144980, 614811134]
  a := ![4, 0, -1, -3, -14]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-361637986, -325495584, -492079742, -92341614, 614811134]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 12117361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2362, -2477, -732, 1953, 2673]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![-2362, -2477, -732, 1953, 2673]] 
 ![![59, 0, 0, 0, 0], ![58, 1, 0, 0, 0], ![58, 0, 1, 0, 0], ![19, 0, 0, 1, 0], ![48, 0, 0, 0, 1]] where
  M :=![![![-2362, -2477, -732, 1953, 2673], ![-56133, -27640, -2966, 13185, 8631], ![-181251, -144031, -34893, 100869, 124173], ![-504378, -280081, -41311, 152231, 133322], ![107304, 38133, -1125, -9558, 9349]]]
  hmulB := by decide  
  f := ![![![9874, -5283, -578, 699, -237]], ![![9791, -4992, -650, 735, -39]], ![![5633, -6821, -251, 627, -921]], ![![4244, -1900, -461, 440, 389]], ![![6366, -4491, -267, 450, -545]]]
  g := ![![![311, -2477, -732, 1953, 2673], ![17868, -27640, -2966, 13185, 8631], ![39314, -144031, -34893, 100869, 124173], ![149907, -280081, -41311, 152231, 133322], ![-39090, 38133, -1125, -9558, 9349]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-9874, 5283, 578, -699, 237]] ![![-2362, -2477, -732, 1953, 2673]]
  ![![59, 0, 0, 0, 0]] where
 M := ![![![-59, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11183, 1032, -1150, 594, 1162]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![11183, 1032, -1150, 594, 1162]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![20, 19, 9, 1, 0], ![32, 59, 51, 0, 1]] where
  M :=![![![11183, 1032, -1150, 594, 1162], ![-24402, 1281, 2738, -1554, 182], ![-3822, -27224, -2641, 2442, -23030], ![75264, 25080, -4488, 1577, 24920], ![-87780, -28412, 5212, -1860, -28535]]]
  hmulB := by decide  
  f := ![![![-502681, -334384, -65690, 85614, 105182]], ![![-2208822, -1469243, -288618, 376386, 462322]], ![![-9708762, -6457488, -1268393, 1655766, 2033150]], ![![-2460992, -1636893, -321531, 419597, 515284]], ![![-10473476, -6966241, -1368353, 1785828, 2193025]]]
  g := ![![![-621, -1292, -1078, 594, 1162], ![14, 329, 122, -1554, 182], ![11218, 21068, 18851, 2442, -23030], ![-12356, -24183, -21141, 1577, 24920], ![14140, 27713, 24217, -1860, -28535]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [29, 56, 51, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [43, 3, 48], [28, 57, 13], [0, 1]]
 g := ![![[49, 35, 47], [16, 1], [13, 59, 3], [26, 2, 39], [1]], ![[54, 55, 14, 60], [1, 19], [31, 3, 10, 20], [59, 40, 10, 25], [27, 16, 47, 60]], ![[4, 40, 46, 4], [17, 56], [9, 36, 16, 52], [25, 50, 3, 22], [60, 13, 56, 1]]]
 h' := ![![[43, 3, 48], [23, 56, 13], [50, 58, 60], [39, 59, 8], [32, 5, 10], [0, 1]], ![[28, 57, 13], [13, 59, 13], [46, 51, 43], [51, 2, 55], [34, 25, 17], [43, 3, 48]], ![[0, 1], [10, 7, 35], [36, 13, 19], [33, 0, 59], [21, 31, 34], [28, 57, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49, 47], []]
 b := ![[], [45, 40, 13], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [29, 56, 51, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![21893333697, 13152443336, 2253945532, -7776929452, -7646601488]
  a := ![7, 13, 14, -107, -136]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![6920051973, 10033829356, 7577426008, -7776929452, -7646601488]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 226981 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5676, 2112, -707, 305, 1469]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![5676, 2112, -707, 305, 1469]] 
 ![![61, 0, 0, 0, 0], ![15, 1, 0, 0, 0], ![19, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![60, 0, 0, 0, 1]] where
  M :=![![![5676, 2112, -707, 305, 1469], ![-30849, -7143, 3221, -1497, -6013], ![126273, 21544, -12088, 5853, 21133], ![-37016, -3624, 3152, -1607, -4956], ![38046, 3790, -3254, 1662, 5137]]]
  hmulB := by decide  
  f := ![![![809572, 201770, -48199, 19507, 221773]], ![![122727, 30637, -7284, 2934, 33562]], ![![692581, 172544, -41265, 16720, 189804]], ![![-261920, -65068, 15690, -6409, -71994]], ![![1126644, 280646, -67144, 27216, 308803]]]
  g := ![![![-1661, 2112, -707, 305, 1469], ![6211, -7143, 3221, -1497, -6013], ![-20441, 21544, -12088, 5853, 21133], ![4230, -3624, 3152, -1607, -4956], ![-4402, 3790, -3254, 1662, 5137]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2249, -560, 134, -54, -616]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![-2249, -560, 134, -54, -616]] 
 ![![61, 0, 0, 0, 0], ![51, 1, 0, 0, 0], ![22, 0, 1, 0, 0], ![22, 0, 0, 1, 0], ![46, 0, 0, 0, 1]] where
  M :=![![![-2249, -560, 134, -54, -616], ![12936, 3215, -774, 318, 3556], ![-74676, -18612, 4445, -1782, -20440], ![48804, 12102, -2934, 1231, 13468], ![-55986, -13930, 3344, -1362, -15367]]]
  hmulB := by decide  
  f := ![![![36331, 24228, 4762, -6198, -7616]], ![![32997, 21999, 4324, -5628, -6916]], ![![24622, 16400, 3221, -4194, -5152]], ![![25798, 17186, 3378, -4397, -5404]], ![![24232, 16162, 3176, -4134, -5079]]]
  g := ![![![867, -560, 134, -54, -616], ![-4993, 3215, -774, 318, 3556], ![28790, -18612, 4445, -1782, -20440], ![-18860, 12102, -2934, 1231, 13468], ![21602, -13930, 3344, -1362, -15367]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![11183, 1032, -1150, 594, 1162]] ![![5676, 2112, -707, 305, 1469]]
  ![![-91353462, -6277356, 7410031, -3888353, -11055209]] where
 M := ![![![-91353462, -6277356, 7410031, -3888353, -11055209]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![-91353462, -6277356, 7410031, -3888353, -11055209]] ![![-2249, -560, 134, -54, -616]]
  ![![61, 0, 0, 0, 0]] where
 M := ![![![68335128, 2955572, -5293763, 2844613, 7479515]]]
 hmul := by decide  
 g := ![![![![1120248, 48452, -86783, 46633, 122615]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1, I61N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
    exact isPrimeI61N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0 ⊙ MulI61N1)


lemma PB3811I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB3811I1 : PrimesBelowBoundCertificateInterval O 23 61 3811 where
  m := 9
  g := ![2, 3, 3, 2, 1, 2, 2, 2, 3]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB3811I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0, I29N1]
    · exact ![I31N0, I31N1, I31N2]
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0, I41N1]
    · exact ![I43N0]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1, I61N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC29
    · exact PBC31
    · exact PBC37
    · exact PBC41
    · exact PBC43
    · exact PBC47
    · exact PBC53
    · exact PBC59
    · exact PBC61
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![707281, 29]
    · exact ![961, 961, 31]
    · exact ![50653, 37, 37]
    · exact ![68921, 1681]
    · exact ![147008443]
    · exact ![4879681, 47]
    · exact ![148877, 2809]
    · exact ![12117361, 59]
    · exact ![226981, 61, 61]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
      exact NI31N2
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
      exact NI37N2
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
      exact NI61N2
  β := ![I29N1, I31N0, I31N1, I31N2, I37N1, I37N2, I41N1, I47N1, I53N1, I59N1, I61N1, I61N2]
  Il := ![[I29N1], [I31N0, I31N1, I31N2], [I37N1, I37N2], [I41N1], [], [I47N1], [I53N1], [I59N1], [I61N1, I61N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
