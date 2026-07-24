
import IdealArithmetic.Examples.NF5_1_24300000_2.RI5_1_24300000_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1447886, 344120, 596302, 148779, 707260]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![1447886, 344120, 596302, 148779, 707260]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![0, 0, 67, 0, 0], ![0, 0, 0, 67, 0], ![2, 1, 17, 30, 1]] where
  M :=![![![1447886, 344120, 596302, 148779, 707260], ![3275377, 778447, 1348938, 336565, 1599934], ![7409431, 1761012, 3051511, 761377, 3619324], ![6743025, 1602612, 2777076, 692878, 3293826], ![-73489, -17482, -30266, -7555, -35907]]]
  hmulB := by decide  
  f := ![![![-204, -136, 64, 41, 134]], ![![659, -367, 80, -47, 380]], ![![1379, -68, -81, -173, 98]], ![![-393, 648, -198, -20, -660]], ![![163, 269, -107, -51, -267]]]
  g := ![![![498, -5420, -170554, -314463, 707260], ![1127, -12261, -385820, -711365, 1599934], ![2549, -27736, -872791, -1609229, 3619324], ![2319, -25242, -794298, -1464506, 3293826], ![-25, 275, 8659, 15965, -35907]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 4 2 6 [41, 18, 30, 51, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 8, 15, 29], [19, 19, 7, 36], [27, 39, 45, 2], [0, 1]]
 g := ![![[4, 33, 4, 23], [7, 43, 55, 55], [49, 43, 21], [7, 54, 55], [1], []], ![[5, 66, 32, 9, 17, 33], [41, 59, 31, 44, 8, 21], [21, 29, 1], [50, 52, 9], [57, 37, 60], [57, 55, 37]], ![[27, 36, 48, 43, 23, 35], [41, 66, 55, 2, 6, 4], [13, 19, 59], [15, 52, 19], [16, 60, 35], [6, 1, 23]], ![[4, 54, 34, 50, 12, 53], [54, 48, 7, 18, 26, 45], [54, 54, 15], [11, 0, 55], [14, 25, 33], [2, 43, 4]]]
 h' := ![![[37, 8, 15, 29], [48, 10, 46, 31], [36, 54, 53, 51], [54, 7, 17, 17], [26, 49, 37, 16], [0, 0, 1], [0, 1]], ![[19, 19, 7, 36], [59, 51, 45, 22], [64, 7, 23, 43], [56, 32, 40, 1], [37, 7, 7, 3], [37, 58, 39, 44], [37, 8, 15, 29]], ![[27, 39, 45, 2], [13, 32, 29, 58], [1, 61, 4, 22], [47, 10, 66, 27], [40, 0, 17, 32], [48, 37, 22, 13], [19, 19, 7, 36]], ![[0, 1], [63, 41, 14, 23], [14, 12, 54, 18], [33, 18, 11, 22], [22, 11, 6, 16], [44, 39, 5, 10], [27, 39, 45, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [2, 54, 15], []]
 b := ![[], [], [31, 25, 51, 61], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 4
  hpos := by decide
  P := [41, 18, 30, 51, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10975477, -5975191, 7026475, -2930490, 4885978]
  a := ![-13, -7, -11, 0, -26]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![17963, -162107, -1134853, -2231490, 4885978]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 20151121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![204, 136, -64, -41, -134]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![204, 136, -64, -41, -134]] 
 ![![67, 0, 0, 0, 0], ![20, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![37, 0, 0, 1, 0], ![58, 0, 0, 0, 1]] where
  M :=![![![204, 136, -64, -41, -134], ![-659, 367, -80, 47, -380], ![-1379, 68, 81, 173, -98], ![393, -648, 198, 20, 660], ![983, -378, 60, -89, 403]]]
  hmulB := by decide  
  f := ![![![-1447886, -344120, -596302, -148779, -707260]], ![![-481091, -114341, -198134, -49435, -235002]], ![![-153809, -36556, -63345, -15805, -75132]], ![![-900221, -213956, -370750, -92503, -439738]], ![![-1252297, -297634, -515750, -128681, -611719]]]
  g := ![![![103, 136, -64, -41, -134], ![186, 367, -80, 47, -380], ![-54, 68, 81, 173, -98], ![-389, -648, 198, 20, 660], ![-174, -378, 60, -89, 403]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![1447886, 344120, 596302, 148779, 707260]] ![![204, 136, -64, -41, -134]]
  ![![67, 0, 0, 0, 0]] where
 M := ![![![-67, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0, 0, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0, 0, 0]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![0, 0, 0, 71, 0], ![0, 0, 0, 0, 71]] where
  M :=![![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![0, 0, 0, 71, 0], ![0, 0, 0, 0, 71]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 5 2 6 [34, 44, 48, 17, 20, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 45, 27, 22, 9], [44, 49, 26, 44, 43], [59, 63, 68, 32, 39], [3, 55, 21, 44, 51], [0, 1]]
 g := ![![[58, 46, 9, 13, 30], [13, 12, 8, 4, 38], [37, 56, 67, 60, 58], [16, 28, 51, 1], [], []], ![[34, 7, 63, 9, 31, 10, 25, 25], [37, 9, 52, 0, 38, 57, 62, 54], [65, 40, 18, 25, 31, 44, 6, 57], [21, 70, 62, 19], [39, 9, 51, 25], [23, 4, 54, 10]], ![[16, 61, 13, 43, 0, 4, 28, 37], [16, 64, 15, 62, 2, 60, 34, 30], [16, 58, 43, 9, 28, 41, 15, 5], [38, 65, 26, 60], [58, 52, 24, 49], [23, 2, 32, 3]], ![[3, 60, 70, 24, 68, 48, 15, 66], [7, 54, 6, 59, 59, 12, 50, 59], [54, 70, 21, 59, 69, 35, 68, 59], [42, 22, 58, 37], [19, 33, 16, 32], [5, 61, 50, 30]], ![[34, 5, 39, 49, 26, 11, 37, 41], [61, 44, 7, 10, 11, 55, 37, 51], [26, 3, 61, 46, 54, 20, 2, 65], [10, 55, 57, 2], [16, 38, 63, 18], [26, 68, 38, 45]]]
 h' := ![![[16, 45, 27, 22, 9], [55, 59, 42, 24, 32], [20, 26, 46, 6, 40], [24, 48, 29, 11, 49], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[44, 49, 26, 44, 43], [69, 16, 63, 1, 49], [55, 70, 7, 37, 19], [69, 9, 5, 28, 39], [12, 70, 69, 45, 27], [42, 8, 57, 48, 5], [16, 45, 27, 22, 9]], ![[59, 63, 68, 32, 39], [5, 14, 13, 55, 25], [58, 61, 4, 51, 69], [69, 61, 41, 44, 30], [56, 65, 58, 4, 29], [18, 37, 66, 21, 7], [44, 49, 26, 44, 43]], ![[3, 55, 21, 44, 51], [3, 44, 45, 19, 10], [51, 13, 31, 68, 13], [40, 26, 66, 5, 13], [30, 65, 5, 29, 26], [45, 28, 56, 5, 23], [59, 63, 68, 32, 39]], ![[0, 1], [14, 9, 50, 43, 26], [25, 43, 54, 51, 1], [27, 69, 1, 54, 11], [56, 13, 10, 64, 59], [48, 69, 33, 68, 36], [3, 55, 21, 44, 51]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45, 33, 6, 59], [], [], []]
 b := ![[], [42, 19, 20, 28, 25], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 5
  hpos := by decide
  P := [34, 44, 48, 17, 20, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2505475456268, -2556634283328, -5277505798890, 5389702522230, -11782568924858]
  a := ![19, -56, 15, -67, 35]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![35288386708, -36008933568, -74331067590, 75911303130, -165951674998]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 1804229351 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def PBC71 : ContainsPrimesAboveP 71 ![I71N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![71, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 71 (by decide) 𝕀

instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2547715, -605513, -1049257, -261794, -1244496]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![-2547715, -605513, -1049257, -261794, -1244496]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![0, 0, 73, 0, 0], ![7, 25, 62, 1, 0], ![3, 71, 11, 0, 1]] where
  M :=![![![-2547715, -605513, -1049257, -261794, -1244496], ![-5763366, -1369774, -2373597, -592224, -2815260], ![-13037712, -3098667, -5369482, -1339710, -6368604], ![-11865090, -2819961, -4886547, -1219213, -5795802], ![129333, 30740, 53266, 13289, 63179]]]
  hmulB := by decide  
  f := ![![![-1, -409, 145, 44, 408]], ![![1764, -628, 87, -162, 672]], ![![2202, 345, -280, -336, -300]], ![![2447, 58, -199, -335, -6]], ![![2016, -568, 48, -203, 617]]]
  g := ![![![41347, 1291761, 395499, -261794, -1244496], ![93534, 2922182, 894687, -592224, -2815260], ![211590, 6610479, 2023934, -1339710, -6368604], ![192559, 6015922, 1841897, -1219213, -5795802], ![-2099, -65578, -20077, 13289, 63179]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [51, 58, 34, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 62, 37], [32, 10, 36], [0, 1]]
 g := ![![[70, 38, 55], [43, 25], [10, 55], [63, 51, 9], [39, 1], []], ![[5, 56, 27, 50], [64, 32], [1, 16], [19, 22, 34, 49], [44, 27], [17, 55]], ![[15, 11, 64, 27], [33, 18], [13, 67], [3, 7, 63, 41], [54, 48], [18, 55]]]
 h' := ![![[7, 62, 37], [1, 63, 36], [2, 9, 5], [72, 55, 37], [55, 23, 3], [0, 0, 1], [0, 1]], ![[32, 10, 36], [48, 2, 63], [63, 32, 18], [48, 14, 69], [25, 30, 5], [58, 70, 10], [7, 62, 37]], ![[0, 1], [66, 8, 47], [17, 32, 50], [60, 4, 40], [14, 20, 65], [33, 3, 62], [32, 10, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33, 10], []]
 b := ![[], [10, 15, 53], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [51, 58, 34, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5417, 5040, -1914, 131, 103]
  a := ![-2, -4, -2, -3, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-91, -76, -153, 131, 103]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 389017 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -409, 145, 44, 408]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-1, -409, 145, 44, 408]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![70, 22, 1, 0, 0], ![33, 49, 0, 1, 0], ![68, 58, 0, 0, 1]] where
  M :=![![![-1, -409, 145, 44, 408], ![1764, -628, 87, -162, 672], ![2202, 345, -280, -336, -300], ![-1986, 1407, -357, 119, -1494], ![-2295, 556, -28, 247, -595]]]
  hmulB := by decide  
  f := ![![![-2547715, -605513, -1049257, -261794, -1244496]], ![![-5763366, -1369774, -2373597, -592224, -2815260]], ![![-4358518, -1035885, -1795022, -447866, -2129028]], ![![-5182803, -1231792, -2134497, -532567, -2531670]], ![![-6950555, -1651932, -2862532, -714215, -3395173]]]
  g := ![![![-539, -403, 145, 44, 408], ![-612, -460, 87, -162, 672], ![730, 553, -280, -336, -300], ![1653, 1234, -357, 119, -1494], ![438, 323, -28, 247, -595]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P1 : CertificateIrreducibleZModOfList' 73 2 2 6 [31, 64, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 72], [0, 1]]
 g := ![![[68, 38], [18], [32], [30, 41], [8], [1]], ![[45, 35], [18], [32], [34, 32], [8], [1]]]
 h' := ![![[9, 72], [45, 44], [26, 23], [19, 18], [56, 25], [42, 9], [0, 1]], ![[0, 1], [3, 29], [14, 50], [35, 55], [62, 48], [50, 64], [9, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [68]]
 b := ![[], [66, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N1 : CertifiedPrimeIdeal' SI73N1 73 where
  n := 2
  hpos := by decide
  P := [31, 64, 1]
  hirr := P73P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![14971, 4436, 8686, 295, 11451]
  a := ![23, 27, 19, 12, 45]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-18924, -11853, 8686, 295, 11451]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N1 B_one_repr
lemma NI73N1 : Nat.card (O ⧸ I73N1) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![-2547715, -605513, -1049257, -261794, -1244496]] ![![-1, -409, 145, 44, 408]]
  ![![73, 0, 0, 0, 0]] where
 M := ![![![73, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0)
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![51, -87, -7, 38, -92]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![51, -87, -7, 38, -92]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![0, 0, 79, 0, 0], ![0, 0, 0, 79, 0], ![69, 31, 37, 70, 1]] where
  M :=![![![51, -87, -7, 38, -92], ![-254, 266, -103, 40, 136], ![664, -589, 482, -382, 376], ![306, -127, -437, 465, -1026], ![-605, 572, -250, 127, 21]]]
  hmulB := by decide  
  f := ![![![1711, 407, 705, 176, 836]], ![![3872, 920, 1595, 398, 1892]], ![![8762, 2081, 3608, 900, 4280]], ![![7974, 1895, 3283, 819, 3894]], ![![14182, 3370, 5840, 1457, 6927]]]
  g := ![![![81, 35, 43, 82, -92], ![-122, -50, -65, -120, 136], ![-320, -155, -170, -338, 376], ![900, 401, 475, 915, -1026], ![-26, -1, -13, -17, 21]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 4 2 6 [14, 2, 20, 14, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 36, 33, 65], [21, 9, 16, 7], [33, 33, 30, 7], [0, 1]]
 g := ![![[50, 70, 63, 23], [58, 67, 0, 21], [15, 13, 54, 38], [21, 15, 28, 38], [1], []], ![[65, 70, 75, 62, 40, 44], [9, 64, 36, 53, 72, 50], [58, 23, 44, 12, 30, 32], [18, 73, 31, 39, 21, 72], [25, 78, 19], [34, 45, 38]], ![[22, 38, 45, 44, 76, 58], [30, 68, 49, 24, 24, 34], [36, 61, 55, 0, 57, 33], [10, 49, 12, 30, 20, 43], [0, 69, 11], [24, 12, 49]], ![[76, 31, 4, 65, 41, 63], [10, 40, 67, 66, 25, 78], [10, 78, 0, 10, 73, 74], [32, 66, 24, 78, 11, 29], [57, 36, 51], [77, 50, 49]]]
 h' := ![![[11, 36, 33, 65], [57, 70, 43, 55], [27, 35, 9, 69], [22, 23, 4, 14], [65, 77, 59, 65], [0, 0, 1], [0, 1]], ![[21, 9, 16, 7], [40, 65, 32, 68], [50, 77, 40, 63], [8, 63, 52, 76], [65, 58, 23, 44], [40, 15, 9, 63], [11, 36, 33, 65]], ![[33, 33, 30, 7], [40, 43, 43, 32], [62, 15, 71, 45], [68, 14, 71, 4], [44, 32, 68, 35], [26, 4, 37, 66], [21, 9, 16, 7]], ![[0, 1], [72, 59, 40, 3], [75, 31, 38, 60], [17, 58, 31, 64], [34, 70, 8, 14], [11, 60, 32, 29], [33, 33, 30, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [46, 34, 5], []]
 b := ![[], [], [7, 38, 69, 67], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 4
  hpos := by decide
  P := [14, 2, 20, 14, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![535451239, -410010208, -140006510, 267751027, -688970793]
  a := ![-33, -9, -27, 15, -65]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![608537164, 265165625, 320910289, 613869703, -688970793]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 38950081 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1711, -407, -705, -176, -836]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![-1711, -407, -705, -176, -836]] 
 ![![79, 0, 0, 0, 0], ![53, 1, 0, 0, 0], ![35, 0, 1, 0, 0], ![73, 0, 0, 1, 0], ![32, 0, 0, 0, 1]] where
  M :=![![![-1711, -407, -705, -176, -836], ![-3872, -920, -1595, -398, -1892], ![-8762, -2081, -3608, -900, -4280], ![-7974, -1895, -3283, -819, -3894], ![87, 20, 36, 9, 43]]]
  hmulB := by decide  
  f := ![![![-51, 87, 7, -38, 92]], ![![-31, 55, 6, -26, 60]], ![![-31, 46, -3, -12, 36]], ![![-51, 82, 12, -41, 98]], ![![-13, 28, 6, -17, 37]]]
  g := ![![![1065, -407, -705, -176, -836], ![2409, -920, -1595, -398, -1892], ![5449, -2081, -3608, -900, -4280], ![4959, -1895, -3283, -819, -3894], ![-54, 20, 36, 9, 43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![51, -87, -7, 38, -92]] ![![-1711, -407, -705, -176, -836]]
  ![![79, 0, 0, 0, 0]] where
 M := ![![![-79, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0)
instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8878, 14944, -5978, -2759, -14914]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![8878, 14944, -5978, -2759, -14914]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![0, 0, 83, 0, 0], ![11, 48, 12, 1, 0], ![69, 69, 73, 0, 1]] where
  M :=![![![8878, 14944, -5978, -2759, -14914], ![-67933, 29969, -5488, 5717, -31468], ![-108721, -4768, 9935, 14775, 2834], ![61797, -59824, 16552, -1728, 61476], ![93543, -28570, 3050, -9227, 30521]]]
  hmulB := by decide  
  f := ![![![-159900, -38008, -65848, -16437, -78100]], ![![-361711, -85985, -148982, -37159, -176722]], ![![-818365, -194408, -337025, -84083, -399676]], ![![-357663, -85004, -147306, -36747, -174718]], ![![-1153297, -274041, -474973, -118498, -563315]]]
  g := ![![![12871, 14174, 13444, -2759, -14914], ![24584, 23215, 26784, 5717, -31468], ![-5624, -10958, -4509, 14775, 2834], ![-50133, -50828, -53620, -1728, 61476], ![-23023, -20381, -25473, -9227, 30521]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [28, 57, 32, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 15, 2], [38, 67, 81], [0, 1]]
 g := ![![[44, 61, 21], [27], [70, 68], [77, 59], [54, 51, 1], []], ![[58, 45, 63, 19], [52, 26, 23, 50], [0, 10], [20, 12], [60, 18, 65, 14], [15, 4]], ![[51, 12, 1, 11], [71, 34, 68, 33], [61, 70], [55, 38], [37, 11, 1, 48], [19, 4]]]
 h' := ![![[13, 15, 2], [74, 14, 41], [68, 39], [77, 52, 20], [65, 59, 68], [0, 0, 1], [0, 1]], ![[38, 67, 81], [8, 42, 36], [77, 4, 78], [49, 30, 33], [32, 78, 26], [81, 4, 67], [13, 15, 2]], ![[0, 1], [67, 27, 6], [56, 40, 5], [41, 1, 30], [81, 29, 72], [82, 79, 15], [38, 67, 81]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58], []]
 b := ![[], [22, 54], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [28, 57, 32, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1096330, -1175428, 1024588, -784118, 761916]
  a := ![14, -4, 12, -22, 28]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-516272, -194096, -544408, -784118, 761916]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 571787 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, 3, 3, -4, 10]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-3, 3, 3, -4, 10]] 
 ![![83, 0, 0, 0, 0], ![12, 1, 0, 0, 0], ![22, 0, 1, 0, 0], ![28, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] where
  M :=![![![-3, 3, 3, -4, 10], ![28, -24, 5, 0, -14], ![-56, 61, -38, 24, -14], ![-6, -9, 45, -43, 72], ![41, -44, 14, -3, -17]]]
  hmulB := by decide  
  f := ![![![8045, 1921, 3311, 826, 3922]], ![![1382, 330, 569, 142, 674]], ![![2628, 627, 1082, 270, 1282]], ![![3166, 755, 1303, 325, 1544]], ![![868, 207, 357, 89, 423]]]
  g := ![![![-1, 3, 3, -4, 10], ![4, -24, 5, 0, -14], ![-6, 61, -38, 24, -14], ![-4, -9, 45, -43, 72], ![6, -44, 14, -3, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1

def I83N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-547, 1596, 6, 118, 1140]] i)))

def SI83N2: IdealEqSpanCertificate' Table ![![-547, 1596, 6, 118, 1140]] 
 ![![83, 0, 0, 0, 0], ![47, 1, 0, 0, 0], ![32, 0, 1, 0, 0], ![13, 0, 0, 1, 0], ![76, 0, 0, 0, 1]] where
  M :=![![![-547, 1596, 6, 118, 1140], ![4914, -2703, 2972, -1246, 1848], ![3654, 2944, -3347, 5342, -5628], ![-5700, 9804, 2514, -2581, 12288], ![4188, -4752, 3858, -2842, 2513]]]
  hmulB := by decide  
  f := ![![![3401971, -1503996, 275970, -285962, 1579068]], ![![1992181, -848843, 150286, -170860, 892524]], ![![1278226, -525712, 89709, -111646, 553572]], ![![387413, -207480, 44280, -28703, 216348]], ![![3057884, -1392984, 262650, -252654, 1460825]]]
  g := ![![![-1975, 1596, 6, 118, 1140], ![-1053, -2703, 2972, -1246, 1848], ![3984, 2944, -3347, 5342, -5628], ![-17437, 9804, 2514, -2581, 12288], ![-602, -4752, 3858, -2842, 2513]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N2 : Nat.card (O ⧸ I83N2) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N2)

lemma isPrimeI83N2 : Ideal.IsPrime I83N2 := prime_ideal_of_norm_prime hp83.out _ NI83N2
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![8878, 14944, -5978, -2759, -14914]] ![![-3, 3, 3, -4, 10]]
  ![![131646, -15633, -4433, -15605, 18146]] where
 M := ![![![131646, -15633, -4433, -15605, 18146]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI83N1 : IdealMulLeCertificate' Table 
  ![![131646, -15633, -4433, -15605, 18146]] ![![-547, 1596, 6, 118, 1140]]
  ![![83, 0, 0, 0, 0]] where
 M := ![![![-85158, 91051, -57851, 37433, -17762]]]
 hmul := by decide  
 g := ![![![![-1026, 1097, -697, 451, -214]]]]
 hle2 := by decide  


def PBC83 : ContainsPrimesAboveP 83 ![I83N0, I83N1, I83N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
    exact isPrimeI83N1
    exact isPrimeI83N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 83 (by decide) (𝕀 ⊙ MulI83N0 ⊙ MulI83N1)
instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![267, 210, 204, 78, 164]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![267, 210, 204, 78, 164]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![0, 0, 89, 0, 0], ![0, 0, 0, 89, 0], ![0, 74, 49, 58, 1]] where
  M :=![![![267, 210, 204, 78, 164], ![890, 221, 530, 166, 632], ![3026, 322, 1185, 262, 1628], ![3204, 498, 972, 157, 1284], ![178, 128, -74, -44, -145]]]
  hmulB := by decide  
  f := ![![![7, -10, 16, -14, 20]], ![![38, -31, -18, 26, -64]], ![![-178, 174, -43, 2, 92]], ![![168, -186, 144, -103, 84]], ![![44, -52, 55, -44, 51]]]
  g := ![![![3, -134, -88, -106, 164], ![10, -523, -342, -410, 632], ![34, -1350, -883, -1058, 1628], ![36, -1062, -696, -835, 1284], ![2, 122, 79, 94, -145]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 4 2 6 [65, 77, 51, 18, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 5, 40, 18], [18, 45, 63, 17], [47, 38, 75, 54], [0, 1]]
 g := ![![[67, 46, 41, 67], [4, 9, 44], [6, 58, 72], [36, 39, 10, 36], [71, 1], []], ![[87, 25, 30, 36, 10, 67], [19, 1, 64], [37, 66, 68], [68, 67, 36, 71, 58, 1], [32, 40, 42, 4, 11, 53], [54, 58, 57]], ![[4, 31, 67, 28, 50, 50], [51, 75, 79], [64, 4, 87], [21, 40, 35, 55, 40, 18], [32, 9, 42, 17, 87, 68], [5, 55, 22]], ![[41, 36, 42, 63, 88, 70], [23, 2, 40], [23, 73, 21], [69, 47, 83, 31, 48, 74], [60, 49, 4, 53, 27, 26], [62, 23, 68]]]
 h' := ![![[6, 5, 40, 18], [12, 17, 1, 45], [19, 38, 0, 20], [63, 24, 21, 28], [13, 75, 40, 6], [0, 0, 1], [0, 1]], ![[18, 45, 63, 17], [10, 50, 7, 35], [34, 52, 67, 81], [6, 43, 7, 54], [21, 15, 68, 19], [86, 53, 82, 40], [6, 5, 40, 18]], ![[47, 38, 75, 54], [72, 68, 9, 58], [70, 57, 74, 48], [15, 71, 53, 40], [74, 68, 3, 72], [88, 63, 64, 2], [18, 45, 63, 17]], ![[0, 1], [40, 43, 72, 40], [17, 31, 37, 29], [34, 40, 8, 56], [80, 20, 67, 81], [48, 62, 31, 47], [47, 38, 75, 54]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [15, 61, 20], []]
 b := ![[], [], [25, 50, 3, 25], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 4
  hpos := by decide
  P := [65, 77, 51, 18, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![575550718, 172032403, 228929858, 75817390, 288020457]
  a := ![29, 19, 20, 10, 45]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![6466862, -237544735, -156000815, -186846844, 288020457]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 62742241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, -10, 16, -14, 20]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![7, -10, 16, -14, 20]] 
 ![![89, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![40, 0, 1, 0, 0], ![79, 0, 0, 1, 0], ![85, 0, 0, 0, 1]] where
  M :=![![![7, -10, 16, -14, 20], ![38, -31, -18, 26, -64], ![-178, 174, -43, 2, 92], ![168, -186, 144, -103, 84], ![82, -72, -18, 36, -105]]]
  hmulB := by decide  
  f := ![![![267, 210, 204, 78, 164]], ![![31, 19, 22, 8, 20]], ![![154, 98, 105, 38, 92]], ![![273, 192, 192, 71, 160]], ![![257, 202, 194, 74, 155]]]
  g := ![![![-13, -10, 16, -14, 20], ![49, -31, -18, 26, -64], ![-86, 174, -43, 2, 92], ![-37, -186, 144, -103, 84], ![83, -72, -18, 36, -105]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![267, 210, 204, 78, 164]] ![![7, -10, 16, -14, 20]]
  ![![89, 0, 0, 0, 0]] where
 M := ![![![89, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0)
instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, -23, 5, -2, 2]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![19, -23, 5, -2, 2]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![0, 0, 97, 0, 0], ![0, 0, 0, 97, 0], ![58, 37, 51, 96, 1]] where
  M :=![![![19, -23, 5, -2, 2], ![2, 18, -25, 10, -10], ![-10, 7, 28, -50, 50], ![24, -75, -9, 23, -120], ![-71, 40, -34, 33, -33]]]
  hmulB := by decide  
  f := ![![![-3, 1, -1, 0, -2]], ![![-8, 0, -1, 0, -2]], ![![-8, -5, -2, 0, -2]], ![![0, -3, -3, -1, 0]], ![![-9, -5, -5, -1, -3]]]
  g := ![![![-1, -1, -1, -2, 2], ![6, 4, 5, 10, -10], ![-30, -19, -26, -50, 50], ![72, 45, 63, 119, -120], ![19, 13, 17, 33, -33]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 4 2 6 [51, 73, 95, 11, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [90, 75, 17, 64], [96, 26, 35, 64], [94, 92, 45, 66], [0, 1]]
 g := ![![[61, 31, 16, 22], [13, 14, 96], [20, 14, 3], [77, 47, 49], [26, 86, 1], []], ![[13, 95, 81, 66, 15, 47], [77, 47, 50], [56, 63, 93], [36, 32, 33], [94, 4, 18], [2, 46, 84, 23, 87, 50]], ![[70, 81, 4, 1, 73, 75], [60, 15, 65], [88, 93, 16], [32], [8, 76, 47], [70, 40, 80, 85, 14, 50]], ![[29, 89, 19, 29, 41, 86], [85, 83, 12], [55, 17, 86], [58, 6, 24], [3, 23, 93], [38, 61, 30, 45, 81, 85]]]
 h' := ![![[90, 75, 17, 64], [17, 19, 48, 33], [96, 32, 64, 22], [7, 19, 46, 10], [32, 21, 28, 7], [0, 0, 0, 1], [0, 1]], ![[96, 26, 35, 64], [74, 50, 32, 50], [86, 83, 38, 27], [56, 59, 56, 53], [7, 66, 51, 79], [40, 94, 23, 55], [90, 75, 17, 64]], ![[94, 92, 45, 66], [33, 1, 39, 18], [38, 9, 61, 68], [89, 29, 27, 93], [13, 35, 41], [18, 9, 44, 85], [96, 26, 35, 64]], ![[0, 1], [34, 27, 75, 93], [2, 70, 31, 77], [24, 87, 65, 38], [84, 72, 74, 11], [72, 91, 30, 53], [94, 92, 45, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [59, 25, 93], []]
 b := ![[], [], [1, 78, 93, 91], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 4
  hpos := by decide
  P := [51, 73, 95, 11, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1755055, 1815146, -783626, 371146, 338312]
  a := ![3, -3, 3, -6, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-220383, -110334, -185954, -330998, 338312]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 88529281 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, -1, 1, 0, 2]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![3, -1, 1, 0, 2]] 
 ![![97, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![72, 0, 1, 0, 0], ![60, 0, 0, 1, 0], ![65, 0, 0, 0, 1]] where
  M :=![![![3, -1, 1, 0, 2], ![8, 0, 1, 0, 2], ![8, 5, 2, 0, 2], ![0, 3, 3, 1, 0], ![-5, 0, 0, 1, -1]]]
  hmulB := by decide  
  f := ![![![-19, 23, -5, 2, -2]], ![![-1, 1, 0, 0, 0]], ![![-14, 17, -4, 2, -2]], ![![-12, 15, -3, 1, 0]], ![![-12, 15, -3, 1, -1]]]
  g := ![![![-2, -1, 1, 0, 2], ![-2, 0, 1, 0, 2], ![-3, 5, 2, 0, 2], ![-3, 3, 3, 1, 0], ![0, 0, 0, 1, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![19, -23, 5, -2, 2]] ![![3, -1, 1, 0, 2]]
  ![![97, 0, 0, 0, 0]] where
 M := ![![![-97, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC97 : ContainsPrimesAboveP 97 ![I97N0, I97N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
    exact isPrimeI97N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 97 (by decide) (𝕀 ⊙ MulI97N0)
instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0, 0, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0, 0, 0]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![0, 0, 101, 0, 0], ![0, 0, 0, 101, 0], ![0, 0, 0, 0, 101]] where
  M :=![![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![0, 0, 101, 0, 0], ![0, 0, 0, 101, 0], ![0, 0, 0, 0, 101]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 5 2 6 [1, 58, 13, 77, 95, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [90, 44, 5, 80, 21], [22, 55, 30, 3, 24], [28, 68, 8, 28, 31], [68, 34, 58, 91, 25], [0, 1]]
 g := ![![[11, 31, 28, 46, 37], [60, 53, 7, 20], [18, 93, 54, 95, 70], [12, 81, 51, 65], [6, 1], []], ![[29, 36, 30, 26, 58, 99, 61, 31], [62, 4, 71, 47], [76, 83, 92, 10, 28, 39, 14, 100], [90, 16, 42, 65], [38, 5, 1, 100], [68, 39, 77, 44, 67, 69, 8, 70]], ![[72, 58, 27, 97, 1, 29, 82, 20], [77, 3, 75, 80], [1, 6, 68, 100, 2, 58, 98, 22], [14, 50, 86, 71], [100, 32, 64, 96], [80, 72, 86, 8, 8, 93, 56, 88]], ![[40, 12, 81, 73, 15, 6, 35, 70], [99, 55, 80, 95], [41, 3, 7, 29, 61, 20, 27, 54], [100, 13, 58, 16], [53, 66, 13, 49], [58, 39, 45, 87, 85, 37, 1, 97]], ![[9, 54, 6, 59, 8, 62, 62, 25], [32, 11, 85, 6], [91, 59, 81, 51, 33, 20, 53, 9], [28, 34, 54, 97], [98, 34, 30, 30], [72, 1, 88, 17, 39, 31, 58, 71]]]
 h' := ![![[90, 44, 5, 80, 21], [62, 99, 60, 92, 21], [83, 45, 82, 74, 90], [24, 78, 55, 82, 75], [95, 55, 66, 30, 60], [0, 0, 0, 1], [0, 1]], ![[22, 55, 30, 3, 24], [52, 87, 68, 40, 8], [35, 57, 31, 54, 42], [34, 63, 100, 34, 23], [86, 22, 29, 13, 41], [15, 71, 51, 66, 10], [90, 44, 5, 80, 21]], ![[28, 68, 8, 28, 31], [49, 9, 11, 91, 61], [96, 37, 31, 39, 22], [3, 72, 21, 72, 89], [57, 33, 45, 35, 24], [64, 4, 53, 12, 46], [22, 55, 30, 3, 24]], ![[68, 34, 58, 91, 25], [51, 37, 72, 25, 10], [7, 56, 85, 68, 87], [34, 55, 76, 39, 56], [72, 66, 13, 30, 97], [78, 84, 70, 16, 7], [28, 68, 8, 28, 31]], ![[0, 1], [93, 71, 92, 55, 1], [23, 7, 74, 68, 62], [26, 35, 51, 76, 60], [85, 26, 49, 94, 81], [48, 43, 28, 6, 38], [68, 34, 58, 91, 25]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 89, 52, 1], [], [], []]
 b := ![[], [19, 97, 100, 17, 24], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 5
  hpos := by decide
  P := [1, 58, 13, 77, 95, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9143640797, 1960092658, 3439477836, 1197156838, 3779688458]
  a := ![19, 9, 16, -1, 35]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![90531097, 19406858, 34054236, 11853038, 37422658]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10510100501 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def PBC101 : ContainsPrimesAboveP 101 ![I101N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![101, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 101 (by decide) 𝕀

instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0, 0, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0, 0, 0]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![0, 0, 0, 103, 0], ![0, 0, 0, 0, 103]] where
  M :=![![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![0, 0, 0, 103, 0], ![0, 0, 0, 0, 103]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 5 2 6 [73, 23, 60, 8, 14, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 64, 3, 1, 68], [43, 7, 28, 77, 93], [80, 37, 51, 91, 90], [66, 97, 21, 37, 58], [0, 1]]
 g := ![![[31, 73, 31, 101, 59], [92, 86, 30, 87, 61], [77, 102, 3, 31, 28], [55, 54, 81, 15], [89, 1], []], ![[57, 96, 42, 60, 67, 79, 3, 36], [101, 15, 40, 87, 76, 13, 37, 76], [96, 101, 101, 35, 39, 16, 50, 25], [24, 7, 40, 76], [41, 26, 17, 46], [83, 22, 44, 2, 20, 23, 36, 76]], ![[0, 91, 16, 15, 8, 89, 64, 26], [9, 78, 99, 61, 79, 7, 5, 60], [20, 2, 18, 13, 33, 82, 24, 8], [44, 60, 89, 1], [75, 18, 98, 68], [7, 54, 102, 73, 24, 63, 20, 30]], ![[24, 47, 95, 67, 95, 79, 34, 43], [72, 102, 88, 66, 25, 89, 70, 101], [91, 93, 18, 49, 15, 14, 98, 65], [1, 56, 11, 68], [80, 0, 98, 15], [72, 46, 60, 56, 49, 42, 57, 69]], ![[57, 79, 0, 66, 90, 76, 57, 34], [78, 49, 18, 12, 9, 72, 14, 15], [87, 67, 102, 74, 2, 91, 49, 63], [65, 24, 87, 18], [22, 32, 87, 91], [101, 81, 80, 65, 79, 9, 21, 30]]]
 h' := ![![[3, 64, 3, 1, 68], [82, 31, 88, 0, 70], [44, 83, 50, 4, 79], [66, 79, 55, 65, 50], [95, 43, 96, 52, 85], [0, 0, 0, 1], [0, 1]], ![[43, 7, 28, 77, 93], [53, 5, 78, 76, 7], [81, 16, 42, 15, 68], [32, 89, 76, 82, 80], [62, 99, 71, 64, 73], [45, 67, 25, 41, 47], [3, 64, 3, 1, 68]], ![[80, 37, 51, 91, 90], [41, 67, 29, 64, 92], [62, 100, 83, 67, 32], [62, 36, 89, 8, 24], [9, 4, 39, 0, 1], [98, 15, 89, 57, 58], [43, 7, 28, 77, 93]], ![[66, 97, 21, 37, 58], [18, 20, 19, 81, 58], [29, 30, 16, 28, 99], [102, 25, 24, 22, 43], [81, 9, 32, 82, 58], [87, 42, 99, 20, 18], [80, 37, 51, 91, 90]], ![[0, 1], [7, 83, 95, 88, 82], [48, 80, 15, 92, 31], [27, 80, 65, 29, 9], [72, 51, 71, 8, 92], [66, 82, 96, 87, 83], [66, 97, 21, 37, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47, 42, 20, 75], [], [], []]
 b := ![[], [24, 2, 5, 100, 61], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 5
  hpos := by decide
  P := [73, 23, 60, 8, 14, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11065790683, 11739870784, 31233308, -2161428838, 11041948140]
  a := ![21, 7, 17, -8, 41]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-107434861, 113979328, 303236, -20984746, 107203380]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 11592740743 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def PBC103 : ContainsPrimesAboveP 103 ![I103N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![103, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 103 (by decide) 𝕀



lemma PB307I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 103 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 103 (by omega)

def PB307I2 : PrimesBelowBoundCertificateInterval O 61 103 307 where
  m := 9
  g := ![2, 1, 2, 2, 3, 2, 2, 1, 1]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103]
  hP := PB307I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0, I67N1]
    · exact ![I71N0]
    · exact ![I73N0, I73N1]
    · exact ![I79N0, I79N1]
    · exact ![I83N0, I83N1, I83N2]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0]
    · exact ![I103N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC67
    · exact PBC71
    · exact PBC73
    · exact PBC79
    · exact PBC83
    · exact PBC89
    · exact PBC97
    · exact PBC101
    · exact PBC103
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![20151121, 67]
    · exact ![1804229351]
    · exact ![389017, 5329]
    · exact ![38950081, 79]
    · exact ![571787, 83, 83]
    · exact ![62742241, 89]
    · exact ![88529281, 97]
    · exact ![10510100501]
    · exact ![11592740743]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
      exact NI83N1
      exact NI83N2
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
  β := ![I67N1, I79N1, I83N1, I83N2, I89N1, I97N1]
  Il := ![[I67N1], [], [], [I79N1], [I83N1, I83N2], [I89N1], [I97N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
