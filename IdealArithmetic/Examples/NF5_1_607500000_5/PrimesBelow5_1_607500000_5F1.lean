
import IdealArithmetic.Examples.NF5_1_607500000_5.RI5_1_607500000_5
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![35, -52, 11, -5, 6]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![35, -52, 11, -5, 6]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![25, 28, 1, 0, 0], ![14, 7, 0, 1, 0], ![20, 28, 0, 0, 1]] where
  M :=![![![35, -52, 11, -5, 6], ![38, -1, -14, -16, -10], ![-72, 118, -53, -16, -32], ![-46, 58, -30, -11, -18], ![-8, 14, -8, -4, -5]]]
  hmulB := by decide  
  f := ![![![-7, 4, -7, 9, -4]], ![![-26, 11, -28, 30, 18]], ![![-23, 10, -24, 25, 16]], ![![-6, 3, -6, 7, 0]], ![![-48, 22, -52, 60, 15]]]
  g := ![![![-10, -17, 11, -5, 6], ![28, 27, -14, -16, -10], ![73, 90, -53, -16, -32], ![42, 51, -30, -11, -18], ![12, 14, -8, -4, -5]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [27, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 28], [0, 1]]
 g := ![![[4, 6], [9], [14, 6], [8, 1]], ![[23, 23], [9], [4, 23], [16, 28]]]
 h' := ![![[8, 28], [19, 8], [28, 3], [16, 8], [0, 1]], ![[0, 1], [25, 21], [23, 26], [22, 21], [8, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [13, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [27, 21, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![80399, -42287, 88835, -122752, 55364]
  a := ![-12, 17, 2, -12, -36]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-52732, -111055, 88835, -122752, 55364]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0, 0, 0], ![19, -19, 2, 0, 1]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![29, 0, 0, 0, 0], ![19, -19, 2, 0, 1]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![4, 10, 1, 0, 0], ![4, 7, 0, 1, 0], ![11, 19, 0, 0, 1]] where
  M :=![![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![0, 0, 0, 29, 0], ![0, 0, 0, 0, 29]], ![![19, -19, 2, 0, 1], ![6, 12, -14, 1, 0], ![28, 19, 53, -95, 2], ![6, 13, 18, -32, -26], ![-140, 71, -155, 185, 8]]]
  hmulB := by decide  
  f := ![![![18240923, 24284561, -32634427, 2348178, 214186], ![-6202868, -68502147, -4263, 0, 0]], ![![23446622, 31215014, -41947811, 3018309, 275312], ![-7973086, -88051656, -5481, 0, 0]], ![![10571078, 14073535, -18912490, 1360828, 124126], ![-3594712, -39698757, -2471, 0, 0]], ![![8175509, 10884263, -14626635, 1052444, 95997], ![-2780091, -30702420, -1911, 0, 0]], ![![22280554, 29662598, -39861624, 2868201, 261620], ![-7576563, -83672589, -5208, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-4, -10, 29, 0, 0], ![-4, -7, 0, 29, 0], ![-11, -19, 0, 0, 29]], ![![0, -2, 2, 0, 1], ![2, 5, -14, 1, 0], ![6, 4, 53, -95, 2], ![12, 19, 18, -32, -26], ![-12, 6, -155, 185, 8]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P1 : CertificateIrreducibleZModOfList' 29 2 2 4 [8, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [21, 28], [0, 1]]
 g := ![![[1, 22], [28], [2, 4], [21, 1]], ![[28, 7], [28], [28, 25], [13, 28]]]
 h' := ![![[21, 28], [3, 15], [13, 17], [6, 27], [0, 1]], ![[0, 1], [28, 14], [22, 12], [22, 2], [21, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [7, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N1 : CertifiedPrimeIdeal' SI29N1 29 where
  n := 2
  hpos := by decide
  P := [8, 8, 1]
  hirr := P29P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-757366, 412790, -856137, 1216540, -598143]
  a := ![84, 41, 130, -312, -13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![151055, 407693, -856137, 1216540, -598143]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N1 B_one_repr
lemma NI29N1 : Nat.card (O ⧸ I29N1) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N1

def I29N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0, 0, 0], ![-9, 1, 0, 0, 0]] i)))

def SI29N2: IdealEqSpanCertificate' Table ![![29, 0, 0, 0, 0], ![-9, 1, 0, 0, 0]] 
 ![![29, 0, 0, 0, 0], ![20, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![17, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  M :=![![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![0, 0, 0, 29, 0], ![0, 0, 0, 0, 29]], ![![-9, 1, 0, 0, 0], ![0, -9, 1, 0, 0], ![-2, -1, -12, 7, 0], ![0, -1, -1, -6, 2], ![10, -5, 11, -13, -9]]]
  hmulB := by decide  
  f := ![![![-41736986, 4778086, -1668332, 955521, -672], ![-133608017, 988552, -3950235, 9744, 0]], ![![-31304816, 3583805, -1251332, 716688, -504], ![-100212660, 741472, -2962872, 7308, 0]], ![![-10432176, 1194291, -417001, 238833, -168], ![-33395376, 247110, -987363, 2436, 0]], ![![-24346688, 2787235, -973199, 557390, -392], ![-77938371, 576675, -2304315, 5684, 0]], ![![-8635236, 988577, -345173, 197694, -139], ![-27643030, 204553, -817290, 2016, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-20, 29, 0, 0, 0], ![-6, 0, 29, 0, 0], ![-17, 0, 0, 29, 0], ![-6, 0, 0, 0, 29]], ![![-1, 1, 0, 0, 0], ![6, -9, 1, 0, 0], ![-1, -1, -12, 7, 0], ![4, -1, -1, -6, 2], ![11, -5, 11, -13, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N2 : Nat.card (O ⧸ I29N2) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N2)

lemma isPrimeI29N2 : Ideal.IsPrime I29N2 := prime_ideal_of_norm_prime hp29.out _ NI29N2
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![35, -52, 11, -5, 6]] ![![29, 0, 0, 0, 0], ![19, -19, 2, 0, 1]]
  ![![29, 0, 0, 0, 0], ![-92, 92, -23, 4, -12]] where
 M := ![![![1015, -1508, 319, -145, 174], ![-209, -719, 361, 173, 235]]]
 hmul := by decide  
 g := ![![![![35, -52, 11, -5, 6], ![0, 0, 0, 0, 0]], ![![15, -47, 18, 5, 11], ![7, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI29N1 : IdealMulLeCertificate' Table 
  ![![29, 0, 0, 0, 0], ![-92, 92, -23, 4, -12]] ![![29, 0, 0, 0, 0], ![-9, 1, 0, 0, 0]]
  ![![29, 0, 0, 0, 0]] where
 M := ![![![841, 0, 0, 0, 0], ![-261, 29, 0, 0, 0]], ![![-2668, 2668, -667, 116, -348], ![754, -841, 232, -29, 116]]]
 hmul := by decide  
 g := ![![![![29, 0, 0, 0, 0]], ![![-9, 1, 0, 0, 0]]], ![![![-92, 92, -23, 4, -12]], ![![26, -29, 8, -1, 4]]]]
 hle2 := by decide  


def PBC29 : ContainsPrimesAboveP 29 ![I29N0, I29N1, I29N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N1
    exact isPrimeI29N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 29 (by decide) (𝕀 ⊙ MulI29N0 ⊙ MulI29N1)
instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0], ![81, -67, 26, 1, 13]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0, 0, 0], ![81, -67, 26, 1, 13]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![24, 29, 28, 1, 0], ![2, 26, 7, 0, 1]] where
  M :=![![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]], ![![81, -67, 26, 1, 13], ![78, -11, -3, 16, 2], ![26, 55, 4, 1, 32], ![90, -17, 65, -52, 18], ![-58, 41, -78, 119, -62]]]
  hmulB := by decide  
  f := ![![![2080, 1652, -1099, 973, -329], ![1085, -1953, 0, 0, 0]], ![![-747, -505, 349, -325, 101], ![-341, 651, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![969, 759, -505, 450, -151], ![499, -903, 0, 0, 0]], ![![-508, -304, 217, -210, 61], ![-210, 420, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-24, -29, -28, 31, 0], ![-2, -26, -7, 0, 31]], ![![1, -14, -3, 1, 13], ![-10, -17, -15, 16, 2], ![-2, -26, -8, 1, 32], ![42, 33, 45, -52, 18], ![-90, -58, -96, 119, -62]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 3 2 4 [14, 29, 21, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [21, 14, 5], [20, 16, 26], [0, 1]]
 g := ![![[14, 11, 20], [18, 3, 10], [1, 17, 7], [1]], ![[24, 1, 16, 19], [11, 10, 23, 28], [20, 9, 2, 9], [13, 20, 6, 1]], ![[9, 15, 6, 11], [6, 23, 5, 3], [17, 27, 25, 6], [28, 10, 12, 30]]]
 h' := ![![[21, 14, 5], [27, 4, 19], [17, 22, 14], [17, 2, 10], [0, 1]], ![[20, 16, 26], [13, 23, 14], [25, 21, 24], [27, 9, 15], [21, 14, 5]], ![[0, 1], [11, 4, 29], [11, 19, 24], [13, 20, 6], [20, 16, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 6], []]
 b := ![[], [19, 10, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 3
  hpos := by decide
  P := [14, 29, 21, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1734744, -739069, 1953373, -2123599, -1266751]
  a := ![2, 5, 7, -17, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1781762, 3025188, 2267142, -2123599, -1266751]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 29791 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0], ![-5, -15, 2, 0, 1]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![31, 0, 0, 0, 0], ![-5, -15, 2, 0, 1]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![21, 18, 1, 0, 0], ![30, 13, 0, 1, 0], ![15, 11, 0, 0, 1]] where
  M :=![![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]], ![![-5, -15, 2, 0, 1], ![6, -12, -10, 1, 0], ![20, 15, 17, -67, 2], ![6, 9, 14, -44, -18], ![-100, 51, -111, 133, -16]]]
  hmulB := by decide  
  f := ![![![-1937204, 3091185, 3038266, -311830, 32253], ![-986203, 9209790, -6820, 0, 0]], ![![-2130085, 3398956, 3340776, -342884, 35465], ![-1084411, 10126770, -7502, 0, 0]], ![![-2542874, 4057653, 3988187, -409328, 42337], ![-1294539, 12089250, -8954, 0, 0]], ![![-2767975, 4416838, 4341228, -445561, 46085], ![-1409143, 13159410, -9746, 0, 0]], ![![-1693190, 2701826, 2655564, -272554, 28190], ![-861965, 8049720, -5962, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-21, -18, 31, 0, 0], ![-30, -13, 0, 31, 0], ![-15, -11, 0, 0, 31]], ![![-2, -2, 2, 0, 1], ![6, 5, -10, 1, 0], ![53, 18, 17, -67, 2], ![42, 17, 14, -44, -18], ![-49, 16, -111, 133, -16]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P1 : CertificateIrreducibleZModOfList' 31 2 2 4 [21, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 30], [0, 1]]
 g := ![![[5, 1], [10, 14], [11, 1], [19, 1]], ![[24, 30], [28, 17], [30, 30], [7, 30]]]
 h' := ![![[19, 30], [7, 30], [17, 18], [4, 30], [0, 1]], ![[0, 1], [19, 1], [18, 13], [16, 1], [19, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [6, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N1 : CertifiedPrimeIdeal' SI31N1 31 where
  n := 2
  hpos := by decide
  P := [21, 12, 1]
  hirr := P31P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![35286, -38862, 30199, -102688, 308924]
  a := ![7, -44, -32, 93, 78]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-69423, -85344, 30199, -102688, 308924]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N1 B_one_repr
lemma NI31N1 : Nat.card (O ⧸ I31N1) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![31, 0, 0, 0, 0], ![81, -67, 26, 1, 13]] ![![31, 0, 0, 0, 0], ![-5, -15, 2, 0, 1]]
  ![![31, 0, 0, 0, 0]] where
 M := ![![![961, 0, 0, 0, 0], ![-155, -465, 62, 0, 31]], ![![2511, -2077, 806, 31, 403], ![-1581, 651, -155, -124, -93]]]
 hmul := by decide  
 g := ![![![![31, 0, 0, 0, 0]], ![![-5, -15, 2, 0, 1]]], ![![![81, -67, 26, 1, 13]], ![![-51, 21, -5, -4, -3]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0)
instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0, 0, 0], ![45, -26, 14, 1, 7]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0, 0, 0], ![45, -26, 14, 1, 7]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![3, 28, 20, 1, 0], ![6, 24, 15, 0, 1]] where
  M :=![![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![0, 0, 0, 0, 37]], ![![45, -26, 14, 1, 7], ![42, -5, 8, 10, 2], ![4, 14, -17, 60, 20], ![54, -22, 30, -1, 28], ![52, -20, 49, -42, -32]]]
  hmulB := by decide  
  f := ![![![2224, 912, 114, 1083, -171], ![2109, -4218, 0, 0, 0]], ![![-393, -138, -26, -181, 25], ![-333, 703, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![-111, -34, -8, -49, 6], ![-86, 190, 0, 0, 0]], ![![96, 64, -1, 58, -13], ![134, -228, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-3, -28, -20, 37, 0], ![-6, -24, -15, 0, 37]], ![![0, -6, -3, 1, 7], ![0, -9, -6, 10, 2], ![-8, -58, -41, 60, 20], ![-3, -18, -10, -1, 28], ![10, 52, 37, -42, -32]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [2, 2, 7, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 23, 36], [13, 13, 1], [0, 1]]
 g := ![![[10, 26, 3], [30, 1], [3, 21, 26], [30, 1], []], ![[11, 6, 12, 34], [23, 21], [9, 25, 32, 25], [23, 21], [21, 1]], ![[10, 3], [15, 11], [13, 25, 5, 30], [15, 11], [19, 1]]]
 h' := ![![[17, 23, 36], [13, 12, 22], [31, 0, 36], [14, 12, 10], [0, 0, 1], [0, 1]], ![[13, 13, 1], [27, 10, 15], [6, 2, 24], [24, 34, 7], [25, 35, 13], [17, 23, 36]], ![[0, 1], [17, 15], [11, 35, 14], [0, 28, 20], [20, 2, 23], [13, 13, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31, 20], []]
 b := ![[], [16, 19, 20], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [2, 2, 7, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2096689460, 973778844, -2343521706, 2802981902, 419279020]
  a := ![-34, 30, -9, 9, -73]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-351927278, -2366821916, -1748441758, 2802981902, 419279020]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 50653 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0, 0, 0], ![9, 1, 0, 0, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0, 0, 0], ![9, 1, 0, 0, 0]] 
 ![![37, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![30, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![33, 0, 0, 0, 1]] where
  M :=![![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![0, 0, 0, 0, 37]], ![![9, 1, 0, 0, 0], ![0, 9, 1, 0, 0], ![-2, -1, 6, 7, 0], ![0, -1, -1, 12, 2], ![10, -5, 11, -13, 9]]]
  hmulB := by decide  
  f := ![![![-91781774, -11343018, 1440336, 1807857, 768], ![375206973, 3882114, -9531459, -14208, 0]], ![![-22939830, -2835069, 359995, 451854, 192], ![93778795, 970325, -2382282, -3552, 0]], ![![-74573166, -9216264, 1170280, 1468893, 624], ![304857606, 3154251, -7744359, -11544, 0]], ![![-17208830, -2126792, 270058, 338968, 144], ![70350275, 727916, -1787121, -2664, 0]], ![![-81859422, -10116746, 1284624, 1612413, 685], ![334644065, 3462426, -8501031, -12672, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-9, 37, 0, 0, 0], ![-30, 0, 37, 0, 0], ![-7, 0, 0, 37, 0], ![-33, 0, 0, 0, 37]], ![![0, 1, 0, 0, 0], ![-3, 9, 1, 0, 0], ![-6, -1, 6, 7, 0], ![-3, -1, -1, 12, 2], ![-13, -5, 11, -13, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0, 0, 0], ![-4, 1, 0, 0, 0]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![37, 0, 0, 0, 0], ![-4, 1, 0, 0, 0]] 
 ![![37, 0, 0, 0, 0], ![33, 1, 0, 0, 0], ![21, 0, 1, 0, 0], ![36, 0, 0, 1, 0], ![8, 0, 0, 0, 1]] where
  M :=![![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![0, 0, 0, 0, 37]], ![![-4, 1, 0, 0, 0], ![0, -4, 1, 0, 0], ![-2, -1, -7, 7, 0], ![0, -1, -1, -1, 2], ![10, -5, 11, -13, -4]]]
  hmulB := by decide  
  f := ![![![69847401, -17206620, 2111545, -2062380, -2160], ![640635020, -1739185, 10906860, 39960, 0]], ![![64022753, -15771741, 1935461, -1890396, -1980], ![587211794, -1594145, 9997326, 36630, 0]], ![![40740293, -10036204, 1231613, -1202936, -1260], ![373666852, -1014428, 6361706, 23310, 0]], ![![67907380, -16728706, 2052897, -2005097, -2100], ![622841296, -1690899, 10603920, 38850, 0]], ![![15102144, -3720350, 456550, -445920, -467], ![138515710, -376030, 2358240, 8640, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-33, 37, 0, 0, 0], ![-21, 0, 37, 0, 0], ![-36, 0, 0, 37, 0], ![-8, 0, 0, 0, 37]], ![![-1, 1, 0, 0, 0], ![3, -4, 1, 0, 0], ![-2, -1, -7, 7, 0], ![2, -1, -1, -1, 2], ![12, -5, 11, -13, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0, 0, 0], ![45, -26, 14, 1, 7]] ![![37, 0, 0, 0, 0], ![9, 1, 0, 0, 0]]
  ![![37, 0, 0, 0, 0], ![47, 5, 15, 14, 7]] where
 M := ![![![1369, 0, 0, 0, 0], ![333, 37, 0, 0, 0]], ![![1665, -962, 518, 37, 259], ![447, -239, 134, 19, 65]]]
 hmul := by decide  
 g := ![![![![-10, -5, -15, -14, -7], ![37, 0, 0, 0, 0]], ![![-38, -4, -15, -14, -7], ![37, 0, 0, 0, 0]]], ![![![-2, -31, -1, -13, 0], ![37, 0, 0, 0, 0]], ![![-40, -12, -13, -15, -6], ![41, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![37, 0, 0, 0, 0], ![47, 5, 15, 14, 7]] ![![37, 0, 0, 0, 0], ![-4, 1, 0, 0, 0]]
  ![![37, 0, 0, 0, 0]] where
 M := ![![![1369, 0, 0, 0, 0], ![-148, 37, 0, 0, 0]], ![![1739, 185, 555, 518, 259], ![-148, -37, -37, 0, 0]]]
 hmul := by decide  
 g := ![![![![37, 0, 0, 0, 0]], ![![-4, 1, 0, 0, 0]]], ![![![47, 5, 15, 14, 7]], ![![-4, -1, -1, 0, 0]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-57, 97, -33, 0, -18]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![-57, 97, -33, 0, -18]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![3, 22, 13, 1, 0], ![10, 6, 36, 0, 1]] where
  M :=![![![-57, 97, -33, 0, -18], ![-114, 66, -2, 3, 0], ![4, -115, 69, -5, 6], ![-42, -25, -16, 54, -4], ![4, -17, 20, -31, 63]]]
  hmulB := by decide  
  f := ![![![-8499, 4729, -3725, -1866, -2192]], ![![-14470, 8052, -6342, -3177, -3732]], ![![-24636, 13709, -10797, -5409, -6354]], ![![-16711, 9299, -7324, -3669, -4310]], ![![-25966, 14449, -11380, -5701, -6697]]]
  g := ![![![3, 5, 15, 0, -18], ![-3, 0, -1, 3, 0], ![-1, -1, -2, -5, 6], ![-4, -29, -14, 54, -4], ![-13, 7, -45, -31, 63]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [27, 12, 21, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 24, 38], [16, 16, 3], [0, 1]]
 g := ![![[12, 1, 16], [31, 40], [17, 18], [19, 20, 1], []], ![[26, 2, 29, 15], [3, 23], [4, 21], [30, 32, 6, 11], [36, 9]], ![[11, 17, 6, 12], [23, 1], [0, 4], [17, 23, 4, 6], [30, 9]]]
 h' := ![![[4, 24, 38], [20, 4, 37], [23, 37, 9], [20, 11, 31], [0, 0, 1], [0, 1]], ![[16, 16, 3], [6, 19, 6], [13, 26, 33], [30, 10, 12], [28, 9, 16], [4, 24, 38]], ![[0, 1], [4, 18, 39], [16, 19, 40], [37, 20, 39], [20, 32, 24], [16, 16, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 29], []]
 b := ![[], [21, 23, 37], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [27, 12, 21, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-254802321, 157932080, -276433440, 458611048, -501927132]
  a := ![38, -8, 34, -70, 42]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![82649655, -168779224, 288560968, 458611048, -501927132]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 68921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8499, 4729, -3725, -1866, -2192]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-8499, 4729, -3725, -1866, -2192]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![14, 29, 1, 0, 0], ![18, 23, 0, 1, 0], ![24, 24, 0, 0, 1]] where
  M :=![![![-8499, 4729, -3725, -1866, -2192], ![-14470, 8052, -6342, -3177, -3732], ![-24636, 13709, -10797, -5409, -6354], ![-21046, 11711, -9224, -4620, -5428], ![-5900, 3283, -2586, -1295, -1521]]]
  hmulB := by decide  
  f := ![![![-57, 97, -33, 0, -18]], ![![-114, 66, -2, 3, 0]], ![![-100, 77, -11, 2, -6]], ![![-90, 79, -16, 3, -8]], ![![-100, 95, -20, 1, -9]]]
  g := ![![![3167, 5080, -3725, -1866, -2192], ![5392, 8649, -6342, -3177, -3732], ![9180, 14725, -10797, -5409, -6354], ![7842, 12579, -9224, -4620, -5428], ![2198, 3526, -2586, -1295, -1521]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P1 : CertificateIrreducibleZModOfList' 41 2 2 5 [35, 25, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 40], [0, 1]]
 g := ![![[30, 10], [16], [21], [24, 10], [1]], ![[26, 31], [16], [21], [20, 31], [1]]]
 h' := ![![[16, 40], [22, 25], [34, 37], [21, 29], [6, 16], [0, 1]], ![[0, 1], [12, 16], [11, 4], [34, 12], [16, 25], [16, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [27, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N1 : CertifiedPrimeIdeal' SI41N1 41 where
  n := 2
  hpos := by decide
  P := [35, 25, 1]
  hirr := P41P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![186923, -111208, 199371, -309641, 298470]
  a := ![17, -44, -17, 67, 80]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-102293, -144744, 199371, -309641, 298470]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N1 B_one_repr
lemma NI41N1 : Nat.card (O ⧸ I41N1) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![-57, 97, -33, 0, -18]] ![![-8499, 4729, -3725, -1866, -2192]]
  ![![41, 0, 0, 0, 0]] where
 M := ![![![41, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0, 0, 0], ![-39, 87, -15, 7, -8]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0, 0, 0], ![-39, 87, -15, 7, -8]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![21, 16, 18, 26, 1]] where
  M :=![![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![0, 0, 0, 0, 43]], ![![-39, 87, -15, 7, -8], ![-50, 9, 37, 20, 14], ![66, -177, 32, 137, 40], ![58, -93, 19, 80, 56], ![182, -105, 199, -219, 23]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![15, -32, 6, -2, 3], ![16, 0, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![-21, -16, -18, -26, 43]], ![![3, 5, 3, 5, -8], ![-8, -5, -5, -8, 14], ![-18, -19, -16, -21, 40], ![-26, -23, -23, -32, 56], ![-7, -11, -5, -19, 23]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 4 2 5 [37, 21, 12, 25, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 31, 16, 32], [25, 14, 39, 23], [27, 40, 31, 31], [0, 1]]
 g := ![![[23, 8, 42, 41], [42, 16, 14, 16], [12, 17, 35], [18, 1], []], ![[24, 20, 33, 39, 25, 20], [20, 7, 39, 9, 40, 33], [36, 7, 31], [32, 0, 25, 32, 32, 19], [30, 20, 35]], ![[3, 36, 32, 16, 22, 35], [0, 23, 29, 17, 39, 36], [42, 28, 13], [38, 9, 36, 0, 11, 4], [28, 7, 13]], ![[41, 41, 6, 17, 19, 35], [33, 42, 2, 29, 11, 1], [33, 33, 31], [19, 26, 2, 28, 8, 23], [18, 42, 15]]]
 h' := ![![[9, 31, 16, 32], [37, 40, 11, 27], [40, 37, 41, 4], [22, 15, 21, 11], [0, 0, 1], [0, 1]], ![[25, 14, 39, 23], [5, 24, 31, 7], [11, 25, 28, 30], [15, 6, 20, 26], [3, 5, 34, 15], [9, 31, 16, 32]], ![[27, 40, 31, 31], [35, 28, 11, 40], [15, 14, 40, 14], [8, 24, 3, 23], [19, 25, 21, 24], [25, 14, 39, 23]], ![[0, 1], [28, 37, 33, 12], [4, 10, 20, 38], [35, 41, 42, 26], [20, 13, 30, 4], [27, 40, 31, 31]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [13, 13, 38], []]
 b := ![[], [], [41, 7, 31, 32], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 4
  hpos := by decide
  P := [37, 21, 12, 25, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5440028024, 2136750930, -6162974071, 6110710936, 6533181920]
  a := ![11, 0, 12, -27, 8]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3317136008, -2381259530, -2878145317, -3808186488, 6533181920]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 3418801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0, 0, 0], ![-9, 1, 0, 0, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0, 0, 0], ![-9, 1, 0, 0, 0]] 
 ![![43, 0, 0, 0, 0], ![34, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![19, 0, 0, 0, 1]] where
  M :=![![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![0, 0, 0, 0, 43]], ![![-9, 1, 0, 0, 0], ![0, -9, 1, 0, 0], ![-2, -1, -12, 7, 0], ![0, -1, -1, -6, 2], ![10, -5, 11, -13, -9]]]
  hmulB := by decide  
  f := ![![![89481873, -10078076, 2152718, -1224898, -2442], ![425842416, -1681859, 7569376, 52503, 0]], ![![72552532, -8171374, 1745439, -993156, -1980], ![345276026, -1363659, 6137304, 42570, 0]], ![![12090065, -1361662, 290857, -165498, -330], ![57536374, -227211, 1022712, 7095, 0]], ![![14510649, -1634291, 349091, -198633, -396], ![69055884, -272735, 1227472, 8514, 0]], ![![39538515, -4453105, 951201, -541234, -1079], ![188162990, -743148, 3344608, 23199, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-34, 43, 0, 0, 0], ![-5, 0, 43, 0, 0], ![-7, 0, 0, 43, 0], ![-19, 0, 0, 0, 43]], ![![-1, 1, 0, 0, 0], ![7, -9, 1, 0, 0], ![1, -1, -12, 7, 0], ![1, -1, -1, -6, 2], ![9, -5, 11, -13, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0, 0, 0], ![-39, 87, -15, 7, -8]] ![![43, 0, 0, 0, 0], ![-9, 1, 0, 0, 0]]
  ![![43, 0, 0, 0, 0]] where
 M := ![![![1849, 0, 0, 0, 0], ![-387, 43, 0, 0, 0]], ![![-1677, 3741, -645, 301, -344], ![301, -774, 172, -43, 86]]]
 hmul := by decide  
 g := ![![![![43, 0, 0, 0, 0]], ![![-9, 1, 0, 0, 0]]], ![![![-39, 87, -15, 7, -8]], ![![7, -18, 4, -1, 2]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0, 0, 0], ![-46, 106, -13, 13, -7]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0, 0, 0], ![-46, 106, -13, 13, -7]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![20, 5, 22, 25, 1]] where
  M :=![![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![0, 0, 0, 0, 47]], ![![-46, 106, -13, 13, -7], ![-44, -11, 55, 39, 26], ![150, -268, 71, 164, 78], ![136, -154, 65, 76, 82], ![194, -116, 204, -204, 5]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![20, -45, 6, -5, 3], ![20, 0, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![-20, -5, -22, -25, 47]], ![![2, 3, 3, 4, -7], ![-12, -3, -11, -13, 26], ![-30, -14, -35, -38, 78], ![-32, -12, -37, -42, 82], ![2, -3, 2, -7, 5]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 4 2 5 [40, 45, 23, 37, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 31, 8, 28], [44, 22, 21, 41], [11, 40, 18, 25], [0, 1]]
 g := ![![[7, 18, 46, 3], [4, 39, 6, 42], [15, 16, 20, 7], [10, 1], []], ![[36, 41, 10, 38, 13, 4], [15, 41, 43, 34], [40, 44, 21, 39, 38, 18], [13, 41, 33, 18, 18, 42], [2, 16, 32]], ![[5, 7, 3, 33, 1, 43], [19, 3, 25, 35, 45, 23], [18, 24, 10, 0, 17, 43], [20, 27, 12, 24, 13, 30], [6, 14, 36]], ![[17, 29, 45, 24, 18, 36], [43, 7, 36, 39, 5, 8], [17, 40, 36, 20, 46, 24], [31, 36, 11, 20, 29, 42], [41, 6, 14]]]
 h' := ![![[2, 31, 8, 28], [28, 26, 32, 12], [11, 13, 35, 29], [23, 27, 7, 30], [0, 0, 1], [0, 1]], ![[44, 22, 21, 41], [15, 16, 11, 36], [7, 29, 21], [34, 1, 6, 2], [18, 5, 28, 42], [2, 31, 8, 28]], ![[11, 40, 18, 25], [14, 4, 24, 19], [20, 17, 21, 2], [45, 28, 33, 19], [4, 25, 30, 18], [44, 22, 21, 41]], ![[0, 1], [7, 1, 27, 27], [4, 35, 17, 16], [13, 38, 1, 43], [32, 17, 35, 34], [11, 40, 18, 25]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [26, 28, 22], []]
 b := ![[], [], [33, 23, 20, 35], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 4
  hpos := by decide
  P := [40, 45, 23, 37, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1336294144208, 1133965611602, -1384973297361, 3316545784669, -6903670063320]
  a := ![38, -32, 16, -13, 79]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2909300151536, 758559913366, 3202037619057, 3742729731227, -6903670063320]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 4879681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0, 0, 0], ![-3, 1, 0, 0, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0, 0, 0], ![-3, 1, 0, 0, 0]] 
 ![![47, 0, 0, 0, 0], ![44, 1, 0, 0, 0], ![38, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![41, 0, 0, 0, 1]] where
  M :=![![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![0, 0, 0, 0, 47]], ![![-3, 1, 0, 0, 0], ![0, -3, 1, 0, 0], ![-2, -1, -6, 7, 0], ![0, -1, -1, 0, 2], ![10, -5, 11, -13, -3]]]
  hmulB := by decide  
  f := ![![![-43363589, 13823196, -2474326, 2866248, 760], ![-666533038, 806614, -19244808, -17860, 0]], ![![-41079890, 13095211, -2344018, 2715300, 720], ![-631430758, 764126, -18231300, -16920, 0]], ![![-36520118, 11641672, -2083837, 2413908, 640], ![-561343416, 679292, -16207668, -15040, 0]], ![![-4564475, 1455037, -260449, 301703, 80], ![-70159630, 84903, -2025720, -1880, 0]], ![![-37827815, 12058532, -2158454, 2500344, 663], ![-581443766, 703614, -16788024, -15580, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-44, 47, 0, 0, 0], ![-38, 0, 47, 0, 0], ![-5, 0, 0, 47, 0], ![-41, 0, 0, 0, 47]], ![![-1, 1, 0, 0, 0], ![2, -3, 1, 0, 0], ![5, -1, -6, 7, 0], ![0, -1, -1, 0, 2], ![0, -5, 11, -13, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0, 0, 0], ![-46, 106, -13, 13, -7]] ![![47, 0, 0, 0, 0], ![-3, 1, 0, 0, 0]]
  ![![47, 0, 0, 0, 0]] where
 M := ![![![2209, 0, 0, 0, 0], ![-141, 47, 0, 0, 0]], ![![-2162, 4982, -611, 611, -329], ![94, -329, 94, 0, 47]]]
 hmul := by decide  
 g := ![![![![47, 0, 0, 0, 0]], ![![-3, 1, 0, 0, 0]]], ![![![-46, 106, -13, 13, -7]], ![![2, -7, 2, 0, 1]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1957, 1088, -858, -432, -492]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-1957, 1088, -858, -432, -492]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![28, 37, 36, 50, 1]] where
  M :=![![![-1957, 1088, -858, -432, -492], ![-3204, 1793, -1318, -906, -864], ![-6004, 3340, -2851, -712, -1812], ![-5364, 2944, -2702, -349, -1244], ![-76, 104, 826, -2180, 179]]]
  hmulB := by decide  
  f := ![![![-313, -488, 246, 128, 164]], ![![1148, -1507, 450, -26, 256]], ![![1660, -556, -15, -256, -52]], ![![716, -280, 10, -105, -12]], ![![2444, -1955, 444, -224, 219]]]
  g := ![![![223, 364, 318, 456, -492], ![396, 637, 562, 798, -864], ![844, 1328, 1177, 1696, -1812], ![556, 924, 794, 1167, -1244], ![-96, -123, -106, -210, 179]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 4 2 5 [27, 14, 21, 37, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [47, 15, 33, 36], [12, 51, 42, 3], [10, 39, 31, 14], [0, 1]]
 g := ![![[12, 24, 42, 16], [32, 10, 16], [26, 32, 13, 6], [23, 16, 1], []], ![[37, 50, 18, 0, 32, 25], [8, 45, 40], [44, 11, 2, 6, 8, 28], [20, 47, 13], [35, 29, 18, 37, 35, 16]], ![[37, 33, 13, 19, 35, 39], [50, 3, 1], [44, 28, 17, 44, 26, 26], [26, 6, 25], [32, 41, 11, 31, 29, 27]], ![[18, 22, 29, 0, 46, 20], [37, 35, 52], [12, 19, 47, 43, 1, 30], [16, 10, 15], [31, 50, 0, 43, 16, 41]]]
 h' := ![![[47, 15, 33, 36], [47, 26, 13, 4], [40, 4, 44, 49], [15, 41, 8, 18], [0, 0, 0, 1], [0, 1]], ![[12, 51, 42, 3], [32, 31, 6, 8], [6, 16, 12, 26], [15, 13, 12, 25], [5, 29, 7, 15], [47, 15, 33, 36]], ![[10, 39, 31, 14], [3, 13, 45, 38], [9, 50, 20, 1], [31, 29, 20, 37], [16, 19, 50, 48], [12, 51, 42, 3]], ![[0, 1], [12, 36, 42, 3], [51, 36, 30, 30], [8, 23, 13, 26], [4, 5, 49, 42], [10, 39, 31, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [47, 28, 7], []]
 b := ![[], [], [18, 28, 43, 33], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 4
  hpos := by decide
  P := [27, 14, 21, 37, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![446799513526, -162365896364, 508954887400, -462756078173, -719966191510]
  a := ![19, -20, 2, 3, 46]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![388789676902, 499554399802, 498636561920, 670482141459, -719966191510]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 7890481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![313, 488, -246, -128, -164]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![313, 488, -246, -128, -164]] 
 ![![53, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![17, 0, 1, 0, 0], ![16, 0, 0, 1, 0], ![19, 0, 0, 0, 1]] where
  M :=![![![313, 488, -246, -128, -164], ![-1148, 1507, -450, 26, -256], ![-1660, 556, 15, 256, 52], ![-716, 280, -10, 105, 12], ![-260, 176, -34, 28, -15]]]
  hmulB := by decide  
  f := ![![![1957, -1088, 858, 432, 492]], ![![282, -157, 122, 66, 72]], ![![741, -412, 329, 152, 192]], ![![692, -384, 310, 137, 172]], ![![703, -392, 292, 196, 173]]]
  g := ![![![127, 488, -246, -128, -164], ![36, 1507, -450, 26, -256], ![-195, 556, 15, 256, 52], ![-78, 280, -10, 105, 12], ![-17, 176, -34, 28, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-1957, 1088, -858, -432, -492]] ![![313, 488, -246, -128, -164]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-73137, 40696, -32054, -16056, -18862]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-73137, 40696, -32054, -16056, -18862]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![24, 14, 24, 1, 0], ![48, 12, 13, 0, 1]] where
  M :=![![![-73137, 40696, -32054, -16056, -18862], ![-124512, 69283, -54568, -27340, -32112], ![-211984, 117956, -92905, -46540, -54680], ![-181104, 100772, -79380, -39741, -46708], ![-50752, 28240, -22234, -11168, -13075]]]
  hmulB := by decide  
  f := ![![![885, -1072, 310, -32, 174]], ![![1120, -263, -56, -188, -64]], ![![-528, 1684, -611, -124, -376]], ![![408, 198, -140, -109, -100]], ![![832, -552, 105, -92, 45]]]
  g := ![![![20637, 8336, 10144, -16056, -18862], ![35136, 14193, 17272, -27340, -32112], ![59824, 24164, 29405, -46540, -54680], ![51096, 20638, 25112, -39741, -46708], ![14320, 5788, 7047, -11168, -13075]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [31, 6, 31, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [10, 48, 14], [18, 10, 45], [0, 1]]
 g := ![![[13, 19, 48], [7, 7, 27], [40, 53], [53, 22, 17], [1]], ![[45, 43, 49, 44], [58, 35, 46, 10], [25, 12], [40, 12, 33, 39], [39, 49, 36, 30]], ![[57, 40, 21, 45], [18, 40, 45, 29], [19, 25], [24, 13, 5, 49], [13, 7, 25, 29]]]
 h' := ![![[10, 48, 14], [19, 5, 15], [21, 11, 33], [9, 20, 17], [28, 53, 28], [0, 1]], ![[18, 10, 45], [10, 41, 43], [13, 43, 12], [32, 54, 37], [27, 21, 19], [10, 48, 14]], ![[0, 1], [7, 13, 1], [30, 5, 14], [41, 44, 5], [1, 44, 12], [18, 10, 45]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 9], []]
 b := ![[], [47, 45, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [31, 6, 31, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![159644107, -81101736, 176924201, -234053675, 65251662]
  a := ![7, -18, -8, 27, 33]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![44828009, 40892030, 83829505, -234053675, 65251662]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 205379 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![885, -1072, 310, -32, 174]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![885, -1072, 310, -32, 174]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![21, 6, 1, 0, 0], ![16, 34, 0, 1, 0], ![13, 5, 0, 0, 1]] where
  M :=![![![885, -1072, 310, -32, 174], ![1120, -263, -56, -188, -64], ![-528, 1684, -611, -124, -376], ![-176, 676, -252, -55, -156], ![32, 152, -70, -24, -41]]]
  hmulB := by decide  
  f := ![![![-73137, 40696, -32054, -16056, -18862]], ![![-124512, 69283, -54568, -27340, -32112]], ![![-42287, 23530, -18533, -9284, -10906]], ![![-94656, 52670, -41484, -20783, -24412]], ![![-27527, 15317, -12064, -6044, -7099]]]
  g := ![![![-125, -46, 310, -32, 174], ![104, 115, -56, -188, -64], ![325, 194, -611, -124, -376], ![136, 82, -252, -55, -156], ![41, 27, -70, -24, -41]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P1 : CertificateIrreducibleZModOfList' 59 2 2 5 [36, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [45, 58], [0, 1]]
 g := ![![[43, 41], [17, 25], [48], [58, 53], [45, 1]], ![[0, 18], [21, 34], [48], [24, 6], [31, 58]]]
 h' := ![![[45, 58], [37, 49], [40, 54], [36, 15], [32, 42], [0, 1]], ![[0, 1], [0, 10], [51, 5], [3, 44], [34, 17], [45, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [2, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N1 : CertifiedPrimeIdeal' SI59N1 59 where
  n := 2
  hpos := by decide
  P := [36, 14, 1]
  hirr := P59P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![823600, -406240, 915032, -1170410, 166345]
  a := ![-50, 32, -35, 45, -89]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-30983, 560437, 915032, -1170410, 166345]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N1 B_one_repr
lemma NI59N1 : Nat.card (O ⧸ I59N1) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-73137, 40696, -32054, -16056, -18862]] ![![885, -1072, 310, -32, 174]]
  ![![59, 0, 0, 0, 0]] where
 M := ![![![59, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1080671419, 601323685, -473626353, -237250460, -278709080]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![-1080671419, 601323685, -473626353, -237250460, -278709080]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![35, 15, 56, 9, 1]] where
  M :=![![![-1080671419, 601323685, -473626353, -237250460, -278709080], ![-1839838094, 1023750794, -806346676, -403917811, -474500920], ![-3132315848, 1742930993, -1372801487, -687668205, -807835622], ![-2675840246, 1488931871, -1172741718, -587453612, -690108908], ![-750119424, 417392899, -328755180, -164681119, -193458521]]]
  hmulB := by decide  
  f := ![![![-69, 121, -53, 14, -26]], ![![-154, 100, -20, 9, 28]], ![![320, -283, 459, -477, 18]], ![![-10, -37, 38, 22, -132]], ![![205, -167, 381, -412, -7]]]
  g := ![![![142199121, 78392785, 248099707, 37231660, -278709080], ![242093346, 133463354, 422388604, 63386729, -474500920], ![412162802, 227220743, 719114645, 107915613, -807835622], ![352097894, 194107631, 614317330, 92188960, -690108908], ![98703751, 54414274, 172211836, 25843370, -193458521]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 4 2 5 [52, 15, 33, 50, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [14, 30, 26, 41], [44, 19, 24, 1], [14, 11, 11, 19], [0, 1]]
 g := ![![[49, 23, 57, 13], [36, 30, 9], [26, 47, 51, 13], [41, 27, 11, 1], []], ![[23, 31, 52, 43, 7, 60], [24, 3, 12], [16, 28, 9, 28, 47, 36], [24, 46, 14, 43, 48, 39], [39, 24, 37, 30, 52, 52]], ![[19, 39, 32, 35, 50, 42], [40, 43, 1], [5, 30, 16, 57, 22, 3], [48, 56, 44, 56, 16, 36], [0, 36, 4, 42, 22, 1]], ![[15, 42, 28, 13, 32, 12], [55, 42, 34], [10, 35, 11, 1, 8, 34], [18, 0, 52, 58, 31, 3], [41, 58, 36, 34, 10, 27]]]
 h' := ![![[14, 30, 26, 41], [58, 49, 10, 14], [51, 42, 19, 3], [3, 55, 49, 14], [0, 0, 0, 1], [0, 1]], ![[44, 19, 24, 1], [17, 19, 15, 34], [44, 4, 36, 16], [18, 2, 51, 13], [45, 8, 46, 19], [14, 30, 26, 41]], ![[14, 11, 11, 19], [52, 53, 27, 46], [34, 38, 16, 1], [36, 19, 52, 8], [28, 22, 2, 55], [44, 19, 24, 1]], ![[0, 1], [48, 1, 9, 28], [38, 38, 51, 41], [35, 46, 31, 26], [2, 31, 13, 47], [14, 11, 11, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [57, 57, 38], []]
 b := ![[], [], [20, 9, 53, 23], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 4
  hpos := by decide
  P := [52, 15, 33, 50, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-378553438814, 227160661751, -412252967623, 659122981895, -641562614597]
  a := ![-22, 17, -11, 13, -43]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![361903902821, 161485243946, 582217269669, 105462073988, -641562614597]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 13845841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![69, -121, 53, -14, 26]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![69, -121, 53, -14, 26]] 
 ![![61, 0, 0, 0, 0], ![43, 1, 0, 0, 0], ![42, 0, 1, 0, 0], ![36, 0, 0, 1, 0], ![38, 0, 0, 0, 1]] where
  M :=![![![69, -121, 53, -14, 26], ![154, -100, 20, -9, -28], ![-320, 283, -459, 477, -18], ![10, 37, -38, -22, 132], ![600, -259, 650, -757, -243]]]
  hmulB := by decide  
  f := ![![![1080671419, -601323685, 473626353, 237250460, 278709080]], ![![791946051, -440666709, 347086555, 173863731, 204245760]], ![![795418286, -442598783, 348608333, 174626025, 205141262]], ![![681639530, -379288271, 298742466, 149647052, 175797308]], ![![685502186, -381437589, 300435354, 150495059, 176793501]]]
  g := ![![![42, -121, 53, -14, 26], ![82, -100, 20, -9, -28], ![-159, 283, -459, 477, -18], ![-69, 37, -38, -22, 132], ![343, -259, 650, -757, -243]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![-1080671419, 601323685, -473626353, -237250460, -278709080]] ![![69, -121, 53, -14, 26]]
  ![![61, 0, 0, 0, 0]] where
 M := ![![![-61, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0)


lemma PB1535I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB1535I1 : PrimesBelowBoundCertificateInterval O 23 61 1535 where
  m := 9
  g := ![3, 2, 3, 2, 2, 2, 2, 2, 2]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB1535I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0, I29N1, I29N2]
    · exact ![I31N0, I31N1]
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1]
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
    · exact ![841, 841, 29]
    · exact ![29791, 961]
    · exact ![50653, 37, 37]
    · exact ![68921, 1681]
    · exact ![3418801, 43]
    · exact ![4879681, 47]
    · exact ![7890481, 53]
    · exact ![205379, 3481]
    · exact ![13845841, 61]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
      exact NI29N2
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
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
      exact NI43N1
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
  β := ![I29N0, I29N1, I29N2, I31N1, I37N1, I37N2, I43N1, I47N1, I53N1, I61N1]
  Il := ![[I29N0, I29N1, I29N2], [I31N1], [I37N1, I37N2], [], [I43N1], [I47N1], [I53N1], [], [I61N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
