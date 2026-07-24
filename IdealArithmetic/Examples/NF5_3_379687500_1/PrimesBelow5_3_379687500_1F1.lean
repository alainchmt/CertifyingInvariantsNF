
import IdealArithmetic.Examples.NF5_3_379687500_1.RI5_3_379687500_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-133, 93, 1014, -315, -598]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![-133, 93, 1014, -315, -598]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![0, 0, 0, 29, 0], ![9, 19, 21, 3, 1]] where
  M :=![![![-133, 93, 1014, -315, -598], ![32, -448, -254, -753, -3064], ![-1558, -721, 357, 5329, 20462], ![9804, 3771, -5196, -31822, -124036], ![-5302, -1984, 2902, 17218, 67171]]]
  hmulB := by decide  
  f := ![![![-1385, 569, -2532, 1075, 2770]], ![![620, -310, 1024, -877, -1940]], ![![-186, -257, -1001, -2245, -3854]], ![![636, -2431, -3138, -16042, -28772]], ![![-101, -441, -1141, -3379, -5913]]]
  g := ![![![181, 395, 468, 51, -598], ![952, 1992, 2210, 291, -3064], ![-6404, -13431, -14805, -1933, 20462], ![38832, 81395, 89640, 11734, -124036], ![-21029, -44077, -48541, -6355, 67171]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 4 2 4 [4, 23, 4, 2, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 28, 20, 3], [14, 18, 27, 23], [5, 11, 11, 3], [0, 1]]
 g := ![![[27, 18, 1, 5], [7, 4, 22], [14, 0, 27, 1], []], ![[26, 24, 12, 21, 1, 26], [4, 5, 22], [19, 7, 15, 8, 0, 11], [14, 5, 15, 28, 22, 27]], ![[3, 15, 16, 15, 6, 13], [4, 16, 7], [2, 13, 24, 1, 22, 20], [7, 13, 5, 13, 13, 16]], ![[1, 19, 25, 6, 7, 14], [11, 4, 7], [13, 2, 9, 1, 23, 8], [11, 14, 3, 9, 11, 27]]]
 h' := ![![[8, 28, 20, 3], [5, 14, 15, 11], [2, 26, 10, 14], [0, 0, 0, 1], [0, 1]], ![[14, 18, 27, 23], [14, 17, 1, 17], [1, 21, 20, 15], [21, 17, 8, 9], [8, 28, 20, 3]], ![[5, 11, 11, 3], [13, 18, 3, 14], [0, 26, 12, 23], [19, 18, 21, 4], [14, 18, 27, 23]], ![[0, 1], [13, 9, 10, 16], [12, 14, 16, 6], [23, 23, 0, 15], [5, 11, 11, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [27, 4, 5], []]
 b := ![[], [], [11, 24, 23, 25], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 4
  hpos := by decide
  P := [4, 23, 4, 2, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-275005438892, 487872537540, 849503541870, 4160707565520, 8524151598900]
  a := ![5, -3, -9, -44, -105]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2654909304448, -5567965787640, -6143368277070, -738336111420, 8524151598900]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 707281 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1385, -569, 2532, -1075, -2770]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![1385, -569, 2532, -1075, -2770]] 
 ![![29, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![9, 0, 1, 0, 0], ![24, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![1385, -569, 2532, -1075, -2770], ![-620, 310, -1024, 877, 1940], ![186, 257, 1001, 2245, 3854], ![-636, 2431, 3138, 16042, 28772], ![246, -670, -678, -4268, -7703]]]
  hmulB := by decide  
  f := ![![![133, -93, -1014, 315, 598]], ![![31, -7, -236, 102, 250]], ![![95, -4, -327, -86, -520]], ![![-228, -207, -660, 1358, 4772]], ![![192, 62, -170, -572, -2275]]]
  g := ![![![480, -569, 2532, -1075, -2770], ![-638, 310, -1024, 877, 1940], ![-2490, 257, 1001, 2245, 3854], ![-16843, 2431, 3138, 16042, 28772], ![4444, -670, -678, -4268, -7703]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![-133, 93, 1014, -315, -598]] ![![1385, -569, 2532, -1075, -2770]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0, 0, 0]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]] where
  M :=![![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 5 2 4 [23, 26, 22, 15, 2, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 2, 4, 20, 28], [26, 10, 13, 24, 8], [23, 19, 15, 21, 15], [30, 30, 30, 28, 11], [0, 1]]
 g := ![![[17, 5, 7, 10, 14], [4, 11, 2, 4, 1], [20, 29, 1], []], ![[15, 9, 23, 2, 21, 4, 3, 16], [11, 11, 5, 19, 26, 5, 7, 4], [25, 24, 23, 12, 10, 14, 14, 28], [27, 15, 1, 8, 28, 3, 5, 4]], ![[19, 20, 19, 6, 8, 12, 2, 10], [1, 22, 20, 0, 3, 3, 1, 16], [6, 1, 18, 5, 7, 21, 30, 9], [0, 3, 2, 2, 14, 15, 19, 16]], ![[5, 17, 30, 2, 7, 5, 30, 6], [13, 26, 14, 22, 11, 9, 30, 30], [6, 26, 21, 25, 25, 27, 24, 24], [8, 16, 1, 12, 22, 21, 16, 27]], ![[8, 14, 3, 17, 26, 21, 30, 30], [17, 2, 0, 0, 6, 1, 29, 30], [28, 28, 5, 4, 13, 4, 27, 24], [9, 29, 13, 27, 17, 26, 0, 29]]]
 h' := ![![[12, 2, 4, 20, 28], [1, 9, 17, 20, 18], [5, 22, 23, 28, 30], [0, 0, 0, 1], [0, 1]], ![[26, 10, 13, 24, 8], [24, 30, 7, 18, 25], [25, 17, 13, 4, 3], [22, 3, 28, 2, 1], [12, 2, 4, 20, 28]], ![[23, 19, 15, 21, 15], [1, 6, 2, 26, 28], [12, 7, 3, 4, 8], [30, 30, 2, 7, 6], [26, 10, 13, 24, 8]], ![[30, 30, 30, 28, 11], [3, 5, 26, 19, 9], [30, 15, 14, 25, 8], [17, 3, 18, 2, 18], [23, 19, 15, 21, 15]], ![[0, 1], [23, 12, 10, 10, 13], [19, 1, 9, 1, 13], [9, 26, 14, 19, 6], [30, 30, 30, 28, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 13, 28, 28], [], [], []]
 b := ![[], [19, 16, 18, 11, 30], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 5
  hpos := by decide
  P := [23, 26, 22, 15, 2, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![274294458585613652123, -864679530181455428760, -1299000310104301947102, -6243078178969771235772, -11719043701828932877158]
  a := ![59, -60, -118, -533, -1236]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![8848208341471408133, -27892888070369529960, -41903235809816191842, -201389618676444233412, -378033667800933318618]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 28629151 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def PBC31 : ContainsPrimesAboveP 31 ![I31N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![31, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 31 (by decide) 𝕀

instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0, 0, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0, 0, 0]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![0, 0, 0, 0, 37]] where
  M :=![![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![0, 0, 0, 0, 37]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 5 2 5 [8, 34, 26, 8, 14, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 26, 8, 30, 24], [16, 0, 28, 31, 36], [14, 30, 19, 15, 14], [24, 17, 19, 35], [0, 1]]
 g := ![![[27, 36, 6, 28, 34], [25, 0, 22, 33], [23, 7, 3, 23, 1], [], []], ![[1, 0, 13, 25, 16, 31, 0, 13], [14, 19, 34, 7], [32, 21, 16, 13, 17, 2], [10, 7, 16, 34], [22, 20, 36, 21]], ![[3, 27, 29, 34, 28, 15, 31, 30], [14, 1, 31, 33], [26, 13, 28, 34, 24, 19, 13, 1], [12, 27, 11, 26], [24, 0, 35, 1]], ![[35, 15, 11, 11, 21, 22, 21, 5], [30, 9, 31, 9], [17, 6, 5, 10, 20, 17, 0, 18], [34, 29, 34, 36], [30, 16, 7, 11]], ![[12, 31, 33, 20, 34, 24, 29], [8, 11, 16, 12], [17, 22, 4, 24, 10, 15, 18], [24, 3], [16, 4]]]
 h' := ![![[6, 26, 8, 30, 24], [23, 27, 28, 25, 16], [1, 13, 28, 14, 12], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[16, 0, 28, 31, 36], [2, 31, 13, 29, 6], [22, 36, 21, 32, 9], [21, 21, 15, 21], [8, 33, 9, 20, 16], [6, 26, 8, 30, 24]], ![[14, 30, 19, 15, 14], [9, 12, 4, 13, 28], [11, 36, 11, 19, 12], [4, 8, 30, 26, 6], [27, 35, 29, 9, 27], [16, 0, 28, 31, 36]], ![[24, 17, 19, 35], [29, 19, 13, 5, 22], [26, 5, 24, 17, 34], [36, 1, 12, 30, 12], [30, 25, 15, 23, 31], [14, 30, 19, 15, 14]], ![[0, 1], [35, 22, 16, 2, 2], [32, 21, 27, 29, 7], [9, 7, 17, 34, 18], [4, 18, 20, 22], [24, 17, 19, 35]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 25, 27, 24], [], [], []]
 b := ![[], [31, 4, 11, 0, 36], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 5
  hpos := by decide
  P := [8, 34, 26, 8, 14, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![360471694143034, -1198969309717137, -1781939908381505, -8551239411034644, -15933788639084575]
  a := ![4, -3, -7, -36, -83]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![9742478220082, -32404575938301, -48160538064365, -231114578676612, -430642936191475]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 69343957 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def PBC37 : ContainsPrimesAboveP 37 ![I37N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![37, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 37 (by decide) 𝕀

instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 54, 178, -82, -202]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![83, 54, 178, -82, -202]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![8, 36, 1, 0, 0], ![40, 24, 0, 1, 0], ![4, 14, 0, 0, 1]] where
  M :=![![![83, 54, 178, -82, -202], ![-38, 1, 10, -4, -10], ![-2, -42, -1, 2, 2], ![-2, 0, -38, 21, 50], ![6, 6, 24, -12, -29]]]
  hmulB := by decide  
  f := ![![![19, 6, -10, -62, -242]], ![![-118, -43, 62, 388, 1510]], ![![-82, -30, 43, 270, 1050]], ![![-162, -60, 86, 533, 2074]], ![![22, 8, -12, -72, -281]]]
  g := ![![![67, -38, 178, -82, -202], ![2, -3, 10, -4, -10], ![-2, -2, -1, 2, 2], ![-18, 4, -38, 21, 50], ![10, -4, 24, -12, -29]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [3, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 40], [0, 1]]
 g := ![![[1, 40], [9], [40], [32, 9], [1]], ![[4, 1], [9], [40], [5, 32], [1]]]
 h' := ![![[38, 40], [9, 9], [35, 38], [27, 9], [38, 38], [0, 1]], ![[0, 1], [23, 32], [3, 3], [0, 32], [6, 3], [38, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [1, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [3, 3, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-492897, 514515, 1092610, 5464773, 12215592]
  a := ![-26, 23, 50, 230, 547]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6748465, -8316885, 1092610, 5464773, 12215592]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19, -6, 10, 62, 242]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-19, -6, 10, 62, 242]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![40, 18, 5, 1, 0], ![20, 14, 34, 0, 1]] where
  M :=![![![-19, -6, 10, 62, 242], ![118, 43, -62, -388, -1510], ![-734, -270, 389, 2402, 9374], ![4570, 1668, -2438, -15021, -58474], ![-2478, -906, 1320, 8136, 31693]]]
  hmulB := by decide  
  f := ![![![-83, -54, -178, 82, 202]], ![![38, -1, -10, 4, 10]], ![![2, 42, 1, -2, -2]], ![![-64, -48, -177, 81, 200]], ![![-26, 8, -90, 40, 101]]]
  g := ![![![-179, -110, -208, 62, 242], ![1118, 687, 1298, -388, -1510], ![-6934, -4262, -8057, 2402, 9374], ![43290, 26602, 50263, -15021, -58474], ![-23458, -14416, -27242, 8136, 31693]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P1 : CertificateIrreducibleZModOfList' 41 3 2 5 [5, 18, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 12, 36], [13, 28, 5], [0, 1]]
 g := ![![[12, 10, 32], [12, 25], [2, 25], [18, 35, 1], []], ![[8, 25, 1, 32], [30, 37], [40, 37], [29, 4, 28, 16], [17, 25]], ![[29, 18, 37, 20], [17, 37], [0, 5], [1, 37, 3, 23], [7, 25]]]
 h' := ![![[22, 12, 36], [27, 25, 27], [13, 33, 36], [33, 34, 36], [0, 0, 1], [0, 1]], ![[13, 28, 5], [34, 8, 16], [15, 34, 23], [16, 5, 18], [30, 15, 28], [22, 12, 36]], ![[0, 1], [34, 8, 39], [18, 15, 23], [10, 2, 28], [11, 26, 12], [13, 28, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40, 17], []]
 b := ![[], [4, 8, 28], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N1 : CertifiedPrimeIdeal' SI41N1 41 where
  n := 3
  hpos := by decide
  P := [5, 18, 6, 1]
  hirr := P41P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![898880180, -479200614, -1444001492, -7424073956, -18370712584]
  a := ![11, -6, -16, -92, -232]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![16226246100, 9520587970, 16104404784, -7424073956, -18370712584]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N1 B_one_repr
lemma NI41N1 : Nat.card (O ⧸ I41N1) = 68921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![83, 54, 178, -82, -202]] ![![-19, -6, 10, 62, 242]]
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


def P43P0 : CertificateIrreducibleZModOfList' 43 5 2 5 [38, 30, 15, 35, 27, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 20, 28, 35, 8], [27, 21, 41, 13, 7], [26, 14, 37, 40, 14], [30, 30, 23, 41, 14], [0, 1]]
 g := ![![[21, 2, 32, 21, 15], [19, 6, 18, 5, 40], [13, 13, 9, 41], [1], []], ![[16, 11, 20, 4, 34, 18], [39, 5, 25, 39, 10, 30, 17, 30], [0, 0, 40, 24], [23, 6, 25, 41, 6, 13, 29, 26], [32, 9, 36, 21]], ![[20, 5, 3, 37, 32, 29, 17, 12], [30, 3, 16, 17, 19, 10, 27, 29], [5, 0, 19, 4], [3, 8, 20, 19, 19, 41, 39, 5], [28, 36, 20, 6]], ![[39, 20, 29, 16, 41, 10, 28, 13], [33, 35, 34, 12, 38, 20, 28, 17], [4, 25, 28, 16], [1, 7, 25, 41, 16, 38, 8, 6], [31, 17, 42, 24]], ![[19, 17, 23, 39, 14, 14], [28, 34, 19, 37, 26, 31, 5, 36], [21, 9, 10, 16], [23, 41, 38, 6, 27, 25, 28, 6], [15, 25, 27, 24]]]
 h' := ![![[19, 20, 28, 35, 8], [9, 35, 0, 36, 31], [4, 20, 38, 7, 13], [5, 13, 28, 8, 16], [0, 0, 1], [0, 1]], ![[27, 21, 41, 13, 7], [41, 28, 17, 20], [15, 22, 40, 4, 6], [31, 17, 42, 0, 29], [5, 17, 34, 5, 10], [19, 20, 28, 35, 8]], ![[26, 14, 37, 40, 14], [28, 5, 0, 34, 10], [20, 3, 9, 17, 27], [9, 30, 33, 22, 41], [9, 1, 8, 33, 23], [27, 21, 41, 13, 7]], ![[30, 30, 23, 41, 14], [32, 6, 37, 40, 2], [18, 6, 26, 26, 32], [27, 4, 11, 36, 4], [14, 12, 22, 34, 5], [26, 14, 37, 40, 14]], ![[0, 1], [41, 12, 32, 42], [42, 35, 16, 32, 8], [18, 22, 15, 20, 39], [29, 13, 21, 14, 5], [30, 30, 23, 41, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21, 17, 42, 12], [], [], []]
 b := ![[], [35, 11, 25, 28, 20], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 5
  hpos := by decide
  P := [38, 30, 15, 35, 27, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5560991851412674, -2036244941154804, 2958707837584284, 18242997329266200, 71100252549603144]
  a := ![-4, 2, 8, 24, 84]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-129325391893318, -47354533515228, 68807159013588, 424255751843400, 1653494245339608]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17, -33, -229, 182, 402]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-17, -33, -229, 182, 402]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![12, 15, 40, 7, 1]] where
  M :=![![![-17, -33, -229, 182, 402], ![38, 165, 111, 453, 810], ![-96, 491, 714, 2952, 5256], ![-648, 2856, 4091, 19362, 34632], ![170, -751, -1094, -5063, -9049]]]
  hmulB := by decide  
  f := ![![![57, 22, -33, -189, -738]], ![![-360, -132, 193, 1182, 4608]], ![![2244, 822, -1194, -7361, -28692]], ![![-13970, -5117, 7431, 45821, 178602]], ![![-110, -40, 58, 360, 1403]]]
  g := ![![![-103, -129, -347, -56, 402], ![-206, -255, -687, -111, 810], ![-1344, -1667, -4458, -720, 5256], ![-8856, -10992, -29387, -4746, 34632], ![2314, 2872, 7678, 1240, -9049]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 4 2 5 [35, 6, 12, 28, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 27, 13, 29], [4, 10, 6, 43], [0, 9, 28, 22], [0, 1]]
 g := ![![[13, 20, 46, 6], [7, 21, 4, 6], [15, 28, 26, 24], [19, 1], []], ![[43, 2, 0, 41, 33, 5], [20, 44, 25, 18, 31, 11], [17, 23, 11, 26, 36, 46], [15, 22, 7, 30, 31, 11], [28, 1, 42]], ![[41, 16, 27, 19, 26, 39], [10, 38, 36, 40, 37, 30], [11, 12, 35, 35, 31, 19], [36, 14, 7, 46, 12, 19], [22, 21, 16]], ![[0, 42, 2, 42, 0, 43], [2, 19, 7, 40, 10, 5], [7, 14, 15, 8, 0, 19], [1, 30, 5, 43, 26, 29], [5, 41, 14]]]
 h' := ![![[15, 27, 13, 29], [37, 39, 6, 10], [39, 13, 29, 37], [40, 39, 1, 20], [0, 0, 1], [0, 1]], ![[4, 10, 6, 43], [4, 0, 27, 21], [42, 42, 35, 40], [33, 25, 26, 9], [44, 43, 12, 7], [15, 27, 13, 29]], ![[0, 9, 28, 22], [26, 20, 39, 7], [0, 27, 27, 4], [25, 35, 18, 30], [45, 12, 44, 17], [4, 10, 6, 43]], ![[0, 1], [24, 35, 22, 9], [37, 12, 3, 13], [12, 42, 2, 35], [13, 39, 37, 23], [0, 9, 28, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [40, 38, 25], []]
 b := ![[], [], [38, 39, 0, 18], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 4
  hpos := by decide
  P := [35, 6, 12, 28, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-239676160407, 483191672641, 809658706731, 3947273221362, 7922545313137]
  a := ![-4, 8, 13, 41, 97]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2027877019533, -2518191234562, -6725364974867, -1095969020651, 7922545313137]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 4879681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![57, 22, -33, -189, -738]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![57, 22, -33, -189, -738]] 
 ![![47, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![22, 0, 1, 0, 0], ![31, 0, 0, 1, 0], ![10, 0, 0, 0, 1]] where
  M :=![![![57, 22, -33, -189, -738], ![-360, -132, 193, 1182, 4608], ![2244, 822, -1194, -7361, -28692], ![-13970, -5117, 7431, 45821, 178602], ![7576, 2775, -4030, -24849, -96857]]]
  hmulB := by decide  
  f := ![![![-17, -33, -229, 182, 402]], ![![-1, 0, -22, 29, 60]], ![![-10, -5, -92, 148, 300]], ![![-25, 39, -64, 532, 1002]], ![![0, -23, -72, -69, -107]]]
  g := ![![![296, 22, -33, -189, -738], ![-1844, -132, 193, 1182, 4608], ![11479, 822, -1194, -7361, -28692], ![-71454, -5117, 7431, 45821, 178602], ![38750, 2775, -4030, -24849, -96857]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-17, -33, -229, 182, 402]] ![![57, 22, -33, -189, -738]]
  ![![47, 0, 0, 0, 0]] where
 M := ![![![47, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-35201, 14653, -63946, 28773, 72966]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-35201, 14653, -63946, 28773, 72966]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![49, 27, 49, 1, 0], ![34, 37, 7, 0, 1]] where
  M :=![![![-35201, 14653, -63946, 28773, 72966], ![15420, -6428, 28006, -12601, -31956], ![-6754, 2819, -12275, 5525, 14010], ![2960, -1229, 5384, -2410, -6120], ![-2790, 1160, -5070, 2278, 5779]]]
  hmulB := by decide  
  f := ![![![11, 9, 4, -37, -138]], ![![-64, -26, 36, 203, 792]], ![![386, 139, -209, -1265, -4938]], ![![289, 107, -147, -951, -3708]], ![![38, 15, -13, -130, -503]]]
  g := ![![![-74074, -65320, -37445, 28773, 72966], ![32441, 28607, 16399, -12601, -31956], ![-14223, -12542, -7190, 5525, 14010], ![6210, 5477, 3138, -2410, -6120], ![-5866, -5173, -2965, 2278, 5779]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [39, 5, 34, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [27, 39, 11], [45, 13, 42], [0, 1]]
 g := ![![[36, 5, 29], [40, 4], [2, 11, 38], [44, 43], [1]], ![[3, 43, 25, 1], [46, 29], [29, 10, 8, 43], [50, 29], [35, 22, 14, 6]], ![[13, 7], [10, 6], [33, 3, 52, 25], [49, 1], [25, 21, 47, 47]]]
 h' := ![![[27, 39, 11], [19, 42, 20], [28, 9, 51], [17, 30, 12], [14, 48, 19], [0, 1]], ![[45, 13, 42], [18, 14, 33], [40, 47, 20], [40, 26, 9], [33, 43, 33], [27, 39, 11]], ![[0, 1], [47, 50], [15, 50, 35], [6, 50, 32], [50, 15, 1], [45, 13, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 50], []]
 b := ![[], [26, 6, 34], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [39, 5, 34, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4359117, -15676886, -22955926, -109929830, -202706538]
  a := ![2, -3, -4, -20, -43]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![231753643, 197218310, 127972670, -109929830, -202706538]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 148877 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 9, 4, -37, -138]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![11, 9, 4, -37, -138]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![2, 4, 1, 0, 0], ![45, 39, 0, 1, 0], ![34, 28, 0, 0, 1]] where
  M :=![![![11, 9, 4, -37, -138], ![-64, -26, 36, 203, 792], ![386, 139, -209, -1265, -4938], ![-2408, -879, 1282, 7914, 30816], ![1306, 478, -694, -4288, -16705]]]
  hmulB := by decide  
  f := ![![![-35201, 14653, -63946, 28773, 72966]], ![![15420, -6428, 28006, -12601, -31956]], ![![-292, 121, -531, 239, 606]], ![![-18485, 7688, -33584, 15112, 38322]], ![![-14488, 6026, -26322, 11844, 30035]]]
  g := ![![![120, 100, 4, -37, -138], ![-683, -571, 36, 203, 792], ![4257, 3558, -209, -1265, -4938], ![-26582, -22217, 1282, 7914, 30816], ![14408, 12042, -694, -4288, -16705]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P1 : CertificateIrreducibleZModOfList' 53 2 2 5 [28, 51, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 52], [0, 1]]
 g := ![![[34, 36], [7], [21, 46], [46], [2, 1]], ![[0, 17], [7], [7, 7], [46], [4, 52]]]
 h' := ![![[2, 52], [41, 6], [48, 22], [46, 24], [50, 29], [0, 1]], ![[0, 1], [0, 47], [39, 31], [41, 29], [2, 24], [2, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [52, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N1 : CertifiedPrimeIdeal' SI53N1 53 where
  n := 2
  hpos := by decide
  P := [28, 51, 1]
  hirr := P53P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-15166, -704, 14230, 76350, 235344]
  a := ![-3, 3, 13, 23, 66]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-216624, -181602, 14230, 76350, 235344]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N1 B_one_repr
lemma NI53N1 : Nat.card (O ⧸ I53N1) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-35201, 14653, -63946, 28773, 72966]] ![![11, 9, 4, -37, -138]]
  ![![53, 0, 0, 0, 0]] where
 M := ![![![53, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![49, -23, 75, 2, -20]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![49, -23, 75, 2, -20]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![30, 10, 11, 53, 1]] where
  M :=![![![49, -23, 75, 2, -20], ![-24, 51, 3, 229, 424], ![-34, 205, 314, 1352, 2410], ![-294, 1318, 1851, 8838, 15814], ![80, -347, -482, -2317, -4147]]]
  hmulB := by decide  
  f := ![![![3, 4, -1, -1, -4]], ![![-2, 2, 5, 6, 26]], ![![14, 4, -6, -49, -190]], ![![-92, -35, 47, 301, 1172]], ![![-78, -28, 41, 259, 1009]]]
  g := ![![![11, 3, 5, 18, -20], ![-216, -71, -79, -377, 424], ![-1226, -405, -444, -2142, 2410], ![-8046, -2658, -2917, -14056, 15814], ![2110, 697, 765, 3686, -4147]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 4 2 5 [53, 46, 7, 41, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [41, 21, 29, 27], [29, 43, 33, 18], [7, 53, 56, 14], [0, 1]]
 g := ![![[56, 17, 42, 9], [15, 29, 46, 5], [8, 29, 26], [47, 22, 18, 1], []], ![[52, 53, 18, 45, 31, 27], [40, 45, 25, 8, 51, 49], [53, 32, 25], [34, 41, 44, 0, 44, 4], [51, 25, 33, 49, 56, 36]], ![[26, 35, 1, 17, 36, 2], [27, 39, 10, 4, 32, 18], [3, 34, 46], [54, 34, 41, 51, 23, 23], [57, 3, 51, 39, 54, 50]], ![[12, 8, 50, 38, 18, 44], [36, 34, 2, 12, 32, 13], [5, 8, 51], [9, 6, 29, 30, 26, 23], [47, 51, 3, 37, 15, 30]]]
 h' := ![![[41, 21, 29, 27], [31, 22, 20, 56], [40, 17, 12, 8], [46, 35, 6, 47], [0, 0, 0, 1], [0, 1]], ![[29, 43, 33, 18], [45, 50, 33, 58], [58, 10, 18, 2], [25, 5, 29, 5], [20, 44, 56, 50], [41, 21, 29, 27]], ![[7, 53, 56, 14], [48, 13, 21, 20], [46, 46, 50, 58], [38, 37, 48, 20], [10, 39, 44, 23], [29, 43, 33, 18]], ![[0, 1], [29, 33, 44, 43], [19, 45, 38, 50], [15, 41, 35, 46], [35, 35, 18, 44], [7, 53, 56, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [44, 54, 50], []]
 b := ![[], [], [1, 3, 51, 30], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 4
  hpos := by decide
  P := [53, 46, 7, 41, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2075768173447, 1724470810491, 4072790343328, 20564994196192, 47680457492251]
  a := ![-8, 5, 12, 68, 169]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-24279482931203, -8052205154441, -8820546475787, -42483038184629, 47680457492251]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 12117361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, -4, 1, 1, 4]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![-3, -4, 1, 1, 4]] 
 ![![59, 0, 0, 0, 0], ![33, 1, 0, 0, 0], ![32, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![8, 0, 0, 0, 1]] where
  M :=![![![-3, -4, 1, 1, 4], ![2, -2, -5, -6, -26], ![-14, -4, 6, 49, 190], ![92, 35, -47, -301, -1172], ![-50, -19, 26, 163, 635]]]
  hmulB := by decide  
  f := ![![![-49, 23, -75, -2, 20]], ![![-27, 12, -42, -5, 4]], ![![-26, 9, -46, -24, -30]], ![![0, -20, -39, -150, -266]], ![![-8, 9, -2, 39, 73]]]
  g := ![![![1, -4, 1, 1, 4], ![8, -2, -5, -6, -26], ![-32, -4, 6, 49, 190], ![197, 35, -47, -301, -1172], ![-107, -19, 26, 163, 635]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![49, -23, 75, 2, -20]] ![![-3, -4, 1, 1, 4]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 1, 2, -3, -6]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![1, 1, 2, -3, -6]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![17, 60, 1, 0, 0], ![17, 16, 0, 1, 0], ![58, 22, 0, 0, 1]] where
  M :=![![![1, 1, 2, -3, -6], ![0, -2, -2, -13, -24], ![2, -13, -17, -79, -138], ![20, -77, -112, -532, -972], ![-6, 20, 30, 142, 265]]]
  hmulB := by decide  
  f := ![![![37, -87, 68, -29, -78]], ![![-20, 8, -96, 43, 108]], ![![-9, -16, -75, 34, 84]], ![![5, -22, -6, 3, 6]], ![![28, -80, 30, -12, -35]]]
  g := ![![![6, 1, 2, -3, -6], ![27, 14, -2, -13, -24], ![158, 87, -17, -79, -138], ![1104, 599, -112, -532, -972], ![-300, -162, 30, 142, 265]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [21, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [45, 60], [0, 1]]
 g := ![![[24, 15], [46], [1, 39], [37, 20], [45, 1]], ![[28, 46], [46], [48, 22], [22, 41], [29, 60]]]
 h' := ![![[45, 60], [24, 36], [40, 31], [16, 10], [31, 52], [0, 1]], ![[0, 1], [58, 25], [32, 30], [39, 51], [53, 9], [45, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [7, 39]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [21, 16, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-12461, 13139, 27774, 138891, 310122]
  a := ![-4, 4, 7, 37, 88]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-341522, -175381, 27774, 138891, 310122]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, -17, -55, 22, 50]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![1, -17, -55, 22, 50]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![11, 3, 1, 0, 0], ![28, 2, 0, 1, 0], ![12, 46, 0, 0, 1]] where
  M :=![![![1, -17, -55, 22, 50], ![6, 23, -1, 19, 74], ![36, 25, 6, -122, -460], ![-216, -86, 119, 692, 2696], ![116, 43, -68, -373, -1457]]]
  hmulB := by decide  
  f := ![![![11925, -4966, 21663, -9747, -24718]], ![![-5224, 2178, -9489, 4272, 10832]], ![![1931, -804, 3508, -1578, -4002]], ![![5286, -2201, 9603, -4319, -10954]], ![![-1578, 659, -2866, 1291, 3273]]]
  g := ![![![-10, -36, -55, 22, 50], ![-23, -56, -1, 19, 74], ![146, 351, 6, -122, -460], ![-873, -2063, 119, 692, 2696], ![472, 1115, -68, -373, -1457]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P1 : CertificateIrreducibleZModOfList' 61 2 2 5 [36, 33, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [28, 60], [0, 1]]
 g := ![![[6, 39], [46], [8, 36], [44, 12], [28, 1]], ![[0, 22], [46], [40, 25], [14, 49], [56, 60]]]
 h' := ![![[28, 60], [36, 51], [17, 30], [2, 55], [29, 16], [0, 1]], ![[0, 1], [0, 10], [3, 31], [17, 6], [50, 45], [28, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [5, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N1 : CertifiedPrimeIdeal' SI61N1 61 where
  n := 2
  hpos := by decide
  P := [36, 33, 1]
  hirr := P61P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-78078, 67662, 155616, 788994, 1817998]
  a := ![-11, 10, -4, 98, 238]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-749142, -1403362, 155616, 788994, 1817998]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N1 B_one_repr
lemma NI61N1 : Nat.card (O ⧸ I61N1) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3183, 1324, -5787, 2587, 6572]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![-3183, 1324, -5787, 2587, 6572]] 
 ![![61, 0, 0, 0, 0], ![59, 1, 0, 0, 0], ![57, 0, 1, 0, 0], ![53, 0, 0, 1, 0], ![38, 0, 0, 0, 1]] where
  M :=![![![-3183, 1324, -5787, 2587, 6572], ![1398, -596, 2513, -1240, -3070], ![-590, 158, -1246, -147, 110], ![404, -737, -393, -4405, -8044], ![-288, 269, -228, 1303, 2485]]]
  hmulB := by decide  
  f := ![![![-2067, 1455, 19191, -8626, -21508]], ![![-2069, 1232, 18514, -8317, -20748]], ![![-1929, 1316, 17781, -7992, -19930]], ![![-1765, 1335, 16668, -7490, -18666]], ![![-1300, 887, 11986, -5389, -13441]]]
  g := ![![![-2267, 1324, -5787, 2587, 6572], ![1241, -596, 2513, -1240, -3070], ![1061, 158, -1246, -147, 110], ![9925, -737, -393, -4405, -8044], ![-2732, 269, -228, 1303, 2485]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![1, 1, 2, -3, -6]] ![![1, -17, -55, 22, 50]]
  ![![31, 56, 7, -41, -142]] where
 M := ![![![31, 56, 7, -41, -142]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![31, 56, 7, -41, -142]] ![![-3183, 1324, -5787, 2587, 6572]]
  ![![61, 0, 0, 0, 0]] where
 M := ![![![-183, 793, 1098, 5307, 9516]]]
 hmul := by decide  
 g := ![![![![-3, 13, 18, 87, 156]]]]
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


lemma PB953I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB953I1 : PrimesBelowBoundCertificateInterval O 23 61 953 where
  m := 9
  g := ![2, 1, 1, 2, 1, 2, 2, 2, 3]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB953I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0, I29N1]
    · exact ![I31N0]
    · exact ![I37N0]
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
    · exact ![28629151]
    · exact ![69343957]
    · exact ![1681, 68921]
    · exact ![147008443]
    · exact ![4879681, 47]
    · exact ![148877, 2809]
    · exact ![12117361, 59]
    · exact ![3721, 3721, 61]
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
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
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
  β := ![I29N1, I47N1, I59N1, I61N2]
  Il := ![[I29N1], [], [], [], [], [I47N1], [], [I59N1], [I61N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
