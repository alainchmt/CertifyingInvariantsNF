
import IdealArithmetic.Examples.NF5_1_3515625_1.RI5_1_3515625_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, 6, -3, 1, -4]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![-3, 6, -3, 1, -4]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![3, 20, 1, 0, 0], ![27, 9, 0, 1, 0], ![27, 22, 0, 0, 1]] where
  M :=![![![-3, 6, -3, 1, -4], ![0, 0, 2, -3, 6], ![-12, -3, 12, 8, -42], ![-20, 22, -35, 22, 8], ![4, -1, -6, -1, 19]]]
  hmulB := by decide  
  f := ![![![-315, 19, -138, 49, -398]], ![![-404, 34, -177, 64, -514]], ![![-329, 27, -144, 52, -418]], ![![-441, 30, -193, 69, -558]], ![![-605, 44, -265, 95, -767]]]
  g := ![![![3, 5, -3, 1, -4], ![-3, -5, 2, -3, 6], ![30, 21, 12, 8, -42], ![-25, 12, -35, 22, 8], ![-16, -10, -6, -1, 19]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [23, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [16, 28], [0, 1]]
 g := ![![[22, 24], [20], [5, 1], [16, 1]], ![[0, 5], [20], [21, 28], [3, 28]]]
 h' := ![![[16, 28], [5, 16], [1, 22], [9, 1], [0, 1]], ![[0, 1], [0, 13], [5, 7], [25, 28], [16, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [10, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [23, 13, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4978, -1714, -852, -3505, 12034]
  a := ![-20, 2, 9, 9, -55]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-7681, -7513, -852, -3505, 12034]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![288, -23, 125, -45, 361]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![288, -23, 125, -45, 361]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![16, 2, 1, 0, 0], ![26, 12, 0, 1, 0], ![23, 25, 0, 0, 1]] where
  M :=![![![288, -23, 125, -45, 361], ![362, -28, 157, -56, 454], ![460, -36, 196, -73, 584], ![584, -51, 256, -96, 730], ![133, -11, 59, -21, 165]]]
  hmulB := by decide  
  f := ![![![-37, 98, -40, 28, -171]], ![![-118, 106, -14, 19, -68]], ![![-28, 59, -22, 16, -94]], ![![-78, 128, -41, 32, -178]], ![![-130, 167, -43, 38, -191]]]
  g := ![![![-305, -302, 125, -45, 361], ![-384, -380, 157, -56, 454], ![-490, -488, 196, -73, 584], ![-614, -609, 256, -96, 730], ![-140, -138, 59, -21, 165]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P1 : CertificateIrreducibleZModOfList' 29 2 2 4 [7, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 28], [0, 1]]
 g := ![![[20, 25], [9], [12, 5], [5, 1]], ![[0, 4], [9], [8, 24], [10, 28]]]
 h' := ![![[5, 28], [4, 5], [3, 3], [23, 18], [0, 1]], ![[0, 1], [0, 24], [18, 26], [26, 11], [5, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [8, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N1 : CertifiedPrimeIdeal' SI29N1 29 where
  n := 2
  hpos := by decide
  P := [7, 24, 1]
  hirr := P29P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![832612, -345510, 537, -603732, 1778592]
  a := ![-239, -1, 122, 120, -658]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-840916, -1295400, 537, -603732, 1778592]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N1 B_one_repr
lemma NI29N1 : Nat.card (O ⧸ I29N1) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N1

def I29N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19, 12, 1, 1, 3]] i)))

def SI29N2: IdealEqSpanCertificate' Table ![![-19, 12, 1, 1, 3]] 
 ![![29, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![9, 0, 1, 0, 0], ![24, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![-19, 12, 1, 1, 3], ![14, -23, 8, -6, 34], ![20, -14, 1, -2, 4], ![-8, 18, -6, 5, -28], ![9, -4, -1, 0, -4]]]
  hmulB := by decide  
  f := ![![![20, -2, 1, -6, 41]], ![![6, -1, 1, -2, 11]], ![![4, 0, 2, 0, 5]], ![![16, 2, -6, -3, 44]], ![![3, 0, -1, -1, 8]]]
  g := ![![![-5, 12, 1, 1, 3], ![5, -23, 8, -6, 34], ![5, -14, 1, -2, 4], ![-4, 18, -6, 5, -28], ![2, -4, -1, 0, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N2 : Nat.card (O ⧸ I29N2) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N2)

lemma isPrimeI29N2 : Ideal.IsPrime I29N2 := prime_ideal_of_norm_prime hp29.out _ NI29N2
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![-3, 6, -3, 1, -4]] ![![288, -23, 125, -45, 361]]
  ![![-20, 2, -1, 6, -41]] where
 M := ![![![-20, 2, -1, 6, -41]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI29N1 : IdealMulLeCertificate' Table 
  ![![-20, 2, -1, 6, -41]] ![![-19, 12, 1, 1, 3]]
  ![![29, 0, 0, 0, 0]] where
 M := ![![![-29, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0, 0, 0]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]] where
  M :=![![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 5 2 4 [2, 25, 5, 17, 3, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [29, 3, 2, 18, 3], [14, 7, 9, 28, 28], [13, 9, 24, 1, 2], [3, 11, 27, 15, 29], [0, 1]]
 g := ![![[1, 21, 10, 1, 9], [8, 25, 26, 26, 2], [23, 28, 1], []], ![[15, 30, 16, 21, 30, 27, 21, 27], [0, 17, 28, 7, 27, 14, 2, 22], [15, 12, 1, 20, 14, 26, 30, 29], [1, 17, 0, 11, 24, 25, 2, 27]], ![[3, 10, 13, 21, 4, 23, 27, 10], [11, 0, 26, 12, 27, 13, 28, 25], [11, 22, 11, 7, 28, 19, 2, 10], [28, 26, 27, 14, 5, 1, 0, 4]], ![[9, 28, 25, 24, 1, 8, 24, 28], [22, 21, 27, 8, 6, 10], [28, 5, 12, 28, 3, 2, 10, 28], [18, 19, 9, 14, 10, 8, 19, 8]], ![[22, 0, 8, 18, 7, 26, 28, 11], [24, 14, 30, 1, 11, 14, 27, 30], [22, 22, 0, 21, 10, 9, 26, 6], [6, 15, 19, 29, 4, 17, 18, 23]]]
 h' := ![![[29, 3, 2, 18, 3], [15, 6, 16, 15, 3], [16, 20, 20, 2, 8], [0, 0, 0, 1], [0, 1]], ![[14, 7, 9, 28, 28], [3, 30, 0, 7, 3], [18, 4, 4, 15, 11], [21, 8, 5, 16, 12], [29, 3, 2, 18, 3]], ![[13, 9, 24, 1, 2], [16, 30, 8, 23, 21], [27, 29, 12, 10, 8], [22, 16, 27, 20, 21], [14, 7, 9, 28, 28]], ![[3, 11, 27, 15, 29], [2, 24, 0, 28, 18], [5, 29, 0, 6], [22, 14, 19, 8, 18], [13, 9, 24, 1, 2]], ![[0, 1], [5, 3, 7, 20, 17], [11, 11, 26, 29, 4], [15, 24, 11, 17, 11], [3, 11, 27, 15, 29]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13, 8, 6], [], [], []]
 b := ![[], [28, 28, 24, 29], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 5
  hpos := by decide
  P := [2, 25, 5, 17, 3, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![55561653555, -4208772102, -44878104242, -34090340276, 193511462502]
  a := ![-17, 1, 9, 8, -47]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1792311405, -135766842, -1447680782, -1099688396, 6242305242]
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


def P37P0 : CertificateIrreducibleZModOfList' 37 5 2 5 [34, 33, 7, 9, 30, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [36, 33, 23, 9, 2], [31, 16, 17, 0, 1], [13, 16, 12, 35, 35], [1, 8, 22, 30, 36], [0, 1]]
 g := ![![[12, 7, 2, 21, 11], [5, 34, 24, 33], [29, 25, 3, 7, 1], [], []], ![[5, 35, 7, 2, 36, 0, 2, 5], [4, 15, 0, 26], [35, 0, 27, 8, 6, 20, 17, 22], [5, 14, 17, 1], [4, 30, 27, 4]], ![[29, 16, 3, 23, 12, 11, 25, 28], [3, 1, 0, 7], [16, 13, 12, 33, 12, 34, 24, 36], [27, 13, 15, 9], [36, 0, 7, 1]], ![[12, 8, 34, 34, 2, 14, 19, 5], [22, 17, 13, 12], [35, 27, 26, 3, 17, 31, 35, 8], [12, 8, 23, 30], [0, 24, 36, 4]], ![[9, 26, 6, 1, 13, 12, 20, 4], [5, 29, 27, 16], [30, 20, 5, 25, 0, 17, 18, 9], [15, 16, 8, 21], [0, 32, 21, 1]]]
 h' := ![![[36, 33, 23, 9, 2], [36, 19, 22, 35, 14], [13, 6, 17, 4, 25], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[31, 16, 17, 0, 1], [24, 9, 34, 0, 13], [30, 9, 3, 2, 10], [36, 29, 25, 28, 23], [13, 3, 32, 5, 1], [36, 33, 23, 9, 2]], ![[13, 16, 12, 35, 35], [0, 36, 29, 23, 18], [19, 21, 12, 13, 28], [23, 13, 18, 18, 6], [33, 26, 6, 29, 3], [31, 16, 17, 0, 1]], ![[1, 8, 22, 30, 36], [22, 13, 36, 36, 4], [17, 5, 30, 24, 7], [33, 33, 4, 31, 25], [21, 7, 32, 24, 20], [13, 16, 12, 35, 35]], ![[0, 1], [26, 34, 27, 17, 25], [23, 33, 12, 31, 4], [9, 36, 27, 34, 19], [1, 1, 3, 16, 13], [1, 8, 22, 30, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21, 14, 10, 30], [], [], []]
 b := ![[], [10, 9, 24, 1, 22], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 5
  hpos := by decide
  P := [34, 33, 7, 9, 30, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-561547276751492, 153173591904436, 192701749495453, 381612416765527, -1521098695485309]
  a := ![103, -3, -50, -52, 283]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-15176953425716, 4139826808228, 5208155391769, 10313849101771, -41110775553657]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, -3, -11, -12, 57]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![19, -3, -11, -12, 57]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![10, 33, 1, 0, 0], ![39, 28, 0, 1, 0], ![4, 23, 0, 0, 1]] where
  M :=![![![19, -3, -11, -12, 57], ![18, -26, 45, -20, -36], ![-232, 74, 54, 161, -584], ![120, 191, -570, -6, 1206], ![81, -1, -78, -48, 304]]]
  hmulB := by decide  
  f := ![![![1446, -122, 610, -221, 1763]], ![![1758, -96, 762, -269, 2190]], ![![1822, -111, 786, -279, 2262]], ![![2646, -188, 1131, -405, 3261]], ![![1143, -67, 494, -175, 1421]]]
  g := ![![![9, -15, -11, -12, 57], ![12, -3, 45, -20, -36], ![-115, 176, 54, 161, -584], ![30, -209, -570, -6, 1206], ![37, -75, -78, -48, 304]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [35, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 40], [0, 1]]
 g := ![![[25, 37], [21], [16], [40, 32], [1]], ![[40, 4], [21], [16], [2, 9], [1]]]
 h' := ![![[27, 40], [2, 23], [9, 29], [35, 37], [6, 27], [0, 1]], ![[0, 1], [8, 18], [13, 12], [9, 4], [38, 14], [27, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38]]
 b := ![[], [10, 19]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [35, 14, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![25670, -11828, 2563, -19065, 50604]
  a := ![-43, 5, 22, 23, -118]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![13199, -17719, 2563, -19065, 50604]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-32, -2, -13, 4, -35]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-32, -2, -13, 4, -35]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![38, 24, 1, 0, 0], ![31, 36, 0, 1, 0], ![29, 14, 0, 0, 1]] where
  M :=![![![-32, -2, -13, 4, -35], ![-38, -1, -18, 6, -52], ![-56, 8, -25, 10, -76], ![-72, 10, -32, 11, -84], ![-17, 4, -8, 3, -23]]]
  hmulB := by decide  
  f := ![![![-11, 8, -1, 3, -9]], ![![6, -5, -4, -4, 30]], ![![-6, 4, -3, 0, 10]], ![![-5, 2, -3, 0, 13]], ![![-6, 4, -2, 1, 3]]]
  g := ![![![33, 16, -13, 4, -35], ![48, 23, -18, 6, -52], ![68, 32, -25, 10, -76], ![79, 38, -32, 11, -84], ![21, 10, -8, 3, -23]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P1 : CertificateIrreducibleZModOfList' 41 2 2 5 [9, 40, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 40], [0, 1]]
 g := ![![[9, 32], [39], [32], [24, 1], [1]], ![[0, 9], [39], [32], [25, 40], [1]]]
 h' := ![![[1, 40], [27, 14], [38, 11], [30, 14], [32, 1], [0, 1]], ![[0, 1], [0, 27], [8, 30], [3, 27], [33, 40], [1, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [7, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N1 : CertifiedPrimeIdeal' SI41N1 41 where
  n := 2
  hpos := by decide
  P := [9, 40, 1]
  hirr := P41P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4839, -2148, 10164, 1812, -27192]
  a := ![16, -2, -6, -18, 44]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![8325, 1692, 10164, 1812, -27192]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N1 B_one_repr
lemma NI41N1 : Nat.card (O ⧸ I41N1) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, -10, 11, -5, 34]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![31, -10, 11, -5, 34]] 
 ![![41, 0, 0, 0, 0], ![25, 1, 0, 0, 0], ![31, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![35, 0, 0, 0, 1]] where
  M :=![![![31, -10, 11, -5, 34], ![28, 2, 10, -3, 26], ![28, 5, 14, -4, 38], ![44, -6, 21, -8, 64], ![6, 3, 4, -1, 11]]]
  hmulB := by decide  
  f := ![![![-17, 15, -10, 13, -24]], ![![-9, 9, -7, 7, -10]], ![![-11, 9, -4, 8, -20]], ![![-20, 7, 4, 14, -50]], ![![-17, 14, -9, 13, -25]]]
  g := ![![![-30, -10, 11, -5, 34], ![-30, 2, 10, -3, 26], ![-45, 5, 14, -4, 38], ![-65, -6, 21, -8, 64], ![-14, 3, 4, -1, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![19, -3, -11, -12, 57]] ![![-32, -2, -13, 4, -35]]
  ![![17, -15, 10, -13, 24]] where
 M := ![![![17, -15, 10, -13, 24]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![17, -15, 10, -13, 24]] ![![31, -10, 11, -5, 34]]
  ![![41, 0, 0, 0, 0]] where
 M := ![![![-41, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1, I41N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
    exact isPrimeI41N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0 ⊙ MulI41N1)
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


def P43P0 : CertificateIrreducibleZModOfList' 43 5 2 5 [39, 39, 14, 7, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 23, 6, 12], [22, 3, 27, 18, 12], [41, 23, 6, 28, 30], [0, 36, 4, 28, 1], [0, 1]]
 g := ![![[38, 37, 8, 4, 35], [25, 5, 7, 25, 15], [24, 6], [1], []], ![[21, 1, 20, 14, 32, 21, 18], [3, 13, 3, 17, 42, 7, 8], [40, 36, 37, 31], [38, 3, 30, 23, 4, 9, 39], [15, 15]], ![[14, 39, 5, 27, 9, 1, 19, 3], [21, 24, 33, 1, 10, 33, 14, 22], [0, 26, 26, 38], [25, 9, 4, 7, 3, 39, 8, 34], [3, 7, 2, 15]], ![[37, 4, 13, 16, 38, 28, 37, 18], [0, 22, 25, 4, 20, 6, 28, 22], [35, 41, 4, 35], [22, 24, 24, 30, 35, 31, 1, 7], [17, 4, 3, 40]], ![[0, 29, 32, 26, 4, 7, 4, 9], [39, 40, 6, 42, 10, 16, 30, 6], [18, 15, 23, 9], [10, 29, 6, 22, 16, 15, 32, 24], [19, 11, 13, 1]]]
 h' := ![![[23, 23, 6, 12], [14, 22, 34, 8, 11], [26, 23, 22, 10, 12], [4, 4, 29, 36], [0, 0, 1], [0, 1]], ![[22, 3, 27, 18, 12], [4, 16, 39, 37, 25], [40, 14, 18, 13, 12], [40, 34, 16, 15, 17], [30, 17, 10, 40, 10], [23, 23, 6, 12]], ![[41, 23, 6, 28, 30], [20, 23, 40, 40, 21], [1, 12, 21, 29, 3], [42, 3, 12, 32, 34], [23, 0, 30, 0, 15], [22, 3, 27, 18, 12]], ![[0, 36, 4, 28, 1], [17, 13, 4, 17, 32], [20, 38, 29, 7, 9], [40, 30, 29, 35, 32], [29, 35, 37, 32, 4], [41, 23, 6, 28, 30]], ![[0, 1], [27, 12, 12, 27, 40], [38, 42, 39, 27, 7], [40, 15, 0, 11, 3], [33, 34, 8, 14, 14], [0, 36, 4, 28, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30, 30, 19], [], [], []]
 b := ![[], [9, 28, 6, 18, 2], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 5
  hpos := by decide
  P := [39, 39, 14, 7, 0, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![22963522931, -624678931, -21154405173, -13707689769, 84317902006]
  a := ![3, 4, 6, 6, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![534035417, -14527417, -491962911, -318783483, 1960881442]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8, -2, -4, 1, -11]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-8, -2, -4, 1, -11]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![17, 24, 1, 0, 0], ![15, 5, 0, 1, 0], ![13, 9, 0, 0, 1]] where
  M :=![![![-8, -2, -4, 1, -11], ![-14, 2, -6, 3, -22], ![-20, 5, -10, 4, -22], ![-12, -2, -11, -4, 0], ![-5, 1, -2, 0, -5]]]
  hmulB := by decide  
  f := ![![![-17, 23, -7, 6, -33]], ![![-18, 10, -1, 2, 0]], ![![-15, 13, -3, 3, -11]], ![![-7, 8, -2, 2, -11]], ![![-8, 8, -2, 2, -9]]]
  g := ![![![4, 4, -4, 1, -11], ![7, 7, -6, 3, -22], ![8, 9, -10, 4, -22], ![5, 6, -11, -4, 0], ![2, 2, -2, 0, -5]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [41, 30, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 46], [0, 1]]
 g := ![![[42, 27], [32, 16], [5, 12], [41, 7], [1]], ![[31, 20], [22, 31], [21, 35], [19, 40], [1]]]
 h' := ![![[17, 46], [4, 36], [30, 43], [11, 23], [6, 17], [0, 1]], ![[0, 1], [5, 11], [9, 4], [26, 24], [13, 30], [17, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [43, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [41, 30, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![475, -81, -364, -325, 1607]
  a := ![-7, -1, 4, 2, -19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-199, -89, -364, -325, 1607]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2, 0, 1, 0, 3]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-2, 0, 1, 0, 3]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![29, 46, 1, 0, 0], ![29, 28, 0, 1, 0], ![21, 16, 0, 0, 1]] where
  M :=![![![-2, 0, 1, 0, 3], ![6, -5, 0, -2, 12], ![8, -4, 3, -4, 4], ![-24, 8, 12, 15, -72], ![-3, 2, 0, 3, -11]]]
  hmulB := by decide  
  f := ![![![21, -2, 13, -5, 41]], ![![42, -15, 18, -8, 54]], ![![55, -16, 26, -11, 79]], ![![39, -10, 19, -8, 59]], ![![24, -6, 12, -5, 37]]]
  g := ![![![-2, -2, 1, 0, 3], ![-4, -3, 0, -2, 12], ![-1, -2, 3, -4, 4], ![15, 4, 12, 15, -72], ![3, 2, 0, 3, -11]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P1 : CertificateIrreducibleZModOfList' 47 2 2 5 [44, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 46], [0, 1]]
 g := ![![[27, 17], [13, 6], [40, 27], [28, 28], [1]], ![[41, 30], [29, 41], [18, 20], [40, 19], [1]]]
 h' := ![![[34, 46], [39, 8], [26, 37], [37, 11], [3, 34], [0, 1]], ![[0, 1], [29, 39], [15, 10], [35, 36], [31, 13], [34, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [22, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N1 : CertifiedPrimeIdeal' SI47N1 47 where
  n := 2
  hpos := by decide
  P := [44, 13, 1]
  hirr := P47P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-766, -10, 1026, 526, -3348]
  a := ![9, 0, 4, -7, 24]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![522, -178, 1026, 526, -3348]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N1 B_one_repr
lemma NI47N1 : Nat.card (O ⧸ I47N1) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N1

def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2, 5, -1, 1, -5]] i)))

def SI47N2: IdealEqSpanCertificate' Table ![![-2, 5, -1, 1, -5]] 
 ![![47, 0, 0, 0, 0], ![24, 1, 0, 0, 0], ![35, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![28, 0, 0, 0, 1]] where
  M :=![![![-2, 5, -1, 1, -5], ![-2, 2, 1, 0, 2], ![4, -4, 2, -1, 8], ![8, -3, 0, -2, 10], ![3, -3, 1, -1, 5]]]
  hmulB := by decide  
  f := ![![![19, -12, 8, -2, 15]], ![![10, -6, 4, -1, 8]], ![![15, -9, 6, -2, 13]], ![![2, -2, 3, 0, -2]], ![![11, -7, 5, -1, 8]]]
  g := ![![![1, 5, -1, 1, -5], ![-3, 2, 1, 0, 2], ![-4, -4, 2, -1, 8], ![-4, -3, 0, -2, 10], ![-2, -3, 1, -1, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N2 : Nat.card (O ⧸ I47N2) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N2)

lemma isPrimeI47N2 : Ideal.IsPrime I47N2 := prime_ideal_of_norm_prime hp47.out _ NI47N2
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-8, -2, -4, 1, -11]] ![![-2, 0, 1, 0, 3]]
  ![![-19, 12, -8, 2, -15]] where
 M := ![![![-19, 12, -8, 2, -15]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![-19, 12, -8, 2, -15]] ![![-2, 5, -1, 1, -5]]
  ![![47, 0, 0, 0, 0]] where
 M := ![![![-47, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1, I47N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
    exact isPrimeI47N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0 ⊙ MulI47N1)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![377, -30, 163, -59, 473]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![377, -30, 163, -59, 473]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![41, 41, 1, 0, 0], ![15, 3, 0, 1, 0], ![17, 44, 0, 0, 1]] where
  M :=![![![377, -30, 163, -59, 473], ![474, -37, 206, -74, 594], ![596, -46, 259, -92, 748], ![760, -60, 322, -121, 968], ![175, -14, 75, -28, 222]]]
  hmulB := by decide  
  f := ![![![14, 32, -23, 14, -99]], ![![-86, 99, -24, 20, -88]], ![![-56, 101, -36, 26, -143]], ![![0, 13, -7, 5, -33]], ![![-67, 92, -27, 21, -104]]]
  g := ![![![-254, -516, 163, -59, 473], ![-320, -649, 206, -74, 594], ![-403, -817, 259, -92, 748], ![-511, -1047, 322, -121, 968], ![-118, -241, 75, -28, 222]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [24, 33, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [20, 52], [0, 1]]
 g := ![![[8, 42], [25], [32, 49], [25], [20, 1]], ![[0, 11], [25], [5, 4], [25], [40, 52]]]
 h' := ![![[20, 52], [23, 28], [27, 5], [45, 46], [50, 5], [0, 1]], ![[0, 1], [0, 25], [21, 48], [11, 7], [44, 48], [20, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [44, 38]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [24, 33, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![14883, -5990, -224, -10617, 31834]
  a := ![31, -3, -16, -16, 85]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6752, -25767, -224, -10617, 31834]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4, 0, 0, 5, -13]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-4, 0, 0, 5, -13]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![8, 45, 1, 0, 0], ![11, 50, 0, 1, 0], ![29, 7, 0, 0, 1]] where
  M :=![![![-4, 0, 0, 5, -13], ![14, 4, -20, -7, 58], ![60, -37, 32, -50, 78], ![-244, 32, 163, 154, -788], ![-47, 17, 8, 32, -111]]]
  hmulB := by decide  
  f := ![![![1783, -125, 771, -276, 2227]], ![![2246, -168, 979, -352, 2836]], ![![2230, -166, 971, -349, 2812]], ![![2557, -190, 1113, -400, 3223]], ![![1288, -92, 558, -200, 1613]]]
  g := ![![![6, -3, 0, 5, -13], ![-27, 16, -20, -7, 58], ![-36, 9, 32, -50, 78], ![370, -179, 163, 154, -788], ![52, -22, 8, 32, -111]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P1 : CertificateIrreducibleZModOfList' 53 2 2 5 [5, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [52, 52], [0, 1]]
 g := ![![[32, 29], [28], [3, 9], [16], [52, 1]], ![[3, 24], [28], [47, 44], [16], [51, 52]]]
 h' := ![![[52, 52], [32, 20], [38, 9], [51, 50], [5, 49], [0, 1]], ![[0, 1], [12, 33], [29, 44], [1, 3], [9, 4], [52, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [14, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N1 : CertifiedPrimeIdeal' SI53N1 53 where
  n := 2
  hpos := by decide
  P := [5, 1, 1]
  hirr := P53P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1281, 65, -1297, -684, 4874]
  a := ![12, 0, -5, -3, 32]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2305, 1104, -1297, -684, 4874]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N1 B_one_repr
lemma NI53N1 : Nat.card (O ⧸ I53N1) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N1

def I53N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19, 31, -8, 7, -36]] i)))

def SI53N2: IdealEqSpanCertificate' Table ![![-19, 31, -8, 7, -36]] 
 ![![53, 0, 0, 0, 0], ![20, 1, 0, 0, 0], ![24, 0, 1, 0, 0], ![50, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![-19, 31, -8, 7, -36], ![-16, 10, 3, 0, 10], ![20, -26, 10, -7, 40], ![24, -13, 2, -2, 6], ![14, -17, 5, -4, 21]]]
  hmulB := by decide  
  f := ![![![17, 2, -17, -5, 62]], ![![8, 0, -6, -3, 26]], ![![4, 1, -4, 0, 14]], ![![6, 10, -25, 4, 52]], ![![1, 1, -3, 0, 7]]]
  g := ![![![-13, 31, -8, 7, -36], ![-6, 10, 3, 0, 10], ![10, -26, 10, -7, 40], ![6, -13, 2, -2, 6], ![7, -17, 5, -4, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N2 : Nat.card (O ⧸ I53N2) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N2)

lemma isPrimeI53N2 : Ideal.IsPrime I53N2 := prime_ideal_of_norm_prime hp53.out _ NI53N2
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![377, -30, 163, -59, 473]] ![![-4, 0, 0, 5, -13]]
  ![![17, 2, -17, -5, 62]] where
 M := ![![![17, 2, -17, -5, 62]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI53N1 : IdealMulLeCertificate' Table 
  ![![17, 2, -17, -5, 62]] ![![-19, 31, -8, 7, -36]]
  ![![53, 0, 0, 0, 0]] where
 M := ![![![53, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1, I53N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
    exact isPrimeI53N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0 ⊙ MulI53N1)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-80, 39, -13, 9, -41]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-80, 39, -13, 9, -41]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![51, 41, 1, 0, 0], ![33, 22, 0, 1, 0], ![29, 47, 0, 0, 1]] where
  M :=![![![-80, 39, -13, 9, -41], ![-10, -48, 3, -8, 34], ![4, -36, -16, 1, -40], ![-72, 43, -40, 20, -138], ![11, -13, -7, 1, -21]]]
  hmulB := by decide  
  f := ![![![19, -2, -16, -12, 69]], ![![42, -38, 46, -37, 12]], ![![41, -27, 20, -33, 55]], ![![25, -10, -3, -18, 59]], ![![44, -31, 27, -36, 49]]]
  g := ![![![25, 39, -13, 9, -41], ![-15, -27, 3, -8, 34], ![33, 42, -16, 1, -40], ![90, 131, -40, 20, -138], ![16, 21, -7, 1, -21]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [25, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [41, 58], [0, 1]]
 g := ![![[55, 26], [11, 17], [1], [8, 16], [41, 1]], ![[0, 33], [0, 42], [1], [15, 43], [23, 58]]]
 h' := ![![[41, 58], [20, 47], [32, 28], [36, 58], [37, 4], [0, 1]], ![[0, 1], [0, 12], [0, 31], [54, 1], [24, 55], [41, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20]]
 b := ![[], [31, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [25, 18, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![37100, -8572, -16449, -24245, 104760]
  a := ![37, -1, -40, -15, 100]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-23084, -63127, -16449, -24245, 104760]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 22, 10, 0, 14]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![41, 22, 10, 0, 14]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![26, 10, 1, 0, 0], ![35, 44, 0, 1, 0], ![56, 45, 0, 0, 1]] where
  M :=![![![41, 22, 10, 0, 14], ![28, 27, 22, -4, 56], ![80, -24, 43, -18, 136], ![128, -38, 48, -21, 148], ![30, -18, 16, -8, 55]]]
  hmulB := by decide  
  f := ![![![-1, 6, -14, 4, 18]], ![![68, -23, -10, -48, 160]], ![![10, -2, -5, -6, 28]], ![![39, -8, -18, -25, 110]], ![![50, -11, -22, -32, 139]]]
  g := ![![![-17, -12, 10, 0, 14], ![-60, -43, 22, -4, 56], ![-136, -98, 43, -18, 136], ![-147, -106, 48, -21, 148], ![-54, -39, 16, -8, 55]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P1 : CertificateIrreducibleZModOfList' 59 2 2 5 [52, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [30, 58], [0, 1]]
 g := ![![[38, 27], [29, 3], [19], [42, 12], [30, 1]], ![[22, 32], [1, 56], [19], [48, 47], [1, 58]]]
 h' := ![![[30, 58], [26, 26], [16, 11], [58, 14], [33, 22], [0, 1]], ![[0, 1], [39, 33], [51, 48], [6, 45], [44, 37], [30, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [35, 37]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N1 : CertifiedPrimeIdeal' SI59N1 59 where
  n := 2
  hpos := by decide
  P := [52, 29, 1]
  hirr := P59P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2011, -645, -353, -1367, 4394]
  a := ![7, 1, -9, -4, 19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3170, -2283, -353, -1367, 4394]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N1 B_one_repr
lemma NI59N1 : Nat.card (O ⧸ I59N1) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, 7, -3, 2, -11]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![-3, 7, -3, 2, -11]] 
 ![![59, 0, 0, 0, 0], ![8, 1, 0, 0, 0], ![54, 0, 1, 0, 0], ![40, 0, 0, 1, 0], ![14, 0, 0, 0, 1]] where
  M :=![![![-3, 7, -3, 2, -11], ![-6, 6, -1, 0, 0], ![0, -6, 6, -1, 0], ![-8, 1, -2, 10, -22], ![1, -3, 0, 0, 6]]]
  hmulB := by decide  
  f := ![![![-1668, 126, -726, 261, -2101]], ![![-262, 20, -114, 41, -330]], ![![-1572, 119, -684, 246, -1980]], ![![-1188, 90, -517, 186, -1496]], ![![-409, 31, -178, 64, -515]]]
  g := ![![![3, 7, -3, 2, -11], ![0, 6, -1, 0, 0], ![-4, -6, 6, -1, 0], ![0, 1, -2, 10, -22], ![-1, -3, 0, 0, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-80, 39, -13, 9, -41]] ![![41, 22, 10, 0, 14]]
  ![![-3306, 1, -725, 217, -1627]] where
 M := ![![![-3306, 1, -725, 217, -1627]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![-3306, 1, -725, 217, -1627]] ![![-3, 7, -3, 2, -11]]
  ![![59, 0, 0, 0, 0]] where
 M := ![![![6549, -13688, 5133, -3717, 21830]]]
 hmul := by decide  
 g := ![![![![111, -232, 87, -63, 370]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1, I59N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
    exact isPrimeI59N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0 ⊙ MulI59N1)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0, 0, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0, 0, 0]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![0, 0, 0, 0, 61]] where
  M :=![![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![0, 0, 0, 0, 61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 5 2 5 [26, 46, 34, 34, 35, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [50, 30, 58, 52, 46], [42, 27, 42, 34, 30], [24, 47, 32, 54, 2], [32, 17, 51, 43, 44], [0, 1]]
 g := ![![[45, 16, 4, 59, 34], [24, 42, 24, 41], [52, 31, 17, 30, 15], [32, 26, 1], []], ![[31, 37, 4, 40, 50, 15, 56, 49], [3, 54, 16, 41], [46, 25, 22, 55, 43, 19, 8, 49], [0, 24, 33, 14, 2, 45, 27, 45], [34, 47, 56, 50, 47, 13, 54, 41]], ![[28, 55, 58, 23, 45, 29, 52, 43], [53, 2, 44, 46], [2, 44, 31, 4, 49, 26, 34, 40], [44, 0, 0, 26, 6, 25, 13, 31], [21, 44, 41, 54, 20, 24, 7, 38]], ![[37, 44, 50, 49, 26, 23, 17, 28], [0, 26, 9, 15], [51, 35, 58, 31, 7, 45, 6, 10], [31, 50, 47, 35, 57, 10, 59, 31], [36, 11, 19, 32, 12, 31, 2, 8]], ![[52, 54, 58, 29, 19, 15, 53, 6], [53, 51, 49, 25], [30, 3, 26, 29, 40, 43], [49, 13, 42, 26, 43, 0, 50, 10], [37, 1, 43, 7, 23, 57, 6, 28]]]
 h' := ![![[50, 30, 58, 52, 46], [25, 51, 9, 13, 41], [51, 31, 1, 41, 23], [22, 48, 8, 56, 36], [0, 0, 0, 1], [0, 1]], ![[42, 27, 42, 34, 30], [19, 41, 49, 17, 14], [55, 46, 39, 52, 38], [55, 39, 41, 45, 14], [42, 52, 0, 46, 34], [50, 30, 58, 52, 46]], ![[24, 47, 32, 54, 2], [25, 11, 17, 36, 6], [0, 26, 54, 54, 30], [51, 28, 7, 37, 46], [37, 47, 7, 53, 50], [42, 27, 42, 34, 30]], ![[32, 17, 51, 43, 44], [57, 23, 19, 24, 40], [22, 45, 59, 43, 36], [30, 11, 7, 2, 26], [17, 35, 23, 60, 30], [24, 47, 32, 54, 2]], ![[0, 1], [37, 57, 28, 32, 21], [45, 35, 30, 54, 56], [60, 57, 59, 43], [25, 49, 31, 23, 8], [32, 17, 51, 43, 44]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13, 50, 3, 37], [], [], []]
 b := ![[], [14, 32, 43, 33, 35], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 5
  hpos := by decide
  P := [26, 46, 34, 34, 35, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2462780084, 35410509333, -85911401613, 10420648788, 148410413478]
  a := ![17, -1, -6, -2, 46]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![40373444, 580500153, -1408383633, 170830308, 2432957598]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 844596301 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def PBC61 : ContainsPrimesAboveP 61 ![I61N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![61, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 61 (by decide) 𝕀



lemma PB117I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB117I1 : PrimesBelowBoundCertificateInterval O 23 61 117 where
  m := 9
  g := ![3, 1, 1, 3, 1, 3, 3, 3, 1]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB117I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0, I29N1, I29N2]
    · exact ![I31N0]
    · exact ![I37N0]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0]
    · exact ![I47N0, I47N1, I47N2]
    · exact ![I53N0, I53N1, I53N2]
    · exact ![I59N0, I59N1, I59N2]
    · exact ![I61N0]
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
    · exact ![28629151]
    · exact ![69343957]
    · exact ![1681, 1681, 41]
    · exact ![147008443]
    · exact ![2209, 2209, 47]
    · exact ![2809, 2809, 53]
    · exact ![3481, 3481, 59]
    · exact ![844596301]
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
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
      exact NI41N2
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
      exact NI47N2
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
      exact NI53N2
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
      exact NI59N2
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
  β := ![I29N2, I41N2, I47N2, I53N2, I59N2]
  Il := ![[I29N2], [], [], [I41N2], [], [I47N2], [I53N2], [I59N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
