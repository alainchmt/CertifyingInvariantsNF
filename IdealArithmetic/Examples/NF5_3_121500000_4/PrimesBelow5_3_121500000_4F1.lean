
import IdealArithmetic.Examples.NF5_3_121500000_4.RI5_3_121500000_4
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0, 0, 0]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0, 0, 0]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![0, 0, 0, 29, 0], ![0, 0, 0, 0, 29]] where
  M :=![![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![0, 0, 0, 29, 0], ![0, 0, 0, 0, 29]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 5 2 4 [18, 19, 28, 1, 15, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [15, 25, 7, 24, 11], [15, 16, 2, 27, 10], [27, 0, 21, 28, 18], [15, 16, 28, 8, 19], [0, 1]]
 g := ![![[4, 7, 14, 27, 1], [4, 4, 7, 23], [21, 14, 1], []], ![[11, 18, 9, 27, 17, 25, 25, 27], [10, 3, 15, 5], [23, 24, 8, 20, 10, 23, 24, 19], [18, 21, 0, 3, 16, 20, 28, 26]], ![[14, 17, 8, 24, 28, 18, 2, 21], [0, 5, 24, 5], [26, 9, 23, 20, 3, 22, 11, 18], [16, 21, 20, 19, 21, 9, 2, 14]], ![[24, 10, 11, 20, 2, 12, 7, 2], [25, 21, 19, 4], [16, 8, 5, 14, 17, 8, 14, 19], [11, 19, 23, 2, 3, 19, 27, 3]], ![[23, 1, 22, 11, 25, 17, 14, 15], [15, 14, 21, 5], [12, 21, 17, 15, 12, 20, 23, 26], [22, 8, 1, 23, 8, 27, 0, 15]]]
 h' := ![![[15, 25, 7, 24, 11], [16, 23, 4, 21, 1], [28, 16, 27, 3, 20], [0, 0, 0, 1], [0, 1]], ![[15, 16, 2, 27, 10], [7, 7, 10, 24, 10], [10, 14, 8, 12, 11], [6, 2, 18, 22, 23], [15, 25, 7, 24, 11]], ![[27, 0, 21, 28, 18], [6, 9, 26, 20, 18], [8, 8, 7, 19, 11], [13, 26, 5, 8, 24], [15, 16, 2, 27, 10]], ![[15, 16, 28, 8, 19], [9, 27, 16, 9, 10], [13, 16, 25, 2, 27], [26, 0, 10, 16, 14], [27, 0, 21, 28, 18]], ![[0, 1], [4, 21, 2, 13, 19], [19, 4, 20, 22, 18], [21, 1, 25, 11, 26], [15, 16, 28, 8, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13, 16, 26, 6], [], [], []]
 b := ![[], [27, 12, 22, 23, 10], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 5
  hpos := by decide
  P := [18, 19, 28, 1, 15, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![104107623929834, 147589901746504, 77109846085244, 22882135496798, -91630229354684]
  a := ![17, 4, 8, 14, -68]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3589918066546, 5089306956776, 2658960209836, 789039155062, -3159663081196]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 20511149 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def PBC29 : ContainsPrimesAboveP 29 ![I29N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![29, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 29 (by decide) 𝕀

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


def P31P0 : CertificateIrreducibleZModOfList' 31 5 2 4 [27, 9, 18, 23, 14, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 30, 8, 0, 7], [5, 12, 17, 16, 14], [14, 18, 29, 5, 18], [28, 1, 8, 10, 23], [0, 1]]
 g := ![![[8, 13, 16, 29, 28], [10, 18, 30, 5, 7], [18, 17, 1], []], ![[26, 18, 26, 22, 10, 3, 4, 5], [13, 1, 22, 26, 25, 13, 24, 9], [8, 21, 25, 29, 27, 29, 2, 9], [6, 30, 13, 10, 16, 3, 3, 2]], ![[0, 19, 0, 18, 28, 8, 3, 25], [20, 4, 28, 9, 17, 25, 5, 1], [2, 5, 6, 14, 8, 15, 18, 7], [23, 14, 20, 11, 8, 25, 8, 16]], ![[2, 4, 25, 10, 1, 1, 24, 4], [12, 2, 3, 15, 28, 28], [28, 22, 19, 0, 16, 24, 29, 2], [4, 8, 19, 27, 15, 10, 30, 4]], ![[15, 8, 22, 11, 13, 20, 30, 27], [14, 14, 28, 3, 27, 20, 18, 24], [1, 16, 22, 29, 20, 29, 24, 29], [15, 0, 30, 20, 24, 23, 5, 15]]]
 h' := ![![[1, 30, 8, 0, 7], [9, 20, 6, 29, 11], [10, 30, 23, 15, 21], [0, 0, 0, 1], [0, 1]], ![[5, 12, 17, 16, 14], [26, 8, 8, 28, 13], [6, 26, 29, 13, 9], [25, 1, 11, 2, 9], [1, 30, 8, 0, 7]], ![[14, 18, 29, 5, 18], [28, 20, 14, 12, 29], [8, 2, 6, 23, 12], [0, 5, 30, 9, 27], [5, 12, 17, 16, 14]], ![[28, 1, 8, 10, 23], [11, 18, 17, 24, 13], [2, 13, 8, 6], [1, 9, 26, 24, 10], [14, 18, 29, 5, 18]], ![[0, 1], [19, 27, 17, 0, 27], [23, 22, 27, 5, 20], [2, 16, 26, 26, 16], [28, 1, 8, 10, 23]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 23, 13, 25], [], [], []]
 b := ![[], [5, 0, 4, 19, 23], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 5
  hpos := by decide
  P := [27, 9, 18, 23, 14, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7814637872123705490, 7945494327557384408, 2254386403524979497, -22228501730267288, -2409630942346385097]
  a := ![113, -4, 57, 50, -449]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![252085092649151790, 256306268630883368, 72722142049192887, -717048442911848, -77730030398270487]
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

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![395, 409, 115, -4, -126]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![395, 409, 115, -4, -126]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![23, 27, 17, 20, 1]] where
  M :=![![![395, 409, 115, -4, -126], ![1524, 1522, 417, -10, -426], ![5142, 5359, 1542, 12, -1398], ![7608, 8167, 2459, 131, -1812], ![4764, 5200, 1594, 108, -1075]]]
  hmulB := by decide  
  f := ![![![1361, 521, -339, -130, 294]], ![![-3138, -1200, 781, 300, -678]], ![![7236, 2767, -1800, -694, 1566]], ![![-6786, -2599, 1687, 657, -1476]], ![![-1763, -676, 438, 172, -385]]]
  g := ![![![89, 103, 61, 68, -126], ![306, 352, 207, 230, -426], ![1008, 1165, 684, 756, -1398], ![1332, 1543, 899, 983, -1812], ![797, 925, 537, 584, -1075]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 4 2 5 [19, 23, 30, 33, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 34, 34, 18], [36, 3, 4, 27], [1, 36, 36, 29], [0, 1]]
 g := ![![[29, 6, 23, 16], [31, 16, 36], [13, 13, 9, 16], [1], []], ![[10, 17, 27, 1, 36, 20], [15, 19, 9], [14, 8, 27, 13, 18, 5], [36, 0, 4], [2, 4, 28]], ![[30, 9, 16, 4, 12, 10], [25, 19, 10], [36, 31, 21, 22, 31, 36], [35, 16, 25], [12, 24, 26]], ![[19, 23, 6, 4, 34, 8], [13, 2, 11], [13, 24, 31, 17, 11, 5], [31, 1, 12], [36, 13, 27]]]
 h' := ![![[4, 34, 34, 18], [36, 19, 19, 33], [12, 0, 14, 6], [18, 14, 7, 4], [0, 0, 1], [0, 1]], ![[36, 3, 4, 27], [36, 18, 1, 16], [5, 28, 9, 34], [22, 9, 4, 8], [15, 2, 4, 35], [4, 34, 34, 18]], ![[1, 36, 36, 29], [13, 22, 22, 31], [9, 8, 31, 11], [26, 18, 25, 27], [32, 2, 1, 32], [36, 3, 4, 27]], ![[0, 1], [19, 15, 32, 31], [28, 1, 20, 23], [33, 33, 1, 35], [20, 33, 31, 7], [1, 36, 36, 29]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [4, 12, 5], []]
 b := ![[], [], [1, 26, 29, 19], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 4
  hpos := by decide
  P := [19, 23, 30, 33, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-45546064886, -45966231345, -13636284687, -42616719, 17988088320]
  a := ![10, 1, 5, 6, -39]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-12412759358, -14368773405, -8633345571, -9724442787, 17988088320]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1874161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1361, -521, 339, 130, -294]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-1361, -521, 339, 130, -294]] 
 ![![37, 0, 0, 0, 0], ![16, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![27, 0, 0, 0, 1]] where
  M :=![![![-1361, -521, 339, 130, -294], ![3138, 1200, -781, -300, 678], ![-7236, -2767, 1800, 694, -1566], ![6786, 2599, -1687, -657, 1476], ![-900, -346, 224, 88, -197]]]
  hmulB := by decide  
  f := ![![![-395, -409, -115, 4, 126]], ![![-212, -218, -61, 2, 66]], ![![-171, -178, -51, 0, 48]], ![![-259, -276, -82, -3, 66]], ![![-417, -439, -127, 0, 121]]]
  g := ![![![358, -521, 339, 130, -294], ![-825, 1200, -781, -300, 678], ![1904, -2767, 1800, 694, -1566], ![-1792, 2599, -1687, -657, 1476], ![239, -346, 224, 88, -197]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![395, 409, 115, -4, -126]] ![![-1361, -521, 339, 130, -294]]
  ![![37, 0, 0, 0, 0]] where
 M := ![![![-37, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6, 4, -2, -3, 5]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![6, 4, -2, -3, 5]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![34, 9, 1, 0, 0], ![11, 18, 0, 1, 0], ![5, 7, 0, 0, 1]] where
  M :=![![![6, 4, -2, -3, 5], ![-51, -33, 10, 15, -21], ![207, 112, -63, -67, 117], ![-576, -346, 118, 147, -216], ![67, 24, -34, -27, 58]]]
  hmulB := by decide  
  f := ![![![476, 82, -84, -25, 65]], ![![-705, -103, 132, 37, -105]], ![![268, 51, -45, -14, 34]], ![![-190, -22, 38, 10, -31]], ![![-56, -5, 12, 3, -10]]]
  g := ![![![2, 1, -2, -3, 5], ![-11, -6, 10, 15, -21], ![61, 26, -63, -67, 117], ![-125, -62, 118, 147, -216], ![30, 10, -34, -27, 58]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [36, 35, 1] where
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
 g := ![![[34, 8], [33], [10], [30, 36], [1]], ![[0, 33], [33], [10], [0, 5], [1]]]
 h' := ![![[6, 40], [1, 34], [0, 22], [27, 16], [5, 6], [0, 1]], ![[0, 1], [0, 7], [9, 19], [0, 25], [0, 35], [6, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38]]
 b := ![[], [25, 19]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [36, 35, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2264645, -2366838, -934720, -125471, 1812203]
  a := ![-61, -8, -30, -43, 245]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![532561, -106861, -934720, -125471, 1812203]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![117, 34, -14, -6, 8]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![117, 34, -14, -6, 8]] 
 ![![41, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![23, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![30, 0, 0, 0, 1]] where
  M :=![![![117, 34, -14, -6, 8], ![-78, 45, 46, 6, -48], ![558, 346, 33, -22, -72], ![504, 572, 172, -9, -216], ![460, 414, 98, -12, -131]]]
  hmulB := by decide  
  f := ![![![3605, 1954, -894, -910, 1496]], ![![508, 273, -126, -126, 208]], ![![3617, 1976, -897, -928, 1520]], ![![-3009, -1670, 746, 797, -1296]], ![![3266, 1778, -810, -832, 1365]]]
  g := ![![![-3, 34, -14, -6, 8], ![-4, 45, 46, 6, -48], ![-35, 346, 33, -22, -72], ![-65, 572, 172, -9, -216], ![-48, 414, 98, -12, -131]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![114, 108, -36, -55, 83]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![114, 108, -36, -55, 83]] 
 ![![41, 0, 0, 0, 0], ![29, 1, 0, 0, 0], ![20, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![40, 0, 0, 0, 1]] where
  M :=![![![114, 108, -36, -55, 83], ![-831, -531, 218, 259, -411], ![4155, 2416, -1049, -1163, 1875], ![-9090, -5100, 2262, 2441, -3960], ![1729, 978, -432, -469, 760]]]
  hmulB := by decide  
  f := ![![![1040, 510, -162, -85, 119]], ![![707, 361, -98, -56, 68]], ![![689, 362, -87, -53, 59]], ![![102, 126, 48, 2, -51]], ![![1113, 588, -138, -85, 94]]]
  g := ![![![-133, 108, -36, -55, 83], ![631, -531, 218, 259, -411], ![-2840, 2416, -1049, -1163, 1875], ![5967, -5100, 2262, 2441, -3960], ![-1146, 978, -432, -469, 760]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2

def I41N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![779, 296, -194, -74, 168]] i)))

def SI41N3: IdealEqSpanCertificate' Table ![![779, 296, -194, -74, 168]] 
 ![![41, 0, 0, 0, 0], ![34, 1, 0, 0, 0], ![33, 0, 1, 0, 0], ![37, 0, 0, 1, 0], ![15, 0, 0, 0, 1]] where
  M :=![![![779, 296, -194, -74, 168], ![-1794, -685, 444, 170, -384], ![4098, 1552, -1025, -390, 888], ![-3846, -1478, 944, 363, -816], ![492, 178, -130, -48, 113]]]
  hmulB := by decide  
  f := ![![![931, 148, -166, -42, 120]], ![![740, 119, -132, -34, 96]], ![![789, 120, -139, -32, 96]], ![![857, 154, -154, -47, 120]], ![![345, 54, -60, -14, 41]]]
  g := ![![![-65, 296, -194, -74, 168], ![154, -685, 444, 170, -384], ![-335, 1552, -1025, -390, 888], ![343, -1478, 944, 363, -816], ![-29, 178, -130, -48, 113]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N3 : Nat.card (O ⧸ I41N3) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N3)

lemma isPrimeI41N3 : Ideal.IsPrime I41N3 := prime_ideal_of_norm_prime hp41.out _ NI41N3
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![6, 4, -2, -3, 5]] ![![117, 34, -14, -6, 8]]
  ![![62, 46, 8, -1, -7]] where
 M := ![![![62, 46, 8, -1, -7]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![62, 46, 8, -1, -7]] ![![114, 108, -36, -55, 83]]
  ![![-931, -148, 166, 42, -120]] where
 M := ![![![-931, -148, 166, 42, -120]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI41N2 : IdealMulLeCertificate' Table 
  ![![-931, -148, 166, 42, -120]] ![![779, 296, -194, -74, 168]]
  ![![41, 0, 0, 0, 0]] where
 M := ![![![-41, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1, I41N2, I41N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
    exact isPrimeI41N2
    exact isPrimeI41N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0 ⊙ MulI41N1 ⊙ MulI41N2)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-374, -149, 89, 35, -77]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![-374, -149, 89, 35, -77]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![30, 28, 19, 1, 0], ![9, 37, 22, 0, 1]] where
  M :=![![![-374, -149, 89, 35, -77], ![819, 296, -219, -81, 189], ![-2025, -831, 458, 183, -405], ![1746, 597, -489, -181, 396], ![-277, -146, 38, 17, -54]]]
  hmulB := by decide  
  f := ![![![-18, -25, 7, 13, -19]], ![![189, 128, -51, -63, 99]], ![![-999, -591, 254, 285, -459]], ![![-279, -166, 71, 80, -129]], ![![-362, -203, 90, 97, -158]]]
  g := ![![![-17, 40, 26, 35, -77], ![36, -103, -66, -81, 189], ![-90, 210, 137, 183, -405], ![84, -209, -134, -181, 396], ![-7, 32, 21, 17, -54]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [18, 4, 41, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 26, 26], [27, 16, 17], [0, 1]]
 g := ![![[42, 26, 17], [13, 37, 38], [42, 31], [0, 2, 1], []], ![[37, 31, 14, 27], [19, 15, 11, 34], [30, 17], [30, 36, 9, 34], [38, 31]], ![[41, 4, 9, 40], [10, 27, 14, 4], [9, 4], [15, 41, 39, 11], [4, 31]]]
 h' := ![![[18, 26, 26], [24, 36, 19], [18, 5, 9], [0, 7, 17], [0, 0, 1], [0, 1]], ![[27, 16, 17], [24, 27, 36], [7, 14, 16], [26, 25, 24], [27, 11, 16], [18, 26, 26]], ![[0, 1], [20, 23, 31], [3, 24, 18], [6, 11, 2], [12, 32, 26], [27, 16, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 15], []]
 b := ![[], [37, 18, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [18, 4, 41, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![13838232, 352059152, 425066834, 204803396, -684089202]
  a := ![29, 11, 15, 32, -117]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![617190, 463461966, 269389878, 204803396, -684089202]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 79507 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![18, 25, -7, -13, 19]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![18, 25, -7, -13, 19]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![26, 5, 1, 0, 0], ![21, 1, 0, 1, 0], ![0, 31, 0, 0, 1]] where
  M :=![![![18, 25, -7, -13, 19], ![-189, -128, 51, 63, -99], ![999, 591, -254, -285, 459], ![-2232, -1257, 555, 601, -972], ![419, 238, -106, -115, 188]]]
  hmulB := by decide  
  f := ![![![374, 149, -89, -35, 77]], ![![-819, -296, 219, 81, -189]], ![![178, 75, -39, -16, 34]], ![![123, 52, -27, -11, 24]], ![![-584, -210, 157, 58, -135]]]
  g := ![![![11, -12, -7, -13, 19], ![-66, 61, 51, 63, -99], ![316, -281, -254, -285, 459], ![-681, 593, 555, 601, -972], ![130, -115, -106, -115, 188]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P1 : CertificateIrreducibleZModOfList' 43 2 2 5 [24, 31, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 42], [0, 1]]
 g := ![![[21, 9], [23, 16], [11], [34, 15], [1]], ![[0, 34], [0, 27], [11], [42, 28], [1]]]
 h' := ![![[12, 42], [7, 3], [38, 4], [1, 22], [19, 12], [0, 1]], ![[0, 1], [0, 40], [0, 39], [7, 21], [34, 31], [12, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [11, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N1 : CertifiedPrimeIdeal' SI43N1 43 where
  n := 2
  hpos := by decide
  P := [24, 31, 1]
  hirr := P43P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![414630, 232852, -111916, -127254, 209976]
  a := ![-18, -16, -8, -38, 72]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![139460, -129990, -111916, -127254, 209976]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N1 B_one_repr
lemma NI43N1 : Nat.card (O ⧸ I43N1) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![-374, -149, 89, 35, -77]] ![![18, 25, -7, -13, 19]]
  ![![43, 0, 0, 0, 0]] where
 M := ![![![-43, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2086, 367, -377, -113, 295]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![2086, 367, -377, -113, 295]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![5, 21, 18, 13, 1]] where
  M :=![![![2086, 367, -377, -113, 295], ![-3201, -538, 593, 175, -471], ![5127, 985, -888, -281, 687], ![-2100, -219, 477, 133, -420], ![971, 290, -114, -51, 72]]]
  hmulB := by decide  
  f := ![![![-54, -21, 13, 5, -11]], ![![117, 42, -31, -11, 27]], ![![-291, -119, 64, 25, -51]], ![![210, 57, -69, -19, 60]], ![![-8, -14, -7, 0, 8]]]
  g := ![![![13, -124, -121, -84, 295], ![-18, 199, 193, 134, -471], ![36, -286, -282, -196, 687], ![0, 183, 171, 119, -420], ![13, -26, -30, -21, 72]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 4 2 5 [13, 4, 16, 28, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 9, 26, 27], [40, 16, 7, 20], [46, 21, 14], [0, 1]]
 g := ![![[16, 43, 45, 17], [6, 25, 2, 27], [11, 28, 37, 21], [19, 1], []], ![[8, 4, 36, 20, 5, 21], [16, 16, 1, 11, 6, 17], [20, 15, 35, 0, 20, 7], [27, 37, 29, 33, 1, 1], [22, 27, 24]], ![[35, 3, 17, 9, 29, 46], [19, 42, 29, 36, 34, 19], [34, 4, 10, 0, 20, 41], [36, 39, 37, 41, 31, 41], [1, 31, 24]], ![[4, 43, 31, 16, 1], [26, 45, 43, 44, 3], [42, 27, 24, 37, 34], [7, 37, 35, 41, 42], [8]]]
 h' := ![![[27, 9, 26, 27], [16, 31, 35, 39], [45, 18, 4, 36], [35, 5, 21, 16], [0, 0, 1], [0, 1]], ![[40, 16, 7, 20], [31, 18, 19, 10], [34, 44, 14, 5], [15, 3, 35, 7], [20, 0, 8, 30], [27, 9, 26, 27]], ![[46, 21, 14], [3, 30, 15, 30], [21, 1, 37, 14], [1, 38, 5, 18], [36, 27, 35, 29], [40, 16, 7, 20]], ![[0, 1], [29, 15, 25, 15], [44, 31, 39, 39], [16, 1, 33, 6], [38, 20, 3, 35], [46, 21, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [5, 22, 1], []]
 b := ![[], [], [36, 0, 35, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 4
  hpos := by decide
  P := [13, 4, 16, 28, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-341381066693, -324218844538, -81400717515, 10094058918, 116393409892]
  a := ![-3, 8, -1, 11, 25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-19645704599, -58903839410, -46308129693, -31979154674, 116393409892]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 4879681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-54, -21, 13, 5, -11]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-54, -21, 13, 5, -11]] 
 ![![47, 0, 0, 0, 0], ![29, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![27, 0, 0, 0, 1]] where
  M :=![![![-54, -21, 13, 5, -11], ![117, 42, -31, -11, 27], ![-291, -119, 64, 25, -51], ![210, 57, -69, -19, 60], ![-55, -34, 2, 3, 2]]]
  hmulB := by decide  
  f := ![![![2086, 367, -377, -113, 295]], ![![1219, 215, -220, -66, 172]], ![![331, 60, -59, -18, 46]], ![![266, 50, -46, -14, 35]], ![![1219, 217, -219, -66, 171]]]
  g := ![![![16, -21, 13, 5, -11], ![-34, 42, -31, -11, 27], ![86, -119, 64, 25, -51], ![-55, 57, -69, -19, 60], ![18, -34, 2, 3, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![2086, 367, -377, -113, 295]] ![![-54, -21, 13, 5, -11]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-650, -119, 115, 35, -89]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-650, -119, 115, 35, -89]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![44, 42, 1, 0, 0], ![30, 15, 0, 1, 0], ![17, 49, 0, 0, 1]] where
  M :=![![![-650, -119, 115, 35, -89], ![963, 142, -189, -53, 153], ![-1677, -397, 248, 87, -177], ![450, -121, -191, -33, 180], ![-421, -210, 2, 17, 18]]]
  hmulB := by decide  
  f := ![![![-1170, -449, 291, 115, -257]], ![![2739, 1062, -679, -277, 609]], ![![1077, 421, -266, -111, 241]], ![![237, 97, -58, -28, 57]], ![![2140, 831, -530, -217, 476]]]
  g := ![![![-99, -21, 115, 35, -89], ![156, 26, -189, -53, 153], ![-230, -65, 248, 87, -177], ![128, -8, -191, -33, 180], ![-25, -27, 2, 17, 18]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [13, 31, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 52], [0, 1]]
 g := ![![[35, 49], [7], [30, 44], [36], [22, 1]], ![[0, 4], [7], [44, 9], [36], [44, 52]]]
 h' := ![![[22, 52], [5, 7], [34, 22], [26, 37], [32, 47], [0, 1]], ![[0, 1], [0, 46], [41, 31], [45, 16], [6, 6], [22, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [16, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [13, 31, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5128, 1786, -3278, -3027, 7353]
  a := ![-1, -4, 0, -7, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2173, -3310, -3278, -3027, 7353]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-46, -10, 8, 3, -7]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-46, -10, 8, 3, -7]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![19, 7, 1, 0, 0], ![13, 12, 0, 1, 0], ![49, 7, 0, 0, 1]] where
  M :=![![![-46, -10, 8, 3, -7], ![75, 15, -16, -7, 15], ![-159, -54, 29, 19, -39], ![168, 74, -38, -35, 48], ![-29, -10, 8, 5, -18]]]
  hmulB := by decide  
  f := ![![![744, 284, -186, -71, 161]], ![![-1719, -659, 426, 163, -369]], ![![114, 43, -29, -11, 25]], ![![-276, -106, 68, 26, -59]], ![![470, 179, -118, -45, 102]]]
  g := ![![![2, -1, 8, 3, -7], ![-5, 2, -16, -7, 15], ![18, -4, 29, 19, -39], ![-19, 8, -38, -35, 48], ![12, 0, 8, 5, -18]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P1 : CertificateIrreducibleZModOfList' 53 2 2 5 [22, 15, 1] where
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
 g := ![![[32, 36], [42], [], [28], [38, 1]], ![[22, 17], [42], [], [28], [23, 52]]]
 h' := ![![[38, 52], [30, 6], [0, 25], [5], [12, 44], [0, 1]], ![[0, 1], [46, 47], [49, 28], [5], [41, 9], [38, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [32, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N1 : CertifiedPrimeIdeal' SI53N1 53 where
  n := 2
  hpos := by decide
  P := [22, 15, 1]
  hirr := P53P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11749, -133992, -198612, -105711, 373023]
  a := ![-27, -11, -10, -32, 111]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-247519, -1629, -198612, -105711, 373023]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N1 B_one_repr
lemma NI53N1 : Nat.card (O ⧸ I53N1) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N1

def I53N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13, -9, 3, 4, -6]] i)))

def SI53N2: IdealEqSpanCertificate' Table ![![-13, -9, 3, 4, -6]] 
 ![![53, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![37, 0, 1, 0, 0], ![30, 0, 0, 1, 0], ![17, 0, 0, 0, 1]] where
  M :=![![![-13, -9, 3, 4, -6], ![60, 34, -17, -18, 30], ![-306, -179, 70, 80, -126], ![606, 329, -161, -167, 276], ![-132, -80, 26, 32, -49]]]
  hmulB := by decide  
  f := ![![![2629, 983, -647, -246, 558]], ![![86, 32, -21, -8, 18]], ![![2093, 784, -515, -196, 444]], ![![1254, 469, -307, -117, 264]], ![![877, 329, -215, -82, 185]]]
  g := ![![![-2, -9, 3, 4, -6], ![11, 34, -17, -18, 30], ![-46, -179, 70, 80, -126], ![105, 329, -161, -167, 276], ![-17, -80, 26, 32, -49]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N2 : Nat.card (O ⧸ I53N2) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N2)

lemma isPrimeI53N2 : Ideal.IsPrime I53N2 := prime_ideal_of_norm_prime hp53.out _ NI53N2
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-650, -119, 115, 35, -89]] ![![-46, -10, 8, 3, -7]]
  ![![11151, 1985, -2003, -602, 1562]] where
 M := ![![![11151, 1985, -2003, -602, 1562]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI53N1 : IdealMulLeCertificate' Table 
  ![![11151, 1985, -2003, -602, 1562]] ![![-13, -9, 3, 4, -6]]
  ![![53, 0, 0, 0, 0]] where
 M := ![![![16059, 2650, -2968, -848, 2332]]]
 hmul := by decide  
 g := ![![![![303, 50, -56, -16, 44]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2821, 494, -510, -152, 400]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![2821, 494, -510, -152, 400]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![2, 10, 40, 1, 0], ![41, 13, 39, 0, 1]] where
  M :=![![![2821, 494, -510, -152, 400], ![-4344, -737, 798, 236, -624], ![6780, 1210, -1209, -360, 960], ![-3048, -506, 566, 173, -408], ![1076, 188, -192, -52, 177]]]
  hmulB := by decide  
  f := ![![![-201, -106, 50, 48, -80]], ![![816, 441, -202, -204, 336]], ![![-3420, -1870, 849, 880, -1440]], ![![-2070, -1132, 514, 533, -872]], ![![-2243, -1225, 557, 576, -943]]]
  g := ![![![-225, -54, -170, -152, 400], ![352, 85, 266, 236, -624], ![-540, -130, -411, -360, 960], ![226, 52, 162, 173, -408], ![-103, -27, -85, -52, 177]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [15, 52, 53, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [24, 37, 32], [41, 21, 27], [0, 1]]
 g := ![![[22], [55, 56, 41], [44, 19], [33, 5, 36], [1]], ![[36, 39, 38, 34], [25, 31, 57, 24], [1, 12], [37, 43, 58, 40], [10, 57, 50, 23]], ![[35, 24, 51, 25], [11, 46, 0, 1], [12, 5], [13, 27, 39, 49], [30, 0, 5, 36]]]
 h' := ![![[24, 37, 32], [1, 9], [46, 20, 10], [36, 27, 14], [44, 7, 6], [0, 1]], ![[41, 21, 27], [40, 38, 52], [51, 9, 24], [19, 11, 37], [45, 21, 55], [24, 37, 32]], ![[0, 1], [16, 12, 7], [12, 30, 25], [30, 21, 8], [31, 31, 57], [41, 21, 27]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 24], []]
 b := ![[], [0, 55, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [15, 52, 53, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-124994685, -198506658, -130509034, -45320960, 209315530]
  a := ![-19, -6, -10, -19, 77]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-146038805, -41803372, -109847056, -45320960, 209315530]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 205379 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-160, -146, -34, 7, 59]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![-160, -146, -34, 7, 59]] 
 ![![59, 0, 0, 0, 0], ![40, 1, 0, 0, 0], ![52, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![40, 0, 0, 0, 1]] where
  M :=![![![-160, -146, -34, 7, 59], ![-729, -673, -160, 29, 261], ![-3219, -3006, -731, 115, 1131], ![-6594, -6220, -1538, 213, 2256], ![-4595, -4348, -1082, 143, 1566]]]
  hmulB := by decide  
  f := ![![![19998, 4316, -3908, -1249, 3149]], ![![12981, 2793, -2534, -809, 2041]], ![![18639, 4056, -3653, -1171, 2947]], ![![42, -36, 6, 7, -10]], ![![13709, 2962, -2680, -857, 2160]]]
  g := ![![![86, -146, -34, 7, 59], ![407, -673, -160, 29, 261], ![1857, -3006, -731, 115, 1131], ![3924, -6220, -1538, 213, 2256], ![2757, -4348, -1082, 143, 1566]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![42, 29, 1, -3, -7]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![42, 29, 1, -3, -7]] 
 ![![59, 0, 0, 0, 0], ![57, 1, 0, 0, 0], ![55, 0, 1, 0, 0], ![56, 0, 0, 1, 0], ![37, 0, 0, 0, 1]] where
  M :=![![![42, 29, 1, -3, -7], ![93, 102, 35, -3, -57], ![693, 587, 108, -35, -207], ![1248, 1195, 311, -45, -492], ![949, 874, 206, -37, -332]]]
  hmulB := by decide  
  f := ![![![-9586, -1571, 1727, 467, -1297]], ![![-9021, -1483, 1626, 442, -1224]], ![![-9257, -1490, 1663, 436, -1232]], ![![-9082, -1551, 1647, 477, -1276]], ![![-6045, -979, 1087, 288, -809]]]
  g := ![![![-21, 29, 1, -3, -7], ![-91, 102, 35, -3, -57], ![-493, 587, 108, -35, -207], ![-1072, 1195, 311, -45, -492], ![-777, 874, 206, -37, -332]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![2821, 494, -510, -152, 400]] ![![-160, -146, -34, 7, 59]]
  ![![-5508, -5028, -1168, 247, 2051]] where
 M := ![![![-5508, -5028, -1168, 247, 2051]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![-5508, -5028, -1168, 247, 2051]] ![![42, 29, 1, -3, -7]]
  ![![59, 0, 0, 0, 0]] where
 M := ![![![746291, 729535, 191691, -14514, -235528]]]
 hmul := by decide  
 g := ![![![![12649, 12365, 3249, -246, -3992]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1213, -215, 219, 66, -172]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![-1213, -215, 219, 66, -172]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![27, 51, 41, 1, 0], ![5, 46, 29, 0, 1]] where
  M :=![![![-1213, -215, 219, 66, -172], ![1866, 316, -347, -104, 276], ![-3000, -585, 524, 170, -420], ![1332, 199, -289, -99, 252], ![-542, -148, 74, 30, -63]]]
  hmulB := by decide  
  f := ![![![801, 305, -199, -76, 172]], ![![-1836, -698, 457, 174, -396]], ![![4230, 1615, -1046, -400, 900]], ![![1599, 613, -393, -151, 336]], ![![701, 270, -171, -66, 145]]]
  g := ![![![-35, 71, 41, 66, -172], ![54, -116, -67, -104, 276], ![-90, 165, 94, 170, -420], ![45, -104, -58, -99, 252], ![-17, 20, 11, 30, -63]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [11, 7, 54, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 30, 41], [4, 30, 20], [0, 1]]
 g := ![![[33, 10, 36], [13, 42], [26, 50, 4], [47, 1, 49], [1]], ![[16, 52, 36, 45], [54, 49], [44, 32, 6, 20], [30, 55, 51, 4], [20, 44, 8, 52]], ![[26, 2, 8, 9], [54, 57], [31, 27, 4, 25], [10, 23, 21, 34], [39, 17, 12, 9]]]
 h' := ![![[3, 30, 41], [35, 51, 6], [19, 48, 46], [32, 25, 59], [50, 54, 7], [0, 1]], ![[4, 30, 20], [50, 22, 14], [20, 25, 54], [31, 53, 50], [51, 3, 45], [3, 30, 41]], ![[0, 1], [38, 49, 41], [12, 49, 22], [16, 44, 13], [1, 4, 9], [4, 30, 20]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51, 22], []]
 b := ![[], [37, 12, 56], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [11, 7, 54, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-60647837, -56063036, -13388502, 2374610, 21800220]
  a := ![-5, 2, -3, 1, 24]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3832187, -19343906, -12179572, 2374610, 21800220]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 226981 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![801, 305, -199, -76, 172]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![801, 305, -199, -76, 172]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![5, 40, 1, 0, 0], ![22, 57, 0, 1, 0], ![23, 36, 0, 0, 1]] where
  M :=![![![801, 305, -199, -76, 172], ![-1836, -698, 457, 174, -396], ![4230, 1615, -1046, -400, 900], ![-3882, -1459, 979, 367, -852], ![542, 218, -124, -50, 101]]]
  hmulB := by decide  
  f := ![![![-1213, -215, 219, 66, -172]], ![![1866, 316, -347, -104, 276]], ![![1075, 180, -201, -60, 160]], ![![1328, 221, -250, -75, 200]], ![![635, 103, -121, -36, 97]]]
  g := ![![![-8, 105, -199, -76, 172], ![19, -240, 457, 174, -396], ![-40, 555, -1046, -400, 900], ![45, -506, 979, 367, -852], ![-1, 72, -124, -50, 101]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P1 : CertificateIrreducibleZModOfList' 61 2 2 5 [49, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [52, 60], [0, 1]]
 g := ![![[45, 5], [25], [27, 22], [37, 48], [52, 1]], ![[0, 56], [25], [12, 39], [32, 13], [43, 60]]]
 h' := ![![[52, 60], [51, 26], [19, 5], [17, 12], [14, 32], [0, 1]], ![[0, 1], [0, 35], [35, 56], [31, 49], [31, 29], [52, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43]]
 b := ![[], [51, 52]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N1 : CertifiedPrimeIdeal' SI61N1 61 where
  n := 2
  hpos := by decide
  P := [49, 9, 1]
  hirr := P61P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![264582, -270368, -655438, -386277, 1229627]
  a := ![51, 23, 13, 60, -197]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-266255, 60629, -655438, -386277, 1229627]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N1 B_one_repr
lemma NI61N1 : Nat.card (O ⧸ I61N1) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![-1213, -215, 219, 66, -172]] ![![801, 305, -199, -76, 172]]
  ![![61, 0, 0, 0, 0]] where
 M := ![![![61, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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


lemma PB539I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB539I1 : PrimesBelowBoundCertificateInterval O 23 61 539 where
  m := 9
  g := ![1, 1, 2, 4, 2, 2, 3, 3, 2]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB539I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0]
    · exact ![I31N0]
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1, I41N2, I41N3]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1, I53N2]
    · exact ![I59N0, I59N1, I59N2]
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
    · exact ![20511149]
    · exact ![28629151]
    · exact ![1874161, 37]
    · exact ![1681, 41, 41, 41]
    · exact ![79507, 1849]
    · exact ![4879681, 47]
    · exact ![2809, 2809, 53]
    · exact ![205379, 59, 59]
    · exact ![226981, 3721]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
      exact NI41N2
      exact NI41N3
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
      exact NI53N2
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
      exact NI59N2
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
  β := ![I37N1, I41N1, I41N2, I41N3, I47N1, I53N2, I59N1, I59N2]
  Il := ![[], [], [I37N1], [I41N1, I41N2, I41N3], [], [I47N1], [I53N2], [I59N1, I59N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
