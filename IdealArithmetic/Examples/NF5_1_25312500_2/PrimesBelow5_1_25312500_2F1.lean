
import IdealArithmetic.Examples.NF5_1_25312500_2.RI5_1_25312500_2
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


def P29P0 : CertificateIrreducibleZModOfList' 29 5 2 4 [2, 25, 0, 1, 23, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 19, 24, 19, 25], [1, 5, 0, 3, 16], [12, 25, 18, 13, 9], [0, 8, 16, 23, 8], [0, 1]]
 g := ![![[18, 2, 26, 1, 9], [27, 1, 2, 1], [6, 6, 1], []], ![[12, 27, 8, 19, 13, 13, 5, 6], [26, 6, 24, 6], [3, 16, 22, 2, 18, 8, 25, 7], [13, 26, 7, 23, 4, 23, 6, 23]], ![[20, 21, 19, 8, 5, 12, 14, 5], [22, 21, 24, 24], [23, 17, 19, 16, 13, 25, 8, 13], [0, 25, 1, 0, 19, 1, 26, 7]], ![[4, 5, 17, 10, 9, 25, 0, 5], [3, 14, 2, 7], [14, 16, 5, 3, 24, 8, 19, 28], [18, 26, 15, 11, 21, 17, 22, 4]], ![[0, 21, 27, 18, 0, 10, 9, 10], [3, 19, 6, 13], [13, 3, 17, 19, 7, 8, 23, 27], [12, 27, 23, 28, 8, 9, 6, 19]]]
 h' := ![![[22, 19, 24, 19, 25], [3, 21, 22, 4, 26], [17, 12, 22, 27, 1], [0, 0, 0, 1], [0, 1]], ![[1, 5, 0, 3, 16], [19, 24, 14, 19, 19], [10, 14, 24, 21, 8], [8, 9, 10, 10, 22], [22, 19, 24, 19, 25]], ![[12, 25, 18, 13, 9], [9, 9, 15, 3, 10], [13, 22, 4, 18, 16], [1, 23, 28, 22, 17], [1, 5, 0, 3, 16]], ![[0, 8, 16, 23, 8], [22, 4, 11, 3, 23], [12, 25, 23, 13, 23], [10, 3, 16, 11, 25], [12, 25, 18, 13, 9]], ![[0, 1], [3, 0, 25, 0, 9], [3, 14, 14, 8, 10], [5, 23, 4, 14, 23], [0, 8, 16, 23, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 10, 23, 7], [], [], []]
 b := ![[], [19, 1, 23, 9, 9], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 5
  hpos := by decide
  P := [2, 25, 0, 1, 23, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2377033816628, -1201964314454, -1733993511213, 931848766813, 119768549275]
  a := ![-16, 11, 7, -17, -30]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![81966683332, -41447045326, -59792879697, 32132716097, 4129949975]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![165, -68, -139, 39, 34]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![165, -68, -139, 39, 34]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![14, 10, 25, 1, 0], ![28, 23, 11, 0, 1]] where
  M :=![![![165, -68, -139, 39, 34], ![-440, 265, 275, -239, 44], ![18, -194, 166, 275, -283], ![1342, -522, -1119, 302, 280], ![-2782, 1526, 1924, -1258, 27]]]
  hmulB := by decide  
  f := ![![![-64103, 34674, -1695, 1451, -8597]], ![![85726, -46379, 2267, -1939, 11499]], ![![-100194, 54198, -2650, 2267, -13438]], ![![-79136, 42804, -2093, 1791, -10613]], ![![-30894, 16705, -817, 700, -4142]]]
  g := ![![![-43, -40, -48, 39, 34], ![54, 53, 186, -239, 44], ![132, 115, -116, 275, -283], ![-346, -322, -379, 302, 280], ![454, 435, 1067, -1258, 27]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 3 2 4 [14, 18, 20, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [7, 12, 10], [4, 18, 21], [0, 1]]
 g := ![![[15, 16, 20], [1, 11, 4], [1, 5, 28], [1]], ![[15, 7, 11, 25], [18, 19], [5, 7, 5, 16], [11, 3, 30, 8]], ![[14, 24, 18, 17], [25, 24, 1, 22], [27, 11, 11, 22], [25, 22, 11, 23]]]
 h' := ![![[7, 12, 10], [17, 24, 19], [17, 15, 2], [17, 13, 11], [0, 1]], ![[4, 18, 21], [29, 30, 24], [24, 6], [3, 5, 18], [7, 12, 10]], ![[0, 1], [24, 8, 19], [4, 10, 29], [24, 13, 2], [4, 18, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 5], []]
 b := ![[], [18, 22, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 3
  hpos := by decide
  P := [14, 18, 20, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3356144793, 3321174927, 1820932906, -3080946148, 1065585978]
  a := ![-121, 61, 62, -122, -243]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![320667545, 310392223, 2165262608, -3080946148, 1065585978]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 29791 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-37, 20, -1, 1, -5]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![-37, 20, -1, 1, -5]] 
 ![![31, 0, 0, 0, 0], ![16, 1, 0, 0, 0], ![19, 0, 1, 0, 0], ![21, 0, 0, 1, 0], ![16, 0, 0, 0, 1]] where
  M :=![![![-37, 20, -1, 1, -5], ![50, -27, 1, -1, 7], ![-60, 32, 0, 1, -8], ![54, -30, 1, 0, 7], ![-18, 10, -2, 0, -1]]]
  hmulB := by decide  
  f := ![![![55, 46, -9, -19, -14]], ![![32, 27, -5, -11, -8]], ![![35, 30, -5, -12, -9]], ![![41, 34, -6, -13, -10]], ![![30, 26, -4, -10, -7]]]
  g := ![![![-9, 20, -1, 1, -5], ![12, -27, 1, -1, 7], ![-15, 32, 0, 1, -8], ![13, -30, 1, 0, 7], ![-4, 10, -2, 0, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1

def I31N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-919, 506, -26, 18, -126]] i)))

def SI31N2: IdealEqSpanCertificate' Table ![![-919, 506, -26, 18, -126]] 
 ![![31, 0, 0, 0, 0], ![27, 1, 0, 0, 0], ![25, 0, 1, 0, 0], ![30, 0, 0, 1, 0], ![28, 0, 0, 0, 1]] where
  M :=![![![-919, 506, -26, 18, -126], ![1252, -657, 30, -34, 162], ![-1438, 790, -39, 30, -196], ![1342, -702, 34, -35, 174], ![-456, 264, -12, 8, -65]]]
  hmulB := by decide  
  f := ![![![-329, 142, 262, -94, -50]], ![![-265, 109, 216, -68, -48]], ![![-253, 120, 191, -88, -22]], ![![-404, 174, 322, -115, -62]], ![![-148, 40, 140, -8, -57]]]
  g := ![![![-353, 506, -26, 18, -126], ![475, -657, 30, -34, 162], ![-555, 790, -39, 30, -196], ![504, -702, 34, -35, 174], ![-184, 264, -12, 8, -65]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N2 : Nat.card (O ⧸ I31N2) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N2)

lemma isPrimeI31N2 : Ideal.IsPrime I31N2 := prime_ideal_of_norm_prime hp31.out _ NI31N2
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![165, -68, -139, 39, 34]] ![![-37, 20, -1, 1, -5]]
  ![![329, -142, -262, 94, 50]] where
 M := ![![![329, -142, -262, 94, 50]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI31N1 : IdealMulLeCertificate' Table 
  ![![329, -142, -262, 94, 50]] ![![-919, 506, -26, 18, -126]]
  ![![31, 0, 0, 0, 0]] where
 M := ![![![-31, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![723, 486, -796, -902, -469]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![723, 486, -796, -902, -469]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![14, 22, 20, 5, 1]] where
  M :=![![![723, 486, -796, -902, -469], ![2992, 1969, -1984, -2494, -1335], ![2940, 2400, -1387, -1984, -1159], ![6714, 5138, -2830, -4167, -2417], ![6364, 5180, -2294, -3626, -2183]]]
  hmulB := by decide  
  f := ![![![-149, 82, 102, -68, 3]], ![![4, -95, 86, 136, -139]], ![![804, -248, -737, 86, 275]], ![![-1222, 666, 844, -549, 15]], ![![236, -92, -198, 53, 52]]]
  g := ![![![197, 292, 232, 39, -469], ![586, 847, 668, 113, -1335], ![518, 754, 589, 103, -1159], ![1096, 1576, 1230, 214, -2417], ![998, 1438, 1118, 197, -2183]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 4 2 5 [22, 27, 26, 1, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 18, 16, 2], [17, 17, 29, 4], [3, 1, 29, 31], [0, 1]]
 g := ![![[6, 36], [32, 27, 1], [34, 24, 14, 1], [1], []], ![[33, 23, 21, 27, 25, 32], [14, 0, 26], [9, 4, 22, 36, 3, 13], [24, 9, 27], [16, 23, 4]], ![[36, 13, 22, 4, 31, 7], [7, 12, 12], [33, 26, 21, 26, 20, 12], [29, 32, 30], [12, 31, 16]], ![[17, 17, 17, 9, 2, 17], [16, 20, 28], [23, 33, 30, 14, 4, 32], [4, 26, 33], [18, 23, 36]]]
 h' := ![![[16, 18, 16, 2], [26, 22, 6], [29, 0, 14, 1], [15, 10, 11, 36], [0, 0, 1], [0, 1]], ![[17, 17, 29, 4], [24, 0, 24, 33], [31, 24, 5, 10], [30, 23, 34, 32], [15, 8, 7, 29], [16, 18, 16, 2]], ![[3, 1, 29, 31], [32, 26, 22, 23], [1, 36, 7, 7], [24, 16, 35, 15], [25, 16, 33, 20], [17, 17, 29, 4]], ![[0, 1], [27, 26, 22, 18], [3, 14, 11, 19], [16, 25, 31, 28], [20, 13, 33, 25], [3, 1, 29, 31]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [36, 29, 27], []]
 b := ![[], [], [34, 30, 28, 21], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 4
  hpos := by decide
  P := [22, 27, 26, 1, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1335702434, -400731536, -1285163128, 90572979, 528061383]
  a := ![-12, 8, 6, -13, -23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-163706944, -324813026, -320172724, -68911728, 528061383]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1874161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, -82, -102, 68, -3]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![149, -82, -102, 68, -3]] 
 ![![37, 0, 0, 0, 0], ![28, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![149, -82, -102, 68, -3], ![-4, 95, -86, -136, 139], ![-804, 248, 737, -86, -275], ![1222, -666, -844, 549, -15], ![-760, 832, 126, -946, 635]]]
  hmulB := by decide  
  f := ![![![-723, -486, 796, 902, 469]], ![![-628, -421, 656, 750, 391]], ![![-99, -78, 59, 78, 44]], ![![-201, -152, 98, 137, 78]], ![![-172, -140, 62, 98, 59]]]
  g := ![![![67, -82, -102, 68, -3], ![-66, 95, -86, -136, 139], ![-227, 248, 737, -86, -275], ![545, -666, -844, 549, -15], ![-628, 832, 126, -946, 635]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![723, 486, -796, -902, -469]] ![![149, -82, -102, 68, -3]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-49, -14, 73, 37, -61]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![-49, -14, 73, 37, -61]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![23, 14, 1, 0, 0], ![18, 34, 0, 1, 0], ![9, 4, 0, 0, 1]] where
  M :=![![![-49, -14, 73, 37, -61], ![720, -295, -589, 183, 135], ![-1238, 698, 834, -589, 48], ![-352, -136, 559, 318, -491], ![3454, -1246, -2990, 632, 907]]]
  hmulB := by decide  
  f := ![![![29929, -16228, 799, -665, 4026]], ![![-40126, 21619, -1047, 933, -5356]], ![![4229, -2340, 121, -80, 583]], ![![-21184, 11368, -545, 506, -2814]], ![![3023, -1654, 83, -63, 411]]]
  g := ![![![-45, -50, 73, 37, -61], ![238, 29, -589, 183, 135], ![-250, 216, 834, -589, 48], ![-354, -410, 559, 318, -491], ![1285, 378, -2990, 632, 907]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [2, 33, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 40], [0, 1]]
 g := ![![[37, 21], [32], [20], [29, 23], [1]], ![[0, 20], [32], [20], [8, 18], [1]]]
 h' := ![![[8, 40], [27, 12], [3, 14], [24, 26], [39, 8], [0, 1]], ![[0, 1], [0, 29], [33, 27], [27, 15], [21, 33], [8, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38]]
 b := ![[], [6, 19]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [2, 33, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-442094, 98240, 319755, -59393, -18817]
  a := ![51, -28, -25, 50, 103]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-159952, -55700, 319755, -59393, -18817]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-39, 22, -7, 3, -5]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-39, 22, -7, 3, -5]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![26, 34, 1, 0, 0], ![11, 18, 0, 1, 0], ![19, 8, 0, 0, 1]] where
  M :=![![![-39, 22, -7, 3, -5], ![46, -23, 11, -11, 11], ![-78, 34, 10, 11, -22], ![124, -60, -45, 14, 19], ![-130, 74, 70, -52, 3]]]
  hmulB := by decide  
  f := ![![![83, 96, 51, 25, 2]], ![![56, 107, 157, 127, 48]], ![![96, 148, 166, 125, 43]], ![![39, 68, 90, 71, 26]], ![![39, 58, 61, 45, 15]]]
  g := ![![![5, 6, -7, 3, -5], ![-8, -7, 11, -11, 11], ![-1, -8, 10, 11, -22], ![19, 26, -45, 14, 19], ![-35, -34, 70, -52, 3]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P1 : CertificateIrreducibleZModOfList' 41 2 2 5 [3, 40, 1] where
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
 g := ![![[27, 36], [18], [1], [36, 1], [1]], ![[22, 5], [18], [1], [37, 40], [1]]]
 h' := ![![[1, 40], [30, 6], [17, 31], [15, 1], [38, 1], [0, 1]], ![[0, 1], [36, 35], [7, 10], [16, 40], [39, 40], [1, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [26, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N1 : CertifiedPrimeIdeal' SI41N1 41 where
  n := 2
  hpos := by decide
  P := [3, 40, 1]
  hirr := P41P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-30339, 7839, 22566, -4999, -3856]
  a := ![-12, 9, 7, -10, -27]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-11922, -15575, 22566, -4999, -3856]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N1 B_one_repr
lemma NI41N1 : Nat.card (O ⧸ I41N1) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-641, -68, 42, 126, 33]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![-641, -68, 42, 126, 33]] 
 ![![41, 0, 0, 0, 0], ![29, 1, 0, 0, 0], ![16, 0, 1, 0, 0], ![37, 0, 0, 1, 0], ![34, 0, 0, 0, 1]] where
  M :=![![![-641, -68, 42, 126, 33], ![-162, -811, 86, 210, 219], ![-866, -10, -21, 86, -9], ![-116, -856, -24, 107, 179], ![-556, -292, -94, 18, 21]]]
  hmulB := by decide  
  f := ![![![8091, -5008, -5016, 4500, -995]], ![![5953, -3503, -3864, 3048, -460]], ![![1598, -1370, -627, 1440, -767]], ![![8939, -5520, -5554, 4953, -1080]], ![![6750, -3368, -4958, 2582, 383]]]
  g := ![![![-125, -68, 42, 126, 33], ![165, -811, 86, 210, 219], ![-76, -10, -21, 86, -9], ![367, -856, -24, 107, 179], ![196, -292, -94, 18, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![-49, -14, 73, 37, -61]] ![![-39, 22, -7, 3, -5]]
  ![![8091, -5008, -5016, 4500, -995]] where
 M := ![![![8091, -5008, -5016, 4500, -995]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![8091, -5008, -5016, 4500, -995]] ![![-641, -68, 42, 126, 33]]
  ![![41, 0, 0, 0, 0]] where
 M := ![![![41, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![74481, -40266, 1965, -1693, 9982]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![74481, -40266, 1965, -1693, 9982]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![8, 40, 5, 26, 1]] where
  M :=![![![74481, -40266, 1965, -1693, 9982], ![-99548, 53907, -2641, 2237, -13368], ![116412, -62940, 3076, -2641, 15605], ![-106616, 57740, -2823, 2400, -14316], ![37662, -20326, 996, -858, 5041]]]
  hmulB := by decide  
  f := ![![![25, -8, -23, 3, 9]], ![![-110, 55, 79, -43, -3]], ![![88, -76, -36, 79, -40]], ![![198, -62, -185, 20, 73]], ![![18, 10, -36, -23, 37]]]
  g := ![![![-125, -10222, -1115, -6075, 9982], ![172, 13689, 1493, 8135, -13368], ![-196, -15980, -1743, -9497, 15605], ![184, 14660, 1599, 8712, -14316], ![-62, -5162, -563, -3068, 5041]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 4 2 5 [12, 17, 4, 30, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 31, 36, 11], [26, 11, 8, 38], [40, 0, 42, 37], [0, 1]]
 g := ![![[8, 11, 15, 16], [13, 40, 18, 13], [28, 12, 6], [13, 1], []], ![[0, 34, 38, 41, 10, 6], [17, 39, 32, 0, 24, 14], [37, 16, 40], [19, 41, 5, 17, 34, 21], [32, 0, 35]], ![[22, 3, 20, 14, 37, 10], [39, 16, 14, 25, 19, 15], [24, 33, 16], [23, 8, 36, 1, 3, 35], [29, 30, 25]], ![[29, 33, 9, 4, 2, 29], [34, 2, 12, 6, 14, 2], [25, 16, 14], [41, 33, 26, 36, 32, 2], [34, 7, 36]]]
 h' := ![![[33, 31, 36, 11], [16, 23, 8, 39], [6, 8, 7, 23], [16, 25, 17, 36], [0, 0, 1], [0, 1]], ![[26, 11, 8, 38], [7, 14, 2, 14], [40, 34, 11, 23], [21, 5, 17, 13], [17, 40, 37, 27], [33, 31, 36, 11]], ![[40, 0, 42, 37], [12, 17, 33, 16], [11, 11, 20, 30], [16, 8, 5, 4], [27, 20, 41, 6], [26, 11, 8, 38]], ![[0, 1], [20, 32, 0, 17], [12, 33, 5, 10], [22, 5, 4, 33], [31, 26, 7, 10], [40, 0, 42, 37]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [24, 3, 17], []]
 b := ![[], [], [27, 42, 10, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 4
  hpos := by decide
  P := [12, 17, 4, 30, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-206987812, 40880090, 132180612, -44036586, -15830332]
  a := ![-16, 10, 4, -26, -12]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1868492, 15676590, 4914704, 8547722, -15830332]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 3418801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-25, 8, 23, -3, -9]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-25, 8, 23, -3, -9]] 
 ![![43, 0, 0, 0, 0], ![35, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![21, 0, 0, 1, 0], ![27, 0, 0, 0, 1]] where
  M :=![![![-25, 8, 23, -3, -9], ![110, -55, -79, 43, 3], ![-88, 76, 36, -79, 40], ![-198, 62, 185, -20, -73], ![614, -286, -466, 208, 59]]]
  hmulB := by decide  
  f := ![![![-74481, 40266, -1965, 1693, -9982]], ![![-58309, 31521, -1538, 1326, -7814]], ![![-28689, 15510, -757, 652, -3845]], ![![-33895, 18322, -894, 771, -4542]], ![![-47643, 25756, -1257, 1083, -6385]]]
  g := ![![![-8, 8, 23, -3, -9], ![52, -55, -79, 43, 3], ![-63, 76, 36, -79, 40], ![-64, 62, 185, -20, -73], ![271, -286, -466, 208, 59]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![74481, -40266, 1965, -1693, 9982]] ![![-25, 8, 23, -3, -9]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2247, -1656, -1142, 1632, -671]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![2247, -1656, -1142, 1632, -671]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![43, 7, 27, 1, 0], ![30, 30, 3, 0, 1]] where
  M :=![![![2247, -1656, -1142, 1632, -671], ![7200, -1241, -7538, -652, 3935], ![-27370, 11630, 22037, -7538, -4587], ![18976, -13684, -9916, 13357, -5235], ![20884, 2740, -27906, -11058, 20895]]]
  hmulB := by decide  
  f := ![![![1042701, -564060, 27572, -23594, 139851]], ![![-1394532, 754365, -36884, 31550, -187039]], ![![1629794, -881638, 43093, -36884, 218589]], ![![1650751, -892985, 43647, -37357, 221402]], ![![-109332, 59132, -2897, 2470, -14664]]]
  g := ![![![-1017, 150, -919, 1632, -671], ![-1762, -2441, -37, -652, 3935], ![9242, 4298, 5092, -7538, -4587], ![-8475, 1061, -7550, 13357, -5235], ![-2776, -11632, 4425, -11058, 20895]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [18, 43, 42, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [32, 32, 28], [20, 14, 19], [0, 1]]
 g := ![![[40, 28, 21], [0, 7, 25], [24, 22, 36], [29, 5, 1], []], ![[26, 23, 21, 18], [0, 32, 40, 24], [31, 42, 13, 32], [11, 12, 27, 36], [25, 32]], ![[15, 24, 40, 11], [23, 34, 17, 43], [35, 23, 6, 44], [11, 1, 23, 45], [34, 32]]]
 h' := ![![[32, 32, 28], [0, 2, 16], [38, 7, 5], [42, 26, 6], [0, 0, 1], [0, 1]], ![[20, 14, 19], [36, 24, 45], [30, 0, 31], [41, 18, 13], [10, 21, 14], [32, 32, 28]], ![[0, 1], [32, 21, 33], [11, 40, 11], [42, 3, 28], [23, 26, 32], [20, 14, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1], []]
 b := ![[], [45, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [18, 43, 42, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2066696, 1047644, 1513696, -809688, -109585]
  a := ![1, 9, 7, 2, -13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![766754, 212830, 504341, -809688, -109585]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 103823 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1042701, -564060, 27572, -23594, 139851]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![1042701, -564060, 27572, -23594, 139851]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![37, 44, 1, 0, 0], ![36, 6, 0, 1, 0], ![19, 12, 0, 0, 1]] where
  M :=![![![1042701, -564060, 27572, -23594, 139851], ![-1394532, 754365, -36884, 31550, -187039], ![1629794, -881638, 43093, -36884, 218589], ![-1493560, 807956, -39510, 33781, -200329], ![526944, -285032, 13922, -11938, 70665]]]
  hmulB := by decide  
  f := ![![![2247, -1656, -1142, 1632, -671]], ![![7200, -1241, -7538, -652, 3935]], ![![7927, -2218, -7487, 514, 3058]], ![![3044, -1718, -2048, 1451, -123]], ![![3191, -928, -2980, 258, 1178]]]
  g := ![![![-37984, -70508, 27572, -23594, 139851], ![50811, 94307, -36884, 31550, -187039], ![-59362, -110202, 43093, -36884, 218589], ![54435, 101014, -39510, 33781, -200329], ![-19171, -35616, 13922, -11938, 70665]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P1 : CertificateIrreducibleZModOfList' 47 2 2 5 [11, 36, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 46], [0, 1]]
 g := ![![[46, 27], [38, 36], [45, 36], [8, 27], [1]], ![[14, 20], [11, 11], [18, 11], [23, 20], [1]]]
 h' := ![![[11, 46], [5, 36], [22, 41], [6, 6], [36, 11], [0, 1]], ![[0, 1], [25, 11], [3, 6], [25, 41], [16, 36], [11, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [27, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N1 : CertifiedPrimeIdeal' SI47N1 47 where
  n := 2
  hpos := by decide
  P := [11, 36, 1]
  hirr := P47P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-484, -12, 260, -123, 8]
  a := ![-3, 0, 1, -4, -3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-124, -230, 260, -123, 8]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N1 B_one_repr
lemma NI47N1 : Nat.card (O ⧸ I47N1) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![2247, -1656, -1142, 1632, -671]] ![![1042701, -564060, 27572, -23594, 139851]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4841, -4366, 305, 293, 1118]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![4841, -4366, 305, 293, 1118]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![26, 35, 3, 1, 0], ![17, 12, 23, 0, 1]] where
  M :=![![![4841, -4366, 305, 293, 1118], ![-10582, 2113, -93, 903, -532], ![8356, -6228, 78, -93, 1435], ![-10716, 2632, -687, 290, -918], ![2038, -2838, -552, -382, 383]]]
  hmulB := by decide  
  f := ![![![-1305, -116, 1691, 611, -1223]], ![![14532, -6169, -11707, 3993, 2445]], ![![-23348, 13568, 15318, -11707, 1548]], ![![7452, -3389, -5788, 2374, 916]], ![![-5915, 3946, 3395, -3702, 1154]]]
  g := ![![![-411, -529, -496, 293, 1118], ![-472, -436, 178, 903, -532], ![-257, -381, -616, -93, 1435], ![-50, 66, 369, 290, -918], ![103, 112, -155, -382, 383]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [19, 21, 25, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 44, 25], [23, 8, 28], [0, 1]]
 g := ![![[36, 39, 16], [33, 15], [35, 52, 17], [0, 42], [1]], ![[48, 16, 12, 52], [0, 38], [51, 22, 22, 11], [40, 24], [22, 24, 17, 43]], ![[15, 50, 2, 44], [16, 52], [16, 24, 28, 25], [3, 11], [47, 32, 16, 10]]]
 h' := ![![[5, 44, 25], [2, 35, 4], [24, 20, 42], [43, 0, 32], [34, 32, 28], [0, 1]], ![[23, 8, 28], [9, 21, 6], [3, 9, 41], [24, 38, 44], [25, 50, 17], [5, 44, 25]], ![[0, 1], [21, 50, 43], [22, 24, 23], [9, 15, 30], [38, 24, 8], [23, 8, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33, 10], []]
 b := ![[], [2, 50, 42], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [19, 21, 25, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10402163, -7072506, -7124084, 5898787, -516511]
  a := ![12, -6, -3, 8, 29]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2531804, -3911923, -244164, 5898787, -516511]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 148877 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1305, 116, -1691, -611, 1223]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![1305, 116, -1691, -611, 1223]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![30, 24, 1, 0, 0], ![11, 19, 0, 1, 0], ![8, 26, 0, 0, 1]] where
  M :=![![![1305, 116, -1691, -611, 1223], ![-14532, 6169, 11707, -3993, -2445], ![23348, -13568, -15318, 11707, -1548], ![9690, 1390, -13061, -5302, 9873], ![-71310, 26926, 60642, -14752, -17009]]]
  hmulB := by decide  
  f := ![![![-4841, 4366, -305, -293, -1118]], ![![10582, -2113, 93, -903, 532]], ![![1894, 1632, -132, -573, -419]], ![![2991, 99, -17, -390, -24]], ![![4422, -324, 10, -480, 85]]]
  g := ![![![924, 387, -1691, -611, 1223], ![-5703, -2554, 11707, -3993, -2445], ![6915, 3243, -15318, 11707, -1548], ![7186, 2998, -13061, -5302, 9873], ![-30042, -13320, 60642, -14752, -17009]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P1 : CertificateIrreducibleZModOfList' 53 2 2 5 [35, 15, 1] where
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
 g := ![![[8, 17], [6], [19, 28], [7], [38, 1]], ![[18, 36], [6], [23, 25], [7], [23, 52]]]
 h' := ![![[38, 52], [48, 32], [24, 18], [45, 9], [48, 31], [0, 1]], ![[0, 1], [45, 21], [19, 35], [16, 44], [7, 22], [38, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [31, 43]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N1 : CertifiedPrimeIdeal' SI53N1 53 where
  n := 2
  hpos := by decide
  P := [35, 15, 1]
  hirr := P53P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-14765, 3534, 10901, -2139, -815]
  a := ![9, -6, -5, 8, 19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5882, -3703, 10901, -2139, -815]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N1 B_one_repr
lemma NI53N1 : Nat.card (O ⧸ I53N1) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![4841, -4366, 305, 293, 1118]] ![![1305, 116, -1691, -611, 1223]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0, 0, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0, 0, 0]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![0, 0, 0, 0, 59]] where
  M :=![![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![0, 0, 0, 0, 59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 5 2 5 [45, 5, 9, 5, 38, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [25, 11, 57, 2, 48], [4, 44, 15, 48, 42], [47, 11, 15, 45, 29], [4, 51, 31, 23, 58], [0, 1]]
 g := ![![[6, 44, 56, 18, 35], [40, 50, 44, 29, 57], [38, 1, 57, 48], [23, 21, 1], []], ![[56, 0, 31, 0, 8, 36, 33, 48], [16, 2, 12, 41, 1, 35, 22, 53], [16, 2, 2, 22], [42, 2, 9, 12, 5, 35, 36, 27], [27, 26, 32, 21, 31, 0, 33, 26]], ![[21, 48, 2, 27, 39, 19, 56, 13], [25, 25, 41, 0, 16, 12, 26, 50], [6, 49, 45, 4], [18, 28, 3, 45, 52, 44, 15, 14], [52, 53, 29, 49, 49, 4, 39, 43]], ![[45, 51, 20, 12, 43, 10, 41, 35], [49, 30, 57, 11, 39, 31, 34, 19], [36, 58, 38, 36], [18, 5, 4, 25, 30, 24, 30, 21], [24, 48, 1, 17, 10, 47, 9, 22]], ![[48, 23, 54, 23, 36, 38, 17, 11], [21, 20, 34, 12, 42, 24, 22, 50], [11, 51, 17, 46], [27, 41, 40, 5, 56, 1, 1, 44], [38, 27, 48, 20, 11, 50, 48, 58]]]
 h' := ![![[25, 11, 57, 2, 48], [29, 40, 23, 1, 25], [22, 50, 57, 10, 36], [27, 2, 56, 45, 15], [0, 0, 0, 1], [0, 1]], ![[4, 44, 15, 48, 42], [4, 9, 16, 31, 1], [48, 42, 25, 19, 50], [1, 47, 33, 40, 9], [14, 27, 31, 12, 14], [25, 11, 57, 2, 48]], ![[47, 11, 15, 45, 29], [22, 22, 42, 38, 33], [53, 36, 54, 4, 2], [38, 26, 55, 5, 2], [25, 57, 25, 0, 43], [4, 44, 15, 48, 42]], ![[4, 51, 31, 23, 58], [11, 40, 22, 29, 15], [22, 29, 19, 7, 27], [7, 37, 19, 50, 53], [24, 53, 30, 17, 31], [47, 11, 15, 45, 29]], ![[0, 1], [3, 7, 15, 19, 44], [58, 20, 22, 19, 3], [50, 6, 14, 37, 39], [6, 40, 32, 29, 30], [4, 51, 31, 23, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51, 11, 18, 7], [], [], []]
 b := ![[], [5, 27, 57, 43, 6], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 5
  hpos := by decide
  P := [45, 5, 9, 5, 38, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-25964071, -7059468, 11762476, 1935082, 1800857]
  a := ![4, 0, 0, 5, 2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-440069, -119652, 199364, 32798, 30523]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 714924299 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def PBC59 : ContainsPrimesAboveP 59 ![I59N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![59, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 59 (by decide) 𝕀

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


def P61P0 : CertificateIrreducibleZModOfList' 61 5 2 5 [42, 48, 18, 42, 58, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [60, 28, 38, 0, 37], [48, 3, 11, 51, 35], [30, 18, 31, 39, 4], [48, 11, 42, 32, 46], [0, 1]]
 g := ![![[16, 10, 56, 27, 27], [35, 27, 35, 9], [28, 17, 17, 9, 1], [28, 3, 1], []], ![[37, 47, 26, 22, 46, 26, 39, 44], [46, 25, 50, 4], [4, 46, 60, 36, 37, 34, 40, 32], [57, 40, 57, 45, 2, 7, 30, 51], [45, 42, 24, 57, 57, 1, 8, 23]], ![[30, 17, 48, 30, 48, 49, 46, 33], [41, 37, 40, 15], [43, 1, 11, 48, 13, 7, 59, 10], [6, 20, 38, 43, 53, 42, 14, 55], [41, 35, 11, 2, 11, 48, 9, 53]], ![[54, 30, 17, 10, 31, 46, 1, 27], [23, 3, 32, 46], [45, 48, 19, 45, 49, 8, 1, 46], [29, 56, 30, 33, 3, 25, 33, 3], [45, 50, 15, 34, 26, 3, 51, 3]], ![[1, 22, 21, 27, 6, 1, 60, 45], [37, 31, 39, 16], [59, 50, 29, 59, 55, 47, 52, 22], [38, 38, 13, 43, 9, 36, 48, 13], [16, 31, 49, 16, 25, 28, 7, 41]]]
 h' := ![![[60, 28, 38, 0, 37], [39, 53, 20, 37, 24], [44, 0, 0, 19, 58], [44, 55, 42, 3, 1], [0, 0, 0, 1], [0, 1]], ![[48, 3, 11, 51, 35], [17, 11, 39, 58, 54], [34, 40, 53, 40, 2], [46, 37, 19, 30, 18], [0, 3, 28, 43, 6], [60, 28, 38, 0, 37]], ![[30, 18, 31, 39, 4], [2, 57, 56, 0, 29], [4, 28, 52, 55, 36], [56, 21, 13, 27, 3], [46, 35, 28, 33, 18], [48, 3, 11, 51, 35]], ![[48, 11, 42, 32, 46], [59, 35, 23, 39, 49], [54, 36, 3, 45, 30], [4, 56, 22, 3, 15], [39, 54, 13, 27, 4], [30, 18, 31, 39, 4]], ![[0, 1], [10, 27, 45, 49, 27], [10, 18, 14, 24, 57], [60, 14, 26, 59, 24], [59, 30, 53, 18, 33], [48, 11, 42, 32, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 4, 3, 60], [], [], []]
 b := ![[], [34, 28, 2, 46, 33], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 5
  hpos := by decide
  P := [42, 48, 18, 42, 58, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3394252533738162, -1517941589248557, -2664470892881414, 1043573384297337, 465266688804385]
  a := ![-60, 45, 21, -60, -127]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![55643484159642, -24884288348337, -43679850702974, 17107760398317, 7627322767285]
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



lemma PB314I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB314I1 : PrimesBelowBoundCertificateInterval O 23 61 314 where
  m := 9
  g := ![1, 3, 2, 3, 2, 2, 2, 1, 1]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB314I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0]
    · exact ![I31N0, I31N1, I31N2]
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0]
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
    · exact ![20511149]
    · exact ![29791, 31, 31]
    · exact ![1874161, 37]
    · exact ![1681, 1681, 41]
    · exact ![3418801, 43]
    · exact ![103823, 2209]
    · exact ![148877, 2809]
    · exact ![714924299]
    · exact ![844596301]
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
      exact NI31N1
      exact NI31N2
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
      exact NI41N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
  β := ![I31N1, I31N2, I37N1, I41N2, I43N1]
  Il := ![[], [I31N1, I31N2], [I37N1], [I41N2], [I43N1], [], [], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
