
import IdealArithmetic.Examples.NF5_1_13500000_3.RI5_1_13500000_3
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


def P29P0 : CertificateIrreducibleZModOfList' 29 5 2 4 [12, 8, 5, 15, 26, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [27, 19, 0, 1, 13], [12, 18, 28, 8, 22], [18, 24, 12, 14, 5], [4, 25, 18, 6, 18], [0, 1]]
 g := ![![[5, 23, 28, 3, 9], [16, 18, 4, 13], [23, 3, 1], []], ![[3, 4, 26, 28, 5, 16, 26, 9], [27, 3, 24, 7], [10, 22, 28, 10, 12, 12, 14, 16], [7, 10, 18, 27, 22, 7, 22, 22]], ![[26, 12, 2, 6, 9, 7], [1, 11, 7, 22], [26, 24, 2, 19, 1, 4, 15, 4], [25, 10, 13, 21, 6, 6, 2, 5]], ![[3, 7, 11, 26, 10, 8, 10, 25], [28, 12, 3, 13], [6, 17, 22, 8, 16, 8, 18, 22], [6, 17, 10, 9, 11, 5, 4, 9]], ![[2, 27, 10, 8, 27, 18, 5, 11], [17, 1], [4, 28, 12, 13, 27, 2, 18, 11], [10, 3, 23, 15, 28, 1, 12, 3]]]
 h' := ![![[27, 19, 0, 1, 13], [4, 21, 23, 25, 3], [14, 12, 23, 9, 19], [0, 0, 0, 1], [0, 1]], ![[12, 18, 28, 8, 22], [11, 10, 23, 12, 20], [4, 11, 11, 22, 6], [24, 23, 26, 13, 12], [27, 19, 0, 1, 13]], ![[18, 24, 12, 14, 5], [10, 25, 20, 17], [15, 20, 0, 1, 14], [7, 3, 25, 19, 25], [12, 18, 28, 8, 22]], ![[4, 25, 18, 6, 18], [17, 4, 15, 21, 18], [18, 20, 17, 25, 19], [18, 21, 26, 28, 4], [18, 24, 12, 14, 5]], ![[0, 1], [8, 27, 6, 12, 17], [26, 24, 7, 1], [2, 11, 10, 26, 17], [4, 25, 18, 6, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 27, 24, 9], [], [], []]
 b := ![[], [23, 27, 13, 2, 6], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 5
  hpos := by decide
  P := [12, 8, 5, 15, 26, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-12910884506, -4283294432, -5334344796, 6499524370, 13678666582]
  a := ![-22, -8, 30, -26, -77]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-445202914, -147699808, -183942924, 224121530, 471678158]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-131, 25, 15, 2, -50]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![-131, 25, 15, 2, -50]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![2, 15, 9, 26, 1]] where
  M :=![![![-131, 25, 15, 2, -50], ![208, -114, -87, 38, 228], ![-760, 159, 114, -22, -380], ![612, -277, -191, 51, 492], ![-604, 182, 134, -40, -395]]]
  hmulB := by decide  
  f := ![![![-13, 3, 3, -2, -2]], ![![0, -12, 11, -2, -20]], ![![72, 9, -40, 14, 52]], ![![-76, 29, 9, -11, 4]], ![![-42, 21, 1, -6, 9]]]
  g := ![![![-1, 25, 15, 42, -50], ![-8, -114, -69, -190, 228], ![0, 189, 114, 318, -380], ![-12, -247, -149, -411, 492], ![6, 197, 119, 330, -395]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 4 2 4 [30, 8, 2, 0, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [16, 2, 22, 30], [26, 18, 7, 29], [20, 10, 2, 3], [0, 1]]
 g := ![![[16, 30, 13, 16], [10, 13, 10, 25], [23, 29, 0, 1], []], ![[6, 20, 17, 14, 25, 22], [30, 21, 30, 24, 18, 30], [5, 6, 30, 3, 30, 23], [15, 8, 16, 13, 4, 30]], ![[22, 23, 2, 20, 18, 17], [22, 29, 5, 6, 8, 27], [2, 7, 26, 0, 21, 12], [10, 8, 0, 0, 22, 23]], ![[11, 12, 25, 29, 20, 27], [21, 24, 19, 4, 14, 17], [7, 21, 9, 11, 28, 29], [8, 25, 26, 4, 23, 27]]]
 h' := ![![[16, 2, 22, 30], [10, 28, 10, 27], [23, 0, 1, 5], [0, 0, 0, 1], [0, 1]], ![[26, 18, 7, 29], [3, 30, 28, 28], [15, 30, 29, 30], [19, 29, 22, 16], [16, 2, 22, 30]], ![[20, 10, 2, 3], [22, 8, 0, 10], [0, 13, 25, 23], [9, 7, 14, 26], [26, 18, 7, 29]], ![[0, 1], [30, 27, 24, 28], [23, 19, 7, 4], [10, 26, 26, 19], [20, 10, 2, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [23, 7, 10], []]
 b := ![[], [], [20, 29, 21, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 4
  hpos := by decide
  P := [30, 8, 2, 0, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![33543151565, -25321483800, -17526876312, 10024270805, 43375785625]
  a := ![17, -58, -22, -45, 58]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1716400635, -21805105425, -13158353127, -36056327595, 43375785625]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 923521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, -3, -3, 2, 2]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![13, -3, -3, 2, 2]] 
 ![![31, 0, 0, 0, 0], ![12, 1, 0, 0, 0], ![11, 0, 1, 0, 0], ![21, 0, 0, 1, 0], ![20, 0, 0, 0, 1]] where
  M :=![![![13, -3, -3, 2, 2], ![0, 12, -11, 2, 20], ![-72, -9, 40, -14, -52], ![76, -29, -9, 11, -4], ![-52, 10, 14, -8, -11]]]
  hmulB := by decide  
  f := ![![![131, -25, -15, -2, 50]], ![![44, -6, -3, -2, 12]], ![![71, -14, -9, 0, 30]], ![![69, -8, -4, -3, 18]], ![![104, -22, -14, 0, 45]]]
  g := ![![![0, -3, -3, 2, 2], ![-15, 12, -11, 2, 20], ![30, -9, 40, -14, -52], ![12, -29, -9, 11, -4], ![2, 10, 14, -8, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![-131, 25, 15, 2, -50]] ![![13, -3, -3, 2, 2]]
  ![![31, 0, 0, 0, 0]] where
 M := ![![![-31, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-551, -12, 260, -104, -325]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![-551, -12, 260, -104, -325]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![19, 17, 14, 24, 1]] where
  M :=![![![-551, -12, 260, -104, -325], ![884, -395, -38, 104, -156], ![1040, 950, -1331, 340, 2080], ![-3922, 222, 1554, -703, -1702], ![1946, 156, -1012, 390, 1265]]]
  hmulB := by decide  
  f := ![![![-37, 4, -20, 38, 75]], ![![-148, -19, -74, 112, 232]], ![![-480, -110, -227, 300, 640]], ![![-606, -194, -278, 317, 704]], ![![-665, -175, -312, 392, 848]]]
  g := ![![![152, 149, 130, 208, -325], ![104, 61, 58, 104, -156], ![-1040, -930, -823, -1340, 2080], ![768, 788, 686, 1085, -1702], ![-597, -577, -506, -810, 1265]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 4 2 5 [6, 8, 13, 26, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 5, 15, 25], [36, 36, 21, 23], [30, 32, 1, 26], [0, 1]]
 g := ![![[3, 3, 30, 33], [27, 22, 28], [16, 36, 9, 10], [1], []], ![[3, 10, 4, 15, 26, 9], [14, 24, 25], [18, 24, 10, 20, 31, 30], [3, 35, 1], [5, 3, 33]], ![[0, 34, 26, 6, 21, 8], [30, 19, 28], [2, 25, 11, 19, 34, 22], [13, 6, 1], [36, 14, 11]], ![[13, 22, 14, 6, 23, 16], [26, 25, 36], [5, 25, 5, 33, 34, 9], [6, 12, 4], [24, 14, 10]]]
 h' := ![![[19, 5, 15, 25], [26, 32, 0, 12], [15, 25, 27, 18], [31, 29, 24, 11], [0, 0, 1], [0, 1]], ![[36, 36, 21, 23], [16, 20, 11, 29], [27, 1, 14, 32], [23, 15, 31, 33], [35, 21, 12, 1], [19, 5, 15, 25]], ![[30, 32, 1, 26], [9, 5, 17, 26], [35, 12, 30, 18], [8, 8, 1, 34], [7, 0, 16, 1], [36, 36, 21, 23]], ![[0, 1], [26, 17, 9, 7], [16, 36, 3, 6], [35, 22, 18, 33], [16, 16, 8, 35], [30, 32, 1, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [8, 19, 28], []]
 b := ![[], [], [10, 10, 22, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 4
  hpos := by decide
  P := [6, 8, 13, 26, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![981574, -582568, 741286, -1507480, -3026376]
  a := ![-7, -5, 10, -11, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1580614, 1374752, 1165150, 1922312, -3026376]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1874161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-37, 4, -20, 38, 75]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-37, 4, -20, 38, 75]] 
 ![![37, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![36, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![13, 0, 0, 0, 1]] where
  M :=![![![-37, 4, -20, 38, 75], ![-148, -19, -74, 112, 232], ![-480, -110, -227, 300, 640], ![-606, -194, -278, 317, 704], ![-122, -32, -56, 70, 151]]]
  hmulB := by decide  
  f := ![![![-551, -12, 260, -104, -325]], ![![9, -11, 6, 0, -13]], ![![-508, 14, 217, -92, -260]], ![![-106, 6, 42, -19, -46]], ![![-141, 0, 64, -26, -80]]]
  g := ![![![-8, 4, -20, 38, 75], ![-13, -19, -74, 112, 232], ![-14, -110, -227, 300, 640], ![12, -194, -278, 317, 704], ![-1, -32, -56, 70, 151]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![-551, -12, 260, -104, -325]] ![![-37, 4, -20, 38, 75]]
  ![![37, 0, 0, 0, 0]] where
 M := ![![![37, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![51, 84, 172, -214, -543]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![51, 84, 172, -214, -543]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![40, 8, 32, 5, 1]] where
  M :=![![![51, 84, 172, -214, -543], ![1316, 9, 282, -512, -824], ![1248, 1086, 1433, -1484, -3872], ![4118, 594, 982, -1279, -2232], ![-478, 544, 536, -398, -1449]]]
  hmulB := by decide  
  f := ![![![269, 12, -132, 52, 165]], ![![-452, 189, 30, -56, 68]], ![![-496, -478, 661, -164, -1056]], ![![2010, -94, -818, 361, 930]], ![![8, -338, 306, -49, -553]]]
  g := ![![![531, 108, 428, 61, -543], ![836, 161, 650, 88, -824], ![3808, 782, 3057, 436, -3872], ![2278, 450, 1766, 241, -2232], ![1402, 296, 1144, 167, -1449]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 4 2 5 [6, 36, 33, 34, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 36, 8, 22], [21, 10, 23, 12], [26, 35, 10, 7], [0, 1]]
 g := ![![[34, 7, 9, 5], [2, 11, 23], [23, 13, 10], [7, 1], []], ![[29, 30, 19, 18, 12, 29], [3, 8, 1], [1, 34, 9], [1, 32, 25, 15, 34, 24], [7, 9, 33]], ![[23, 27, 14, 33, 16, 27], [35, 38, 8], [31, 18, 9], [27, 30, 19, 18, 39, 14], [8, 2, 21]], ![[36, 1, 40, 2, 6, 3], [7, 24, 4], [28, 37, 10], [21, 16, 8, 40, 23, 22], [17, 32, 8]]]
 h' := ![![[1, 36, 8, 22], [20, 40, 1, 28], [27, 20, 6, 8], [40, 29, 20, 16], [0, 0, 1], [0, 1]], ![[21, 10, 23, 12], [21, 36, 31, 22], [30, 36, 21, 1], [35, 18, 39, 38], [0, 12, 26, 4], [1, 36, 8, 22]], ![[26, 35, 10, 7], [0, 40, 6, 22], [28, 39, 13, 34], [3, 26, 13, 3], [24, 38, 30, 34], [21, 10, 23, 12]], ![[0, 1], [24, 7, 3, 10], [5, 28, 1, 39], [38, 9, 10, 25], [0, 32, 25, 3], [26, 35, 10, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [28, 1, 34], []]
 b := ![[], [], [35, 7, 36, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 4
  hpos := by decide
  P := [6, 36, 33, 34, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1853237070, -1224524320, -558195702, 25981320, 439114680]
  a := ![31, 27, -42, 50, 108]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-473605470, -115547360, -356338182, -52916880, 439114680]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 2825761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-269, -12, 132, -52, -165]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-269, -12, 132, -52, -165]] 
 ![![41, 0, 0, 0, 0], ![16, 1, 0, 0, 0], ![31, 0, 1, 0, 0], ![31, 0, 0, 1, 0], ![15, 0, 0, 0, 1]] where
  M :=![![![-269, -12, 132, -52, -165], ![452, -189, -30, 56, -68], ![496, 478, -661, 164, 1056], ![-2010, 94, 818, -361, -930], ![994, 84, -524, 198, 675]]]
  hmulB := by decide  
  f := ![![![-51, -84, -172, 214, 543]], ![![-52, -33, -74, 96, 232]], ![![-69, -90, -165, 198, 505]], ![![-139, -78, -154, 193, 465]], ![![-7, -44, -76, 88, 234]]]
  g := ![![![-2, -12, 132, -52, -165], ![90, -189, -30, 56, -68], ![-185, 478, -661, 164, 1056], ![-91, 94, 818, -361, -930], ![-9, 84, -524, 198, 675]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![51, 84, 172, -214, -543]] ![![-269, -12, 132, -52, -165]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 9, 17, -22, -47]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![37, 9, 17, -22, -47]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![36, 25, 1, 0, 0], ![23, 7, 0, 1, 0], ![28, 1, 0, 0, 1]] where
  M :=![![![37, 9, 17, -22, -47], ![100, 32, 47, -54, -120], ![264, 93, 116, -122, -276], ![258, 113, 113, -101, -242], ![62, 22, 26, -26, -59]]]
  hmulB := by decide  
  f := ![![![-31, -13, 25, -8, -33]], ![![100, -14, -31, 18, 20]], ![![32, -17, 1, 4, -12]], ![![-9, -10, 13, -3, -21]], ![![-14, -8, 13, -4, -17]]]
  g := ![![![29, -5, 17, -22, -47], ![70, -15, 47, -54, -120], ![154, -39, 116, -122, -276], ![123, -41, 113, -101, -242], ![32, -9, 26, -26, -59]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [11, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 42], [0, 1]]
 g := ![![[9, 4], [18, 6], [24], [24, 40], [1]], ![[0, 39], [26, 37], [24], [20, 3], [1]]]
 h' := ![![[30, 42], [17, 41], [30, 36], [37, 14], [32, 30], [0, 1]], ![[0, 1], [0, 2], [35, 7], [27, 29], [29, 13], [30, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [14, 22]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [11, 13, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6501, -7287, -499, 2178, 7443]
  a := ![-35, -7, 48, -31, -122]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5745, -407, -499, 2178, 7443]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-16729, -380, 7872, -3178, -9655]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-16729, -380, 7872, -3178, -9655]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![8, 1, 1, 0, 0], ![39, 4, 0, 1, 0], ![21, 8, 0, 0, 1]] where
  M :=![![![-16729, -380, 7872, -3178, -9655], ![25908, -12035, -622, 3032, -5872], ![35616, 28318, -41971, 10884, 65936], ![-123058, 8282, 47754, -21719, -52748], ![62218, 3808, -31472, 12178, 39859]]]
  hmulB := by decide  
  f := ![![![-29, 948, 456, 64, -537]], ![![2404, 491, -510, 1168, 3044]], ![![-124, 259, 63, 124, 68]], ![![145, 850, 250, 313, 161]], ![![307, 592, 140, 266, 282]]]
  g := ![![![5744, 1900, 7872, -3178, -9655], ![836, 545, -622, 3032, -5872], ![-33436, -11645, -41971, 10884, 65936], ![33713, 10916, 47754, -21719, -52748], ![-23209, -7728, -31472, 12178, 39859]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P1 : CertificateIrreducibleZModOfList' 43 2 2 5 [18, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 42], [0, 1]]
 g := ![![[5, 15], [11, 11], [31], [37, 16], [1]], ![[31, 28], [10, 32], [31], [16, 27], [1]]]
 h' := ![![[39, 42], [17, 31], [12, 22], [22, 17], [25, 39], [0, 1]], ![[0, 1], [22, 12], [10, 21], [40, 26], [41, 4], [39, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40]]
 b := ![[], [40, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N1 : CertifiedPrimeIdeal' SI43N1 43 where
  n := 2
  hpos := by decide
  P := [18, 4, 1]
  hirr := P43P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![17042, -12000, 1784, -228, 3164]
  a := ![28, -2, -38, 10, 98]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1274, -888, 1784, -228, 3164]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N1 B_one_repr
lemma NI43N1 : Nat.card (O ⧸ I43N1) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N1

def I43N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-489, 149, 103, -22, -296]] i)))

def SI43N2: IdealEqSpanCertificate' Table ![![-489, 149, 103, -22, -296]] 
 ![![43, 0, 0, 0, 0], ![17, 1, 0, 0, 0], ![12, 0, 1, 0, 0], ![40, 0, 0, 1, 0], ![21, 0, 0, 0, 1]] where
  M :=![![![-489, 149, 103, -22, -296], ![1096, -408, -311, 118, 876], ![-3032, 903, 636, -150, -1852], ![2856, -1069, -795, 277, 2216], ![-2608, 846, 614, -180, -1761]]]
  hmulB := by decide  
  f := ![![![2701, -2149, 755, 182, -2088]], ![![1279, -765, 126, 124, -572]], ![![-52, -509, 490, -86, -868]], ![![2704, -2373, 959, 149, -2456]], ![![1027, -865, 331, 62, -873]]]
  g := ![![![66, 149, 103, -22, -296], ![-264, -408, -311, 118, 876], ![439, 903, 636, -150, -1852], ![-629, -1069, -795, 277, 2216], ![461, 846, 614, -180, -1761]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N2 : Nat.card (O ⧸ I43N2) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N2)

lemma isPrimeI43N2 : Ideal.IsPrime I43N2 := prime_ideal_of_norm_prime hp43.out _ NI43N2
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![37, 9, 17, -22, -47]] ![![-16729, -380, 7872, -3178, -9655]]
  ![![2701, -2149, 755, 182, -2088]] where
 M := ![![![2701, -2149, 755, 182, -2088]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![2701, -2149, 755, 182, -2088]] ![![-489, 149, 103, -22, -296]]
  ![![43, 0, 0, 0, 0]] where
 M := ![![![43, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1, I43N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
    exact isPrimeI43N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0 ⊙ MulI43N1)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0, 0, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0, 0, 0]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![0, 0, 0, 0, 47]] where
  M :=![![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![0, 0, 0, 0, 47]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 5 2 5 [15, 25, 42, 1, 40, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 40, 14, 8, 26], [22, 21, 29, 43, 19], [23, 37, 42, 2, 6], [39, 42, 9, 41, 43], [0, 1]]
 g := ![![[2, 20, 40, 12, 36], [14, 6, 27, 21, 1], [19, 39, 22, 0, 2], [1], []], ![[16, 3, 24, 40, 34, 20, 4, 30], [38, 3, 2, 37, 5, 5, 44, 15], [42, 40, 29, 21, 10, 1, 16, 15], [5, 20, 17, 36, 16, 30, 11, 20], [35, 9, 25, 18]], ![[0, 1, 1, 40, 45, 4, 23, 19], [13, 43, 40, 9, 6, 44, 14, 44], [19, 23, 6, 34, 39, 17, 32, 26], [10, 10, 27, 4, 12, 36, 24, 19], [34, 39, 25, 32]], ![[4, 41, 12, 18, 39, 38, 39, 2], [13, 17, 4, 4, 0, 44, 27, 4], [6, 25, 8, 33, 13, 13, 36, 24], [0, 29, 12, 31, 27, 30, 41, 21], [1, 7, 41, 36]], ![[6, 28, 46, 28, 26, 6, 15, 40], [19, 23, 37, 41, 6, 3, 45, 20], [30, 5, 22, 40, 16, 34, 22, 39], [43, 23, 38, 41, 43, 23, 30, 22], [43, 34, 19, 16]]]
 h' := ![![[17, 40, 14, 8, 26], [25, 39, 13, 27, 6], [44, 11, 10, 7, 1], [32, 22, 5, 46, 7], [0, 0, 1], [0, 1]], ![[22, 21, 29, 43, 19], [19, 13, 31, 8, 23], [17, 5, 27, 5, 37], [36, 29, 9, 30, 37], [46, 21, 6, 37, 33], [17, 40, 14, 8, 26]], ![[23, 37, 42, 2, 6], [4, 8, 34, 30, 46], [27, 22, 21, 40, 19], [11, 23, 41, 26, 41], [21, 6, 20, 4, 46], [22, 21, 29, 43, 19]], ![[39, 42, 9, 41, 43], [15, 22, 41, 40, 4], [35, 37, 1, 16, 19], [19, 8, 0, 2, 2], [44, 21, 25, 24, 36], [23, 37, 42, 2, 6]], ![[0, 1], [27, 12, 22, 36, 15], [33, 19, 35, 26, 18], [4, 12, 39, 37, 7], [30, 46, 42, 29, 26], [39, 42, 9, 41, 43]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13, 8, 12, 44], [], [], []]
 b := ![[], [19, 27, 20, 45, 20], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 5
  hpos := by decide
  P := [15, 25, 42, 1, 40, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-83927343238, 18174441421, 22790513803, -7894394386, -45239900948]
  a := ![-13, 7, 23, 2, -52]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1785688154, 386690243, 484904549, -167965838, -962551084]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 229345007 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def PBC47 : ContainsPrimesAboveP 47 ![I47N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![47, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 47 (by decide) 𝕀

instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, -25, 3, -26, -44]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-5, -25, 3, -26, -44]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![38, 38, 1, 0, 0], ![20, 13, 0, 1, 0], ![21, 28, 0, 0, 1]] where
  M :=![![![-5, -25, 3, -26, -44], ![72, -28, 43, -98, -188], ![360, 17, 184, -306, -620], ![592, 133, 285, -379, -808], ![104, 14, 50, -76, -157]]]
  hmulB := by decide  
  f := ![![![271, -81, -75, 22, 204]], ![![-728, 218, 195, -62, -508]], ![![-294, 87, 78, -26, -196]], ![![-108, 35, 26, -9, -68]], ![![-249, 73, 67, -22, -169]]]
  g := ![![![25, 27, 3, -26, -44], ![82, 92, 43, -98, -188], ![236, 271, 184, -306, -620], ![270, 318, 285, -379, -808], ![57, 66, 50, -76, -157]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [30, 45, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 52], [0, 1]]
 g := ![![[28, 4], [7], [1, 52], [43], [8, 1]], ![[7, 49], [7], [46, 1], [43], [16, 52]]]
 h' := ![![[8, 52], [1, 51], [23, 31], [24, 30], [25, 34], [0, 1]], ![[0, 1], [38, 2], [6, 22], [52, 23], [32, 19], [8, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [15, 36]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [30, 45, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2520, -1739, -625, 328, 2786]
  a := ![13, -1, -18, 8, 46]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-732, -1137, -625, 328, 2786]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 7, 1, 4, 6]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![5, 7, 1, 4, 6]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![42, 37, 1, 0, 0], ![18, 26, 0, 1, 0], ![26, 13, 0, 0, 1]] where
  M :=![![![5, 7, 1, 4, 6], ![-8, 10, -5, 18, 32], ![-56, 5, -34, 62, 124], ![-120, -19, -57, 81, 170], ![-16, -2, -10, 16, 33]]]
  hmulB := by decide  
  f := ![![![-15, -1, 7, -4, -2]], ![![-8, -12, 19, -2, -48]], ![![-14, -9, 17, -4, -32]], ![![-14, -5, 13, -3, -26]], ![![-6, -4, 7, -2, -11]]]
  g := ![![![-5, -4, 1, 4, 6], ![-18, -13, -5, 18, 32], ![-56, -37, -34, 62, 124], ![-68, -42, -57, 81, 170], ![-14, -9, -10, 16, 33]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P1 : CertificateIrreducibleZModOfList' 53 2 2 5 [4, 51, 1] where
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
 g := ![![[26, 40], [13], [], [], [2, 1]], ![[0, 13], [13], [], [], [4, 52]]]
 h' := ![![[2, 52], [1, 26], [0, 15], [11], [45], [0, 1]], ![[0, 1], [0, 27], [30, 38], [11], [45], [2, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [44, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N1 : CertifiedPrimeIdeal' SI53N1 53 where
  n := 2
  hpos := by decide
  P := [4, 51, 1]
  hirr := P53P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-20502, -10497, -11815, 13450, 37569]
  a := ![45, 13, -59, 47, 156]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-14022, -7763, -11815, 13450, 37569]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N1 B_one_repr
lemma NI53N1 : Nat.card (O ⧸ I53N1) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N1

def I53N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3295, 1007, 559, -464, -117]] i)))

def SI53N2: IdealEqSpanCertificate' Table ![![-3295, 1007, 559, -464, -117]] 
 ![![53, 0, 0, 0, 0], ![31, 1, 0, 0, 0], ![46, 0, 1, 0, 0], ![40, 0, 0, 1, 0], ![20, 0, 0, 0, 1]] where
  M :=![![![-3295, 1007, 559, -464, -117], ![-1388, -3200, 3557, -738, -6028], ![21160, 1431, -10828, 4162, 13780], ![-18542, 8847, 231, -2135, 4588], ![13486, -3434, -2918, 2002, 1613]]]
  hmulB := by decide  
  f := ![![![-4741, -213, -719, 1198, 1595]], ![![-2803, -205, -500, 764, 1129]], ![![-4646, -231, -692, 1134, 1486]], ![![-3578, -373, -707, 993, 1562]], ![![-2066, -38, -246, 458, 507]]]
  g := ![![![-742, 1007, 559, -464, -117], ![1590, -3200, 3557, -738, -6028], ![619, 1431, -10828, 4162, 13780], ![-5845, 8847, 231, -2135, 4588], ![2676, -3434, -2918, 2002, 1613]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N2 : Nat.card (O ⧸ I53N2) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N2)

lemma isPrimeI53N2 : Ideal.IsPrime I53N2 := prime_ideal_of_norm_prime hp53.out _ NI53N2
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-5, -25, 3, -26, -44]] ![![5, 7, 1, 4, 6]]
  ![![3831, 312, 1940, -3094, -6330]] where
 M := ![![![3831, 312, 1940, -3094, -6330]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI53N1 : IdealMulLeCertificate' Table 
  ![![3831, 312, 1940, -3094, -6330]] ![![-3295, 1007, 559, -464, -117]]
  ![![53, 0, 0, 0, 0]] where
 M := ![![![-3233, 159, 1219, -530, -1325]]]
 hmul := by decide  
 g := ![![![![-61, 3, 23, -10, -25]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-93, 18, 2, 16, -2]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-93, 18, 2, 16, -2]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![44, 46, 1, 0, 0], ![50, 56, 0, 1, 0], ![48, 13, 0, 0, 1]] where
  M :=![![![-93, 18, 2, 16, -2], ![72, -75, -82, 68, 232], ![-656, 58, -19, 108, 24], ![132, -246, -230, 163, 592], ![-420, 100, 60, 4, -181]]]
  hmulB := by decide  
  f := ![![![225, 202, -286, 72, 454]], ![![-1528, 11, 678, -284, -808]], ![![-988, 140, 317, -164, -304]], ![![-1214, 202, 362, -197, -324]], ![![-164, 153, -66, -8, 163]]]
  g := ![![![-15, -16, 2, 16, -2], ![-184, -53, -82, 68, 232], ![-108, -92, -19, 108, 24], ![-446, -110, -230, 163, 592], ![92, -9, 60, 4, -181]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [35, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 58], [0, 1]]
 g := ![![[0, 27], [], [29], [0, 45], [0, 1]], ![[0, 32], [], [29], [0, 14], [0, 58]]]
 h' := ![![[0, 58], [0, 26], [47], [0, 18], [0, 24], [0, 1]], ![[0, 1], [0, 33], [47], [0, 41], [0, 35], [0, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [0, 43]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [35, 0, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2932, -1898, -647, 1096, 3304]
  a := ![19, 5, -26, 18, 66]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3184, -1296, -647, 1096, 3304]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-47, 11, -27, 56, 109]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![-47, 11, -27, 56, 109]] 
 ![![59, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![50, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![45, 0, 0, 0, 1]] where
  M :=![![![-47, 11, -27, 56, 109], ![-212, -18, -107, 170, 348], ![-712, -149, -342, 466, 988], ![-938, -285, -431, 505, 1112], ![-182, -46, -86, 110, 237]]]
  hmulB := by decide  
  f := ![![![-291, -191, 301, -86, -437]], ![![9, -11, 6, 0, -13]], ![![-266, -143, 246, -74, -346]], ![![-122, -53, 103, -31, -150]], ![![-199, -135, 209, -60, -300]]]
  g := ![![![-73, 11, -27, 56, 109], ![-212, -18, -107, 170, 348], ![-563, -149, -342, 466, 988], ![-587, -285, -431, 505, 1112], ![-131, -46, -86, 110, 237]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![541, 782, -960, 218, 1582]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![541, 782, -960, 218, 1582]] 
 ![![59, 0, 0, 0, 0], ![22, 1, 0, 0, 0], ![47, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![47, 0, 0, 0, 1]] where
  M :=![![![541, 782, -960, 218, 1582], ![-5456, -201, 2638, -1048, -3276], ![8912, -3866, -465, 1084, -1568], ![8032, 4866, -8072, 2227, 12362], ![-1136, -3100, 3352, -676, -5727]]]
  hmulB := by decide  
  f := ![![![4983, -674, -284, -314, 1162]], ![![1758, -177, -46, -148, 280]], ![![4459, -608, -273, -254, 1106]], ![![-65, 148, 112, -55, -252]], ![![4331, -638, -300, -230, 1147]]]
  g := ![![![-789, 782, -960, 218, 1582], ![544, -201, 2638, -1048, -3276], ![3157, -3866, -465, 1084, -1568], ![-5209, 4866, -8072, 2227, 12362], ![3063, -3100, 3352, -676, -5727]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2

def I59N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-49, 15, 13, -4, -35]] i)))

def SI59N3: IdealEqSpanCertificate' Table ![![-49, 15, 13, -4, -35]] 
 ![![59, 0, 0, 0, 0], ![47, 1, 0, 0, 0], ![33, 0, 1, 0, 0], ![27, 0, 0, 1, 0], ![56, 0, 0, 0, 1]] where
  M :=![![![-49, 15, 13, -4, -35], ![124, -40, -31, 10, 84], ![-296, 103, 68, -22, -196], ![286, -105, -63, 19, 196], ![-254, 90, 58, -18, -173]]]
  hmulB := by decide  
  f := ![![![-229, -131, -95, 50, 147]], ![![-189, -109, -78, 40, 119]], ![![-135, -82, -55, 24, 77]], ![![-99, -64, -40, 13, 49]], ![![-218, -126, -90, 46, 137]]]
  g := ![![![15, 15, 13, -4, -35], ![-33, -40, -31, 10, 84], ![71, 103, 68, -22, -196], ![-71, -105, -63, 19, 196], ![64, 90, 58, -18, -173]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N3 : Nat.card (O ⧸ I59N3) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N3)

lemma isPrimeI59N3 : Ideal.IsPrime I59N3 := prime_ideal_of_norm_prime hp59.out _ NI59N3
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-93, 18, 2, 16, -2]] ![![-47, 11, -27, 56, 109]]
  ![![-15513, -6113, -6823, 6644, 15421]] where
 M := ![![![-15513, -6113, -6823, 6644, 15421]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![-15513, -6113, -6823, 6644, 15421]] ![![541, 782, -960, 218, 1582]]
  ![![-229, -131, -95, 50, 147]] where
 M := ![![![-229, -131, -95, 50, 147]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI59N2 : IdealMulLeCertificate' Table 
  ![![-229, -131, -95, 50, 147]] ![![-49, 15, 13, -4, -35]]
  ![![59, 0, 0, 0, 0]] where
 M := ![![![59, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1, I59N2, I59N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
    exact isPrimeI59N2
    exact isPrimeI59N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0 ⊙ MulI59N1 ⊙ MulI59N2)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5081, -2552, 4624, -1330, -6952]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![-5081, -2552, 4624, -1330, -6952]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![37, 7, 50, 1, 0], ![13, 24, 60, 0, 1]] where
  M :=![![![-5081, -2552, 4624, -1330, -6952], ![22488, -1787, -8476, 3928, 9188], ![-21040, 17940, -6979, -1240, 18240], ![-50204, -13736, 35168, -11423, -49754], ![16124, 10580, -16948, 4592, 26155]]]
  hmulB := by decide  
  f := ![![![163, -248, -224, 150, 572]], ![![-1688, 89, -4, 152, -188]], ![![1360, -1540, -1199, 600, 2880]], ![![959, -1397, -1114, 599, 2662]], ![![743, -1548, -1240, 686, 2911]]]
  g := ![![![2205, 2846, 8004, -1330, -6952], ![-3972, -4095, -12396, 3928, 9188], ![-3480, -6740, -17039, -1240, 18240], ![16709, 20661, 58878, -11423, -49754], ![-8095, -10644, -29768, 4592, 26155]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [32, 14, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [27, 29, 7], [24, 31, 54], [0, 1]]
 g := ![![[43, 41, 57], [20, 13], [43, 46, 27], [48, 12, 39], [1]], ![[39, 51, 37, 38], [35, 13], [22, 58, 8, 21], [58, 9, 51, 26], [43, 19, 40, 38]], ![[16, 3, 11, 30], [49, 52], [9, 2, 40, 38], [44, 42, 30, 43], [12, 23, 57, 23]]]
 h' := ![![[27, 29, 7], [28, 43, 22], [27, 60, 47], [50, 29, 37], [29, 47, 51], [0, 1]], ![[24, 31, 54], [52, 52, 7], [47, 5, 47], [16, 54, 8], [7, 54, 19], [27, 29, 7]], ![[0, 1], [60, 27, 32], [46, 57, 28], [18, 39, 16], [20, 21, 52], [24, 31, 54]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34, 32], []]
 b := ![[], [23, 20, 39], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [32, 14, 10, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-55884, -6706, 9709, 7991, -17517]
  a := ![-2, 3, 4, 3, -9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2030, 5865, 10839, 7991, -17517]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 226981 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, -248, -224, 150, 572]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![163, -248, -224, 150, 572]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![39, 22, 1, 0, 0], ![59, 22, 0, 1, 0], ![26, 60, 0, 0, 1]] where
  M :=![![![163, -248, -224, 150, 572], ![-1688, 89, -4, 152, -188], ![1360, -1540, -1199, 600, 2880], ![-3716, 336, 312, -75, -1466], ![2116, -940, -692, 248, 1847]]]
  hmulB := by decide  
  f := ![![![-5081, -2552, 4624, -1330, -6952]], ![![22488, -1787, -8476, 3928, 9188]], ![![4517, -1982, -215, 546, -832]], ![![2373, -3338, 1992, -57, -4226]], ![![20218, -2672, -6644, 3372, 6503]]]
  g := ![![![-243, -540, -224, 150, 572], ![-92, 133, -4, 152, -188], ![-1019, -2642, -1199, 600, 2880], ![437, 1362, 312, -75, -1466], ![-550, -1672, -692, 248, 1847]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P1 : CertificateIrreducibleZModOfList' 61 2 2 5 [40, 35, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [26, 60], [0, 1]]
 g := ![![[39, 3], [16], [46, 47], [35, 5], [26, 1]], ![[56, 58], [16], [48, 14], [43, 56], [52, 60]]]
 h' := ![![[26, 60], [9, 8], [51, 57], [3, 48], [58, 26], [0, 1]], ![[0, 1], [34, 53], [8, 4], [31, 13], [2, 35], [26, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [14, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N1 : CertifiedPrimeIdeal' SI61N1 61 where
  n := 2
  hpos := by decide
  P := [40, 35, 1]
  hirr := P61P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-250206, -99013, -91941, 110248, 287413]
  a := ![-135, -39, 182, -151, -476]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-174457, -290927, -91941, 110248, 287413]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N1 B_one_repr
lemma NI61N1 : Nat.card (O ⧸ I61N1) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![-5081, -2552, 4624, -1330, -6952]] ![![163, -248, -224, 150, 572]]
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


lemma PB229I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB229I1 : PrimesBelowBoundCertificateInterval O 23 61 229 where
  m := 9
  g := ![1, 2, 2, 2, 3, 1, 3, 4, 2]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB229I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0]
    · exact ![I31N0, I31N1]
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1, I43N2]
    · exact ![I47N0]
    · exact ![I53N0, I53N1, I53N2]
    · exact ![I59N0, I59N1, I59N2, I59N3]
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
    · exact ![923521, 31]
    · exact ![1874161, 37]
    · exact ![2825761, 41]
    · exact ![1849, 1849, 43]
    · exact ![229345007]
    · exact ![2809, 2809, 53]
    · exact ![3481, 59, 59, 59]
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
      exact NI31N1
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
      exact NI43N2
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
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
      exact NI59N3
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
  β := ![I31N1, I37N1, I41N1, I43N2, I53N2, I59N1, I59N2, I59N3]
  Il := ![[], [I31N1], [I37N1], [I41N1], [I43N2], [], [I53N2], [I59N1, I59N2, I59N3], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
