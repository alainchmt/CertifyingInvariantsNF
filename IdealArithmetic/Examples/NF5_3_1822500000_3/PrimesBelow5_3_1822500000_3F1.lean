
import IdealArithmetic.Examples.NF5_3_1822500000_3.RI5_3_1822500000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3391, -710, 516, -536, -1754]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![-3391, -710, 516, -536, -1754]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![12, 26, 16, 1, 0], ![21, 4, 1, 0, 1]] where
  M :=![![![-3391, -710, 516, -536, -1754], ![5944, -29, -584, 952, 2338], ![-7448, 750, 857, 304, -266], ![1520, -1474, 372, 1009, 874], ![3904, 154, -470, 412, 1319]]]
  hmulB := by decide  
  f := ![![![-2931, -610, -808, 656, -3414]], ![![14968, -1485, 4620, -2224, 24942]], ![![-104216, -3302, -30703, 18824, -151398]], ![![-40996, -3440, -11848, 7929, -56062]], ![![-6035, -722, -1721, 1220, -7901]]]
  g := ![![![1375, 698, 374, -536, -1754], ![-1882, -1177, -626, 952, 2338], ![-190, -210, -129, 304, -266], ![-998, -1076, -574, 1009, 874], ![-991, -546, -289, 412, 1319]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 3 2 4 [27, 5, 18, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 20, 1], [21, 8, 28], [0, 1]]
 g := ![![[24, 27, 22], [9, 13], [19, 3, 5], [1]], ![[1, 1, 28, 6], [12, 25], [28, 9, 6, 16], [13, 3, 13, 1]], ![[23, 10, 6, 9], [7, 25], [7, 13, 8, 9], [23, 19, 13, 28]]]
 h' := ![![[19, 20, 1], [12, 17, 15], [9, 2, 10], [2, 24, 11], [0, 1]], ![[21, 8, 28], [1, 28, 21], [8, 6, 24], [12, 25, 25], [19, 20, 1]], ![[0, 1], [19, 13, 22], [11, 21, 24], [27, 9, 22], [21, 8, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 15], []]
 b := ![[], [14, 13, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 3
  hpos := by decide
  P := [27, 5, 18, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2619810199, 8036708645, -6913070245, -10758754820, -22384396440]
  a := ![-55, 82, -115, -139, -330]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![20570950789, 13010411025, 6469358735, -10758754820, -22384396440]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 24389 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2931, 610, 808, -656, 3414]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![2931, 610, 808, -656, 3414]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![8, 21, 1, 0, 0], ![19, 21, 0, 1, 0], ![11, 11, 0, 0, 1]] where
  M :=![![![2931, 610, 808, -656, 3414], ![-14968, 1485, -4620, 2224, -24942], ![104216, 3302, 30703, -18824, 151398], ![-124576, 998, -37232, 21291, -189046], ![69120, -1114, 20718, -11676, 105805]]]
  hmulB := by decide  
  f := ![![![3391, 710, -516, 536, 1754]], ![![-5944, 29, 584, -952, -2338]], ![![-3112, 191, 251, -552, -1200]], ![![-2135, 537, 72, -373, -574]], ![![-1103, 275, 42, -172, -267]]]
  g := ![![![-987, -1384, 808, -656, 3414], ![8762, 11247, -4620, 2224, -24942], ![-49970, -65915, 30703, -18824, 151398], ![63733, 83285, -37232, 21291, -189046], ![-35815, -46719, 20718, -11676, 105805]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P1 : CertificateIrreducibleZModOfList' 29 2 2 4 [15, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [17, 28], [0, 1]]
 g := ![![[24, 20], [24], [13, 24], [17, 1]], ![[16, 9], [24], [15, 5], [5, 28]]]
 h' := ![![[17, 28], [23, 7], [8, 13], [6, 13], [0, 1]], ![[0, 1], [26, 22], [26, 16], [24, 16], [17, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [4, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N1 : CertifiedPrimeIdeal' SI29N1 29 where
  n := 2
  hpos := by decide
  P := [15, 12, 1]
  hirr := P29P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![60040604, -154761788, 136535370, 206619900, 445979372]
  a := ![-689, 1003, -1441, -1754, -4137]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-340130812, -422992950, 136535370, 206619900, 445979372]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N1 B_one_repr
lemma NI29N1 : Nat.card (O ⧸ I29N1) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![-3391, -710, 516, -536, -1754]] ![![2931, 610, 808, -656, 3414]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1179323, -728, 351528, -203690, 1775410]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![1179323, -728, 351528, -203690, 1775410]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![23, 19, 9, 15, 1]] where
  M :=![![![1179323, -728, 351528, -203690, 1775410], ![-7509020, 14983, -2239370, 1294408, -11321330], ![47874136, -70914, 14274575, -8258588, 72139546], ![-58824916, 96878, -17540802, 10145281, -88656722], ![32819572, -55124, 9786472, -5659988, 49465073]]]
  hmulB := by decide  
  f := ![![![93, -1964, 412, -326, -1638]], ![![5900, 2709, -1218, 1168, 4278]], ![![-14776, -1882, 1885, -2636, -7374]], ![![6500, 398, -842, 567, 2102]], ![![2657, -95, -325, 9, 373]]]
  g := ![![![-1279197, -1088178, -504102, -865640, 1775410], ![8157470, 6939363, 3214600, 5519818, -11321330], ![-51978562, -44216848, -20483269, -35172638, 72139546], ![63879990, 54341116, 25173216, 43225681, -88656722], ![-35641197, -30319081, -14045135, -24117293, 49465073]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 4 2 4 [30, 22, 22, 11, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 20, 19, 24], [23, 6, 27, 19], [20, 4, 16, 19], [0, 1]]
 g := ![![[8, 13, 18, 2], [20, 22, 6, 4], [30, 6, 20, 1], []], ![[19, 22, 15, 12], [17, 27, 13, 17, 2, 27], [30, 5, 6, 18, 2, 15], [11, 21, 25, 26, 25, 29]], ![[30, 23, 26, 14, 14, 25], [13, 9, 22, 25, 30, 4], [4, 14, 25, 26, 28, 2], [14, 14, 4, 23, 13, 8]], ![[26, 23, 22, 10, 20, 25], [10, 21, 0, 4, 19, 9], [2, 19, 12, 0, 3, 1], [15, 12, 24, 11, 4, 8]]]
 h' := ![![[8, 20, 19, 24], [20, 17, 18, 8], [30, 28, 3, 29], [0, 0, 0, 1], [0, 1]], ![[23, 6, 27, 19], [27, 21, 27], [3, 22, 2, 6], [27, 23, 14, 12], [8, 20, 19, 24]], ![[20, 4, 16, 19], [3, 22, 4, 27], [3, 2, 2, 17], [29, 21, 19, 25], [23, 6, 27, 19]], ![[0, 1], [15, 2, 13, 27], [16, 10, 24, 10], [17, 18, 29, 24], [20, 4, 16, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [8, 24, 14], []]
 b := ![[], [], [26, 12, 11, 27], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 4
  hpos := by decide
  P := [30, 22, 22, 11, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![15306034216134, -62141951082760, 51979751446742, 84048258395746, 165635100470084]
  a := ![-54, 80, -113, -137, -325]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-122396815374058, -103522866452076, -46410843638194, -77434782214694, 165635100470084]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 923521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-93, 1964, -412, 326, 1638]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![-93, 1964, -412, 326, 1638]] 
 ![![31, 0, 0, 0, 0], ![11, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![25, 0, 0, 1, 0], ![12, 0, 0, 0, 1]] where
  M :=![![![-93, 1964, -412, 326, 1638], ![-5900, -2709, 1218, -1168, -4278], ![14776, 1882, -1885, 2636, 7374], ![-6500, -398, 842, -567, -2102], ![-3612, -1724, 744, -804, -2791]]]
  hmulB := by decide  
  f := ![![![-1179323, 728, -351528, 203690, -1775410]], ![![-176243, -225, -52498, 30522, -264780]], ![![-1658455, 2358, -494489, 286118, -2498896]], ![![946511, -2538, 282342, -163001, 1428112]], ![![-1515208, 2060, -451768, 261428, -2282903]]]
  g := ![![![-1557, 1964, -412, 326, 1638], ![3251, -2709, 1218, -1168, -4278], ![-4989, 1882, -1885, 2636, 7374], ![1121, -398, 842, -567, -2102], ![2152, -1724, 744, -804, -2791]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![1179323, -728, 351528, -203690, 1775410]] ![![-93, 1964, -412, 326, 1638]]
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

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![245, 212, -72, 68, 264]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![245, 212, -72, 68, 264]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![20, 1, 5, 1, 0], ![36, 14, 36, 0, 1]] where
  M :=![![![245, 212, -72, 68, 264], ![-920, -223, 148, -160, -504], ![1696, 64, -211, 248, 600], ![-600, 48, 76, -87, -104], ![-616, -148, 84, -96, -379]]]
  hmulB := by decide  
  f := ![![![-3087, -4468, -440, 1628, 2648]], ![![-7336, -10619, -1044, 3872, 6296]], ![![-17440, -25248, -2471, 9224, 14984]], ![![-4332, -6271, -615, 2289, 3720]], ![![-22612, -32734, -3208, 11952, 19421]]]
  g := ![![![-287, -96, -268, 68, 264], ![552, 189, 516, -160, -504], ![-672, -232, -623, 248, 600], ![132, 43, 115, -87, -104], ![404, 142, 384, -96, -379]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [27, 16, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 26, 27], [13, 10, 10], [0, 1]]
 g := ![![[31, 19, 9], [1, 9], [5, 32, 26], [27, 1], []], ![[36, 7, 6, 30], [4, 11], [7, 35, 20, 4], [36, 26], [34, 26]], ![[15, 19, 6, 25], [7, 30], [17, 33, 24, 10], [11, 10], [14, 26]]]
 h' := ![![[14, 26, 27], [31, 25, 34], [13, 28, 34], [11, 22, 10], [0, 0, 1], [0, 1]], ![[13, 10, 10], [31, 21, 16], [18, 25, 23], [18, 17, 28], [18, 0, 10], [14, 26, 27]], ![[0, 1], [21, 28, 24], [5, 21, 17], [20, 35, 36], [13, 0, 26], [13, 10, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 28], []]
 b := ![[], [25, 10, 25], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [27, 16, 10, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![220517667807, -728396430971, 621541771476, 978082592392, 2003346121309]
  a := ![246, -359, 514, 624, 1475]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2471934987761, -804143911397, -2064576528584, 978082592392, 2003346121309]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 50653 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7717, 11169, 1101, -4068, -6618]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![7717, 11169, 1101, -4068, -6618]] 
 ![![37, 0, 0, 0, 0], ![19, 1, 0, 0, 0], ![9, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  M :=![![![7717, 11169, 1101, -4068, -6618], ![18336, 26539, 2616, -9666, -15726], ![43572, 63060, 6217, -22968, -37362], ![9990, 14463, 1425, -5267, -8574], ![-12576, -18204, -1794, 6630, 10789]]]
  hmulB := by decide  
  f := ![![![-551, -549, 177, -162, -654]], ![![-221, -266, 81, -72, -300]], ![![-255, -141, 58, -54, -204]], ![![-59, -108, 30, -23, -108]], ![![-65, -93, 27, -24, -101]]]
  g := ![![![-3773, 11169, 1101, -4068, -6618], ![-8965, 26539, 2616, -9666, -15726], ![-21303, 63060, 6217, -22968, -37362], ![-4885, 14463, 1425, -5267, -8574], ![6149, -18204, -1794, 6630, 10789]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 1, -1, -2, -2]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![3, 1, -1, -2, -2]] 
 ![![37, 0, 0, 0, 0], ![26, 1, 0, 0, 0], ![27, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![27, 0, 0, 0, 1]] where
  M :=![![![3, 1, -1, -2, -2], ![4, 11, -6, -14, -14], ![28, 60, -37, -92, -98], ![30, 57, -35, -83, -86], ![-4, -6, 4, 10, 11]]]
  hmulB := by decide  
  f := ![![![31, 19, 3, -8, -6]], ![![22, 15, 2, -6, -6]], ![![29, 17, 4, -8, 0]], ![![2, 5, -1, -1, -10]], ![![25, 13, 3, -6, 1]]]
  g := ![![![2, 1, -1, -2, -2], ![10, 11, -6, -14, -14], ![77, 60, -37, -92, -98], ![67, 57, -35, -83, -86], ![-9, -6, 4, 10, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![245, 212, -72, 68, 264]] ![![7717, 11169, 1101, -4068, -6618]]
  ![![-31, -19, -3, 8, 6]] where
 M := ![![![-31, -19, -3, 8, 6]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![-31, -19, -3, 8, 6]] ![![3, 1, -1, -2, -2]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0, 0, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0, 0, 0]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![0, 0, 0, 0, 41]] where
  M :=![![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![0, 0, 0, 0, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 5 2 5 [34, 36, 2, 13, 40, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 4, 19, 31, 20], [3, 26, 9, 32, 20], [33, 15, 21, 11, 35], [23, 36, 33, 8, 7], [0, 1]]
 g := ![![[21, 35, 28, 23, 4], [15, 34, 40, 8], [20, 4, 16, 1], [1], []], ![[39, 27, 29, 13, 31, 28, 2, 36], [1, 2, 14, 4], [35, 13, 14, 33], [35, 13, 22, 35, 5, 37, 32, 40], [11, 6, 0, 31]], ![[35, 5, 15, 9, 22, 37, 14, 16], [27, 40], [14, 35, 35, 20], [28, 21, 34, 35, 40, 12, 7, 10], [5, 37, 40, 31]], ![[8, 9, 2, 32, 6, 22, 9, 35], [9, 31, 8, 9], [7, 36, 30, 40], [14, 31, 24, 10, 29, 35, 40, 26], [25, 2, 27, 36]], ![[13, 18, 10, 34, 32, 39, 5, 29], [4, 21, 32, 4], [26, 20, 36, 21], [0, 27, 6, 7, 16, 31, 26, 35], [39, 9, 38, 8]]]
 h' := ![![[24, 4, 19, 31, 20], [33, 4, 40, 15, 2], [25, 34, 7, 27, 34], [7, 5, 39, 28, 1], [0, 0, 1], [0, 1]], ![[3, 26, 9, 32, 20], [9, 10, 34, 1, 16], [17, 13, 11, 23, 2], [10, 14, 23, 21, 22], [38, 2, 34, 21, 17], [24, 4, 19, 31, 20]], ![[33, 15, 21, 11, 35], [5, 6, 34, 40, 38], [12, 12, 3, 32], [18, 36, 9, 21, 15], [3, 30, 37, 36, 29], [3, 26, 9, 32, 20]], ![[23, 36, 33, 8, 7], [32, 19, 27, 27, 1], [16, 27, 22, 34, 3], [34, 1, 40, 37, 32], [34, 22, 38, 20, 8], [33, 15, 21, 11, 35]], ![[0, 1], [12, 2, 29, 40, 25], [36, 37, 39, 7, 2], [31, 26, 12, 16, 12], [23, 28, 13, 5, 28], [23, 36, 33, 8, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17, 39, 31, 15], [], [], []]
 b := ![[], [5, 16, 32, 6, 30], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 5
  hpos := by decide
  P := [34, 36, 2, 13, 40, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9019462022230426, 26949660564030404, -23249690813040924, -36033771489751390, -75412786859293784]
  a := ![-31, 46, -64, -76, -185]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-219986878590986, 657308794244644, -567065629586364, -878872475359790, -1839336264860824]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 115856201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def PBC41 : ContainsPrimesAboveP 41 ![I41N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![41, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 41 (by decide) 𝕀

instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-209423, -302926, -29898, 110354, 179309]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![-209423, -302926, -29898, 110354, 179309]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![8, 1, 1, 0, 0], ![26, 1, 0, 1, 0], ![24, 37, 0, 0, 1]] where
  M :=![![![-209423, -302926, -29898, 110354, 179309], ![-496528, -719794, -70717, 262028, 427703], ![-1186756, -1710315, -170102, 623810, 1005821], ![-264818, -392282, -36816, 141803, 241799], ![337664, 493736, 47636, -179230, -297779]]]
  hmulB := by decide  
  f := ![![![-19557, -40294, 24758, 59780, 62517]], ![![-130508, -261414, 161067, 387668, 404775]], ![![-26296, -53071, 32667, 78674, 82164]], ![![-32824, -66586, 40971, 98745, 103168]], ![![-121088, -243134, 149769, 360578, 376544]]]
  g := ![![![-166113, -163205, -29898, 110354, 179309], ![-395544, -389212, -70717, 262028, 427703], ![-934528, -915800, -170102, 623810, 1005821], ![-220008, -219624, -36816, 141803, 241799], ![273564, 270771, 47636, -179230, -297779]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [23, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 42], [0, 1]]
 g := ![![[1, 15], [12, 21], [41], [28, 13], [1]], ![[0, 28], [2, 22], [41], [30, 30], [1]]]
 h' := ![![[20, 42], [25, 31], [4, 35], [1, 16], [20, 20], [0, 1]], ![[0, 1], [0, 12], [16, 8], [20, 27], [33, 23], [20, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [9, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [23, 23, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![281423, -1096464, 924054, 1488258, 2942400]
  a := ![-56, 84, -118, -150, -336]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2707519, -2613432, 924054, 1488258, 2942400]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, 4, -2, 2, 6]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![9, 4, -2, 2, 6]] 
 ![![43, 0, 0, 0, 0], ![20, 1, 0, 0, 0], ![30, 0, 1, 0, 0], ![24, 0, 0, 1, 0], ![26, 0, 0, 0, 1]] where
  M :=![![![9, 4, -2, 2, 6], ![-20, -3, 4, -4, -6], ![16, -2, -9, 8, -18], ![12, 2, 8, -5, 34], ![-28, -2, -2, 0, -27]]]
  hmulB := by decide  
  f := ![![![307, 448, 46, -162, -266]], ![![160, 233, 24, -84, -138]], ![![254, 370, 39, -132, -218]], ![![180, 262, 28, -93, -154]], ![![174, 254, 26, -92, -151]]]
  g := ![![![-5, 4, -2, 2, 6], ![4, -3, 4, -4, -6], ![14, -2, -9, 8, -18], ![-24, 2, 8, -5, 34], ![18, -2, -2, 0, -27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1

def I43N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-39, 5, 3, -4, -9]] i)))

def SI43N2: IdealEqSpanCertificate' Table ![![-39, 5, 3, -4, -9]] 
 ![![43, 0, 0, 0, 0], ![32, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![42, 0, 0, 1, 0], ![30, 0, 0, 0, 1]] where
  M :=![![![-39, 5, 3, -4, -9], ![28, -18, 1, 2, -3], ![16, 25, -6, 14, 39], ![-24, -15, 7, 1, -11], ![20, -10, 0, 0, -3]]]
  hmulB := by decide  
  f := ![![![91, -15, 29, -12, 163]], ![![52, -12, 17, -6, 99]], ![![112, -5, 34, -18, 177]], ![![-30, -15, -7, 9, -19]], ![![130, -10, 40, -20, 213]]]
  g := ![![![5, 5, 3, -4, -9], ![14, -18, 1, 2, -3], ![-58, 25, -6, 14, 39], ![16, -15, 7, 1, -11], ![10, -10, 0, 0, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N2 : Nat.card (O ⧸ I43N2) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N2)

lemma isPrimeI43N2 : Ideal.IsPrime I43N2 := prime_ideal_of_norm_prime hp43.out _ NI43N2

def I43N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8389, 16879, -10393, -25022, -26128]] i)))

def SI43N3: IdealEqSpanCertificate' Table ![![8389, 16879, -10393, -25022, -26128]] 
 ![![43, 0, 0, 0, 0], ![33, 1, 0, 0, 0], ![29, 0, 1, 0, 0], ![22, 0, 0, 1, 0], ![42, 0, 0, 0, 1]] where
  M :=![![![8389, 16879, -10393, -25022, -26128], ![54468, 109583, -67474, -162446, -169624], ![353604, 711430, -438051, -1054628, -1101232], ![323678, 651215, -400975, -965365, -1008024], ![-38428, -77316, 47606, 114614, 119679]]]
  hmulB := by decide  
  f := ![![![-3329, -4849, -495, 1784, 2872]], ![![-2739, -3990, -405, 1466, 2368]], ![![-2707, -3909, -404, 1440, 2280]], ![![-1776, -2627, -259, 961, 1600]], ![![-3142, -4552, -470, 1678, 2671]]]
  g := ![![![32573, 16879, -10393, -25022, -26128], ![211465, 109583, -67474, -162446, -169624], ![1372871, 711430, -438051, -1054628, -1101232], ![1256672, 651215, -400975, -965365, -1008024], ![-149200, -77316, 47606, 114614, 119679]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N3 : Nat.card (O ⧸ I43N3) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N3)

lemma isPrimeI43N3 : Ideal.IsPrime I43N3 := prime_ideal_of_norm_prime hp43.out _ NI43N3
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![-209423, -302926, -29898, 110354, 179309]] ![![9, 4, -2, 2, 6]]
  ![![-1059, -7028, 438, 1904, 9875]] where
 M := ![![![-1059, -7028, 438, 1904, 9875]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![-1059, -7028, 438, 1904, 9875]] ![![-39, 5, 3, -4, -9]]
  ![![3329, 4849, 495, -1784, -2872]] where
 M := ![![![3329, 4849, 495, -1784, -2872]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI43N2 : IdealMulLeCertificate' Table 
  ![![3329, 4849, 495, -1784, -2872]] ![![8389, 16879, -10393, -25022, -26128]]
  ![![43, 0, 0, 0, 0]] where
 M := ![![![-43, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1, I43N2, I43N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
    exact isPrimeI43N2
    exact isPrimeI43N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0 ⊙ MulI43N1 ⊙ MulI43N2)
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


def P47P0 : CertificateIrreducibleZModOfList' 47 5 2 5 [11, 44, 15, 38, 31, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 12, 33, 26, 13], [30, 12, 15, 3, 6], [33, 0, 12, 42, 40], [26, 22, 34, 23, 35], [0, 1]]
 g := ![![[28, 42, 42, 27, 12], [45, 28, 2, 35, 7], [34, 19, 45, 13, 21], [1], []], ![[4, 26, 41, 6, 33, 25, 35, 11], [8, 28, 3, 0, 31, 25, 3, 30], [22, 19, 26, 8, 38, 43, 32, 19], [43, 1, 33, 26, 38, 17, 19, 30], [31, 30, 43, 28]], ![[33, 45, 17, 8, 31, 37, 25, 42], [28, 42, 11, 14, 32, 12, 32, 9], [27, 29, 1, 10, 43, 12, 11, 1], [2, 2, 46, 31, 5, 41, 20, 25], [36, 12, 1, 36]], ![[20, 27, 25, 40, 41, 20, 3, 43], [4, 1, 6, 44, 22, 6, 46, 41], [25, 35, 8, 35, 15, 4, 39, 31], [23, 43, 23, 43, 12, 4, 44, 22], [17, 3, 8, 2]], ![[12, 31, 34, 35, 41, 17, 33, 33], [24, 23, 40, 11, 19, 33, 33, 19], [22, 0, 17, 10, 27, 34, 42, 29], [1, 38, 9, 43, 11, 14, 11, 29], [41, 42, 13, 3]]]
 h' := ![![[21, 12, 33, 26, 13], [22, 19, 7, 23, 24], [2, 14, 20, 23, 30], [36, 3, 32, 9, 16], [0, 0, 1], [0, 1]], ![[30, 12, 15, 3, 6], [33, 43, 31, 32, 15], [14, 39, 10, 38, 27], [1, 13, 7, 28, 9], [6, 32, 24, 30, 20], [21, 12, 33, 26, 13]], ![[33, 0, 12, 42, 40], [19, 1, 17, 30, 30], [5, 7, 8, 18, 42], [19, 8, 45, 32, 14], [34, 38, 12, 9, 24], [30, 12, 15, 3, 6]], ![[26, 22, 34, 23, 35], [43, 17, 45, 11, 22], [27, 43, 21, 31, 16], [23, 42, 25, 21, 3], [9, 18, 35, 15, 8], [33, 0, 12, 42, 40]], ![[0, 1], [38, 14, 41, 45, 3], [33, 38, 35, 31, 26], [4, 28, 32, 4, 5], [37, 6, 22, 40, 42], [26, 22, 34, 23, 35]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 6, 39, 31], [], [], []]
 b := ![[], [36, 39, 8, 11, 41], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 5
  hpos := by decide
  P := [11, 44, 15, 38, 31, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-20678448909748297, 7746663563477050, -12053628915794344, -7197678673726624, -48866954998908630]
  a := ![-26, 45, -55, -58, -169]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-439966998079751, 164822629010150, -256460189697752, -153142099440992, -1039722446785290]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![705793, 1420004, -874344, -2105022, -2198042]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![705793, 1420004, -874344, -2105022, -2198042]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![16, 44, 9, 1, 0], ![20, 49, 1, 0, 1]] where
  M :=![![![705793, 1420004, -874344, -2105022, -2198042], ![4582124, 9218901, -5676386, -13666152, -14270054], ![29747912, 59850634, -36852039, -88722924, -92643554], ![27230076, 54784934, -33732918, -81213501, -84802294], ![-3232916, -6504392, 4004972, 9642148, 10068231]]]
  hmulB := by decide  
  f := ![![![-411, -216, 28, 10, -54]], ![![236, -387, -94, 208, 390]], ![![-1144, -778, -39, 268, 546]], ![![-124, -524, -77, 223, 400]], ![![52, -449, -77, 200, 351]]]
  g := ![![![1478245, 3806510, 382432, -2105022, -2198042], ![9597012, 24712495, 2482812, -13666152, -14270054], ![62305392, 160437612, 16118827, -88722924, -92643554], ![57031924, 146858328, 14754545, -81213501, -84802294], ![-6771168, -17435891, -1751747, 9642148, 10068231]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [22, 23, 27, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [48, 35, 30], [31, 17, 23], [0, 1]]
 g := ![![[46, 27, 38], [52, 13], [27, 43, 40], [3, 40], [1]], ![[38, 11, 47, 23], [35, 7], [45, 49, 23, 31], [11, 24], [51, 18, 16, 23]], ![[6, 14, 17, 32], [36, 44], [30, 35, 37, 8], [13, 47], [28, 5, 40, 30]]]
 h' := ![![[48, 35, 30], [37, 29, 41], [42, 6, 38], [47, 10, 27], [31, 30, 26], [0, 1]], ![[31, 17, 23], [9, 46, 30], [39, 19, 31], [12, 26, 17], [25, 49, 17], [48, 35, 30]], ![[0, 1], [43, 31, 35], [26, 28, 37], [21, 17, 9], [25, 27, 10], [31, 17, 23]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19, 30], []]
 b := ![[], [41, 0, 52], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [22, 23, 27, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-76738472, 563697518, -453107469, -773320232, -1409169118]
  a := ![-22, 31, -46, -58, -131]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![763769200, 1955454236, 149357429, -773320232, -1409169118]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 148877 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![25, 50, -32, -76, -79]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![25, 50, -32, -76, -79]] 
 ![![53, 0, 0, 0, 0], ![16, 1, 0, 0, 0], ![9, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![26, 0, 0, 0, 1]] where
  M :=![![![25, 50, -32, -76, -79], ![164, 332, -207, -496, -517], ![1076, 2169, -1342, -3226, -3367], ![990, 1992, -1228, -2955, -3085], ![-116, -234, 146, 350, 365]]]
  hmulB := by decide  
  f := ![![![165, -30, 20, -6, 127]], ![![40, -8, 3, 0, 25]], ![![85, -7, 22, -12, 110]], ![![-69, 0, -22, 13, -108]], ![![122, -14, 22, -10, 125]]]
  g := ![![![31, 50, -32, -76, -79], ![201, 332, -207, -496, -517], ![1306, 2169, -1342, -3226, -3367], ![1195, 1992, -1228, -2955, -3085], ![-142, -234, 146, 350, 365]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1

def I53N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5575, -1529, 917, -988, -3258]] i)))

def SI53N2: IdealEqSpanCertificate' Table ![![-5575, -1529, 917, -988, -3258]] 
 ![![53, 0, 0, 0, 0], ![37, 1, 0, 0, 0], ![9, 0, 1, 0, 0], ![49, 0, 0, 1, 0], ![51, 0, 0, 0, 1]] where
  M :=![![![-5575, -1529, 917, -988, -3258], ![11056, 647, -1306, 1550, 4434], ![-14636, 1972, 1107, -1636, -3570], ![4274, -1355, -167, 289, 298], ![7096, 470, -848, 1014, 2907]]]
  hmulB := by decide  
  f := ![![![117789, -3007, 35425, -19626, 182114]], ![![67745, -2202, 20425, -11172, 105512]], ![![111557, -959, 33348, -19050, 169396]], ![![-3913, -2666, -880, 1329, -1536]], ![![176319, -2909, 52857, -29768, 270009]]]
  g := ![![![4855, -1529, 917, -988, -3258], ![-5721, 647, -1306, 1550, 4434], ![3107, 1972, 1107, -1636, -3570], ![501, -1355, -167, 289, 298], ![-3785, 470, -848, 1014, 2907]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N2 : Nat.card (O ⧸ I53N2) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N2)

lemma isPrimeI53N2 : Ideal.IsPrime I53N2 := prime_ideal_of_norm_prime hp53.out _ NI53N2
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![705793, 1420004, -874344, -2105022, -2198042]] ![![25, 50, -32, -76, -79]]
  ![![-2519267571, -5068583154, 3120896328, 7513696802, 7845724073]] where
 M := ![![![-2519267571, -5068583154, 3120896328, 7513696802, 7845724073]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI53N1 : IdealMulLeCertificate' Table 
  ![![-2519267571, -5068583154, 3120896328, 7513696802, 7845724073]] ![![-5575, -1529, 917, -988, -3258]]
  ![![53, 0, 0, 0, 0]] where
 M := ![![![116020854849, 233425521837, -143727908225, -346031335360, -361322322271]]]
 hmul := by decide  
 g := ![![![![2189072733, 4404255129, -2711847325, -6528893120, -6817402307]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0, 0, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0, 0, 0]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![0, 0, 0, 0, 59]] where
  M :=![![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![0, 0, 0, 0, 59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 5 2 5 [30, 55, 42, 31, 24, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [25, 18, 44, 10, 21], [46, 4, 40, 4, 40], [54, 55, 14, 42, 14], [28, 40, 20, 3, 43], [0, 1]]
 g := ![![[9, 33, 14, 49, 53], [17, 45, 39, 57, 49], [3, 19, 32, 26], [14, 35, 1], []], ![[39, 52, 16, 28, 26, 3, 15, 15], [28, 35, 32, 18, 45, 23, 5, 25], [42, 18, 48, 41], [53, 24, 2, 35, 25, 58, 11, 3], [39, 4, 35, 14, 58, 15, 3, 57]], ![[24, 33, 30, 12, 46, 21, 4, 56], [28, 39, 0, 25, 36, 33, 20, 58], [15, 58, 53, 12], [48, 10, 32, 43, 21, 39, 25, 10], [6, 7, 7, 57, 31, 3, 31, 44]], ![[19, 28, 26, 53, 16, 18, 56, 13], [10, 21, 3, 47, 21, 57, 6, 42], [22, 31, 42, 21], [43, 53, 33, 54, 53, 36, 37, 54], [49, 42, 36, 45, 5, 32, 22, 30]], ![[24, 1, 21, 18, 13, 27, 56, 2], [11, 54, 33, 53, 24, 53, 21, 44], [40, 56, 13, 26], [37, 50, 22, 1, 36, 2, 14, 44], [42, 20, 33, 42, 43, 51, 13, 34]]]
 h' := ![![[25, 18, 44, 10, 21], [21, 45, 45, 51, 17], [18, 24, 40, 51, 52], [52, 9, 53, 47, 12], [0, 0, 0, 1], [0, 1]], ![[46, 4, 40, 4, 40], [46, 41, 3, 13, 47], [47, 2, 21, 58, 2], [3, 23, 44, 31, 49], [0, 38, 52, 7, 28], [25, 18, 44, 10, 21]], ![[54, 55, 14, 42, 14], [2, 49, 20, 37, 54], [47, 0, 0, 21, 38], [54, 9, 4, 7, 37], [42, 13, 47, 17, 29], [46, 4, 40, 4, 40]], ![[28, 40, 20, 3, 43], [50, 44, 33, 20, 50], [15, 0, 38, 27, 48], [47, 19, 53, 3, 32], [57, 52, 23, 41, 39], [54, 55, 14, 42, 14]], ![[0, 1], [13, 57, 17, 56, 9], [26, 33, 19, 20, 37], [20, 58, 23, 30, 47], [42, 15, 55, 52, 22], [28, 40, 20, 3, 43]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44, 40, 19, 34], [], [], []]
 b := ![[], [44, 7, 21, 37, 4], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 5
  hpos := by decide
  P := [30, 55, 42, 31, 24, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![12895402962796495, -38019942596933828, 32850879947435635, 50805720565137002, 106647589015012011]
  a := ![33, -48, 69, 80, 195]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![218566151911805, -644405806727692, 556794575380265, 861113907883678, 1807586254491729]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8827, -3628, 3020, -638, 19200]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![8827, -3628, 3020, -638, 19200]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![50, 6, 2, 10, 1]] where
  M :=![![![8827, -3628, 3020, -638, 19200], ![-78076, -8459, -22360, 15568, -103656], ![445760, -21124, 135109, -71888, 705096], ![-568320, -3758, -168962, 99165, -848872], ![319348, 5372, 94592, -56520, 471673]]]
  hmulB := by decide  
  f := ![![![-153, -480, 288, 730, 784]], ![![-1676, -3127, 1944, 4648, 4840]], ![![-10064, -20460, 12569, 30256, 31576]], ![![-9288, -18658, 11498, 27697, 28936]], ![![-2126, -4394, 2702, 6534, 6841]]]
  g := ![![![-15593, -1948, -580, -3158, 19200], ![83684, 10057, 3032, 17248, -103656], ![-570640, -69700, -20903, -116768, 705096], ![686480, 83434, 25062, 140785, -848872], ![-381382, -46306, -13914, -78250, 471673]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 4 2 5 [57, 55, 21, 57, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 33, 28, 24], [19, 54, 49, 43], [35, 34, 45, 55], [0, 1]]
 g := ![![[18, 47, 24, 19], [47, 6, 39], [40, 21, 31, 42], [24, 56, 4, 1], []], ![[43, 57, 36, 15, 35, 30], [16, 8, 34], [41, 46, 7, 2, 50, 7], [25, 57, 1, 20, 16, 38], [25, 45, 34, 49, 41, 38]], ![[60, 59, 60, 9, 16, 21], [10, 33, 16], [0, 38, 56, 35, 21, 8], [40, 47, 14, 15, 6, 17], [53, 37, 9, 10, 22, 24]], ![[8, 29, 50, 54, 5, 43], [27, 25, 5], [0, 48, 2, 55, 4, 51], [25, 43, 44, 54, 59, 17], [30, 54, 9, 3, 31, 28]]]
 h' := ![![[11, 33, 28, 24], [46, 56, 46, 18], [38, 24, 38, 51], [35, 2, 31, 46], [0, 0, 0, 1], [0, 1]], ![[19, 54, 49, 43], [6, 21, 26, 48], [53, 41, 52, 41], [1, 3, 24, 14], [28, 48, 49, 24], [11, 33, 28, 24]], ![[35, 34, 45, 55], [13, 12, 29, 3], [41, 35, 19, 4], [25, 38, 49, 13], [56, 22, 44, 4], [19, 54, 49, 43]], ![[0, 1], [52, 33, 21, 53], [35, 22, 13, 26], [1, 18, 18, 49], [51, 52, 29, 32], [35, 34, 45, 55]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [37, 27, 60], []]
 b := ![[], [], [56, 57, 30, 44], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 4
  hpos := by decide
  P := [57, 55, 21, 57, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1181594643905, -4326246764758, 3653219192282, 5831074348646, 11705719238326]
  a := ![28, -41, 58, 70, 167]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-9575481430695, -1222304298274, -323905234170, -1823378984174, 11705719238326]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 13845841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![153, 480, -288, -730, -784]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![153, 480, -288, -730, -784]] 
 ![![61, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![12, 0, 1, 0, 0], ![45, 0, 0, 1, 0], ![38, 0, 0, 0, 1]] where
  M :=![![![153, 480, -288, -730, -784], ![1676, 3127, -1944, -4648, -4840], ![10064, 20460, -12569, -30256, -31576], ![9288, 18658, -11498, -27697, -28936], ![-1028, -2228, 1360, 3296, 3451]]]
  hmulB := by decide  
  f := ![![![-8827, 3628, -3020, 638, -19200]], ![![267, 555, 20, -182, -504]], ![![-9044, 1060, -2809, 1304, -15336]], ![![2805, 2738, 542, -1155, -248]], ![![-10734, 2172, -3432, 1324, -19693]]]
  g := ![![![1031, 480, -288, -730, -784], ![6495, 3127, -1944, -4648, -4840], ![42280, 20460, -12569, -30256, -31576], ![38731, 18658, -11498, -27697, -28936], ![-4610, -2228, 1360, 3296, 3451]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![8827, -3628, 3020, -638, 19200]] ![![153, 480, -288, -730, -784]]
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


lemma PB2088I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB2088I1 : PrimesBelowBoundCertificateInterval O 23 61 2088 where
  m := 9
  g := ![2, 2, 3, 1, 4, 1, 3, 1, 2]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB2088I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0, I29N1]
    · exact ![I31N0, I31N1]
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0]
    · exact ![I43N0, I43N1, I43N2, I43N3]
    · exact ![I47N0]
    · exact ![I53N0, I53N1, I53N2]
    · exact ![I59N0]
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
    · exact ![24389, 841]
    · exact ![923521, 31]
    · exact ![50653, 37, 37]
    · exact ![115856201]
    · exact ![1849, 43, 43, 43]
    · exact ![229345007]
    · exact ![148877, 53, 53]
    · exact ![714924299]
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
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
      exact NI43N2
      exact NI43N3
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
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
  β := ![I29N1, I31N1, I37N1, I37N2, I43N0, I43N1, I43N2, I43N3, I53N1, I53N2, I61N1]
  Il := ![[I29N1], [I31N1], [I37N1, I37N2], [], [I43N0, I43N1, I43N2, I43N3], [], [I53N1, I53N2], [], [I61N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
