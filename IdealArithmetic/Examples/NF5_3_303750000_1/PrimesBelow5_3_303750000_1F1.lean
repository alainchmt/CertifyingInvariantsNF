
import IdealArithmetic.Examples.NF5_3_303750000_1.RI5_3_303750000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![81, -288, 730, -527, 639]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![81, -288, 730, -527, 639]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![0, 0, 0, 29, 0], ![23, 2, 5, 24, 1]] where
  M :=![![![81, -288, 730, -527, 639], ![-352, 1316, -3351, 2423, -2938], ![448, -1696, 4315, -3126, 3792], ![-1964, 7431, -18847, 13656, -16570], ![526, -1983, 5033, -3641, 4417]]]
  hmulB := by decide  
  f := ![![![11, 6, 6, 1, 1]], ![![16, 20, 23, 5, 10]], ![![8, 14, 13, 4, 12]], ![![84, 127, 107, 26, 78]], ![![83, 117, 100, 24, 70]]]
  g := ![![![-504, -54, -85, -547, 639], ![2318, 248, 391, 2515, -2938], ![-2992, -320, -505, -3246, 3792], ![13074, 1399, 2207, 14184, -16570], ![-3485, -373, -588, -3781, 4417]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 4 2 4 [15, 14, 16, 1, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [20, 8, 21, 17], [28, 18, 27, 15], [9, 2, 10, 26], [0, 1]]
 g := ![![[18, 13, 0, 6], [0, 28, 13], [17, 14, 28, 1], []], ![[19, 11, 11, 18, 8, 15], [24, 25, 22], [8, 23, 26, 26, 10, 8], [17, 19, 2, 20, 12, 12]], ![[0, 4, 28, 13, 15, 26], [4, 5, 22], [7, 23, 11, 8], [24, 27, 8, 1, 2, 11]], ![[15, 11, 20, 12, 3, 18], [17, 18, 5], [2, 23, 28, 12, 19, 17], [5, 9, 4, 14, 7, 2]]]
 h' := ![![[20, 8, 21, 17], [7, 4, 4, 8], [6, 16, 11, 19], [0, 0, 0, 1], [0, 1]], ![[28, 18, 27, 15], [22, 26, 12, 21], [18, 10, 11, 14], [2, 0, 23, 26], [20, 8, 21, 17]], ![[9, 2, 10, 26], [22, 16, 0, 20], [16, 20, 2, 14], [16, 9, 25], [28, 18, 27, 15]], ![[0, 1], [5, 12, 13, 9], [12, 12, 5, 11], [16, 20, 10, 2], [9, 2, 10, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [0, 12, 9], []]
 b := ![[], [], [28, 18, 2, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 4
  hpos := by decide
  P := [15, 14, 16, 1, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![346195857031, 418604564065, 530771309229, 20191527445, 365108621212]
  a := ![-20, -41, -39, 24, -100]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-277631118305, -10745264771, -44647303339, -301462599367, 365108621212]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 707281 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 6, 6, 1, 1]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![11, 6, 6, 1, 1]] 
 ![![29, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![11, 0, 0, 1, 0], ![20, 0, 0, 0, 1]] where
  M :=![![![11, 6, 6, 1, 1], ![16, 20, 23, 5, 10], ![8, 14, 13, 4, 12], ![84, 127, 107, 26, 78], ![66, 97, 83, 19, 55]]]
  hmulB := by decide  
  f := ![![![81, -288, 730, -527, 639]], ![![13, -44, 111, -80, 97]], ![![35, -128, 325, -235, 285]], ![![-37, 147, -373, 271, -329]], ![![74, -267, 677, -489, 593]]]
  g := ![![![-4, 6, 6, 1, 1], ![-20, 20, 23, 5, 10], ![-17, 14, 13, 4, 12], ![-126, 127, 107, 26, 78], ![-93, 97, 83, 19, 55]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![81, -288, 730, -527, 639]] ![![11, 6, 6, 1, 1]]
  ![![29, 0, 0, 0, 0]] where
 M := ![![![29, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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


def P31P0 : CertificateIrreducibleZModOfList' 31 5 2 4 [15, 6, 25, 30, 9, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [29, 27, 11, 21, 8], [24, 7, 28, 10, 19], [14, 17, 10, 21, 18], [17, 10, 13, 10, 17], [0, 1]]
 g := ![![[27, 30, 26, 4, 1], [18, 4, 27, 20, 9], [20, 22, 1], []], ![[4, 29, 13, 23, 3, 12, 12, 19], [8, 26, 21, 26, 30, 27, 1, 1], [17, 15, 8, 12, 19, 14, 11, 5], [23, 24, 0, 14, 17, 9, 13, 16]], ![[2, 1, 15, 9, 21, 10, 22, 20], [8, 9, 29, 30, 18, 18], [15, 20, 4, 23, 12, 11, 24, 14], [1, 18, 26, 3, 24, 1, 1, 8]], ![[6, 24, 16, 6, 4, 13, 19, 19], [19, 0, 23, 15, 9, 19, 19, 19], [1, 22, 24, 29, 17, 5, 24, 4], [3, 8, 18, 23, 4, 8, 9, 4]], ![[4, 24, 22, 16, 6, 8, 23, 11], [20, 3, 16, 15, 15, 24, 16, 21], [11, 21, 21, 25, 9, 6, 27, 24], [5, 7, 4, 24, 25, 21, 10, 15]]]
 h' := ![![[29, 27, 11, 21, 8], [9, 25, 10, 9, 30], [10, 15, 4, 22, 3], [0, 0, 0, 1], [0, 1]], ![[24, 7, 28, 10, 19], [19, 23, 7, 29, 18], [15, 14, 29, 12, 29], [19, 12, 30, 22, 12], [29, 27, 11, 21, 8]], ![[14, 17, 10, 21, 18], [10, 10, 1, 19, 22], [15, 24, 20, 18], [14, 9, 22, 30, 2], [24, 7, 28, 10, 19]], ![[17, 10, 13, 10, 17], [30, 16, 13, 22, 12], [10, 11, 10, 22, 12], [2, 0, 17, 15, 13], [14, 17, 10, 21, 18]], ![[0, 1], [3, 19, 0, 14, 11], [27, 29, 30, 19, 18], [2, 10, 24, 25, 4], [17, 10, 13, 10, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30, 22, 0, 21], [], [], []]
 b := ![[], [23, 27, 4, 7, 9], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 5
  hpos := by decide
  P := [15, 6, 25, 30, 9, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3006588943439202, -3763741569589970, -4398620138820341, -359953324215602, -2974024207787447]
  a := ![-37, -75, -76, 33, -127]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-96986740110942, -121411018373870, -141890972220011, -11611397555342, -95936264767337]
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

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1411, 69, 331, 60, -223]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![1411, 69, 331, 60, -223]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![29, 15, 31, 1, 0], ![33, 17, 12, 0, 1]] where
  M :=![![![1411, 69, 331, 60, -223], ![-188, -9, -38, -12, 34], ![-652, -30, -159, -22, 96], ![-752, -52, -150, -53, 146], ![-134, -4, -42, 0, 15]]]
  hmulB := by decide  
  f := ![![![5, 7, 5, 2, 7]], ![![32, 55, 38, 8, 30]], ![![36, 46, 49, 10, 20]], ![![53, 74, 68, 15, 39]], ![![35, 52, 43, 10, 30]]]
  g := ![![![190, 80, 31, 60, -223], ![-26, -11, -2, -12, 34], ![-86, -36, -17, -22, 96], ![-109, -47, -7, -53, 146], ![-17, -7, -6, 0, 15]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [23, 19, 14, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 11, 36], [10, 25, 1], [0, 1]]
 g := ![![[30, 10, 7], [6, 7], [36, 26, 27], [23, 1], []], ![[16, 31, 33, 28], [34, 10], [30, 35, 26, 36], [9, 33], [1, 1]], ![[15, 23, 10, 36], [34, 4], [36, 33, 30, 12], [5, 10], [36, 1]]]
 h' := ![![[13, 11, 36], [21, 6, 9], [23, 23, 28], [26, 21, 29], [0, 0, 1], [0, 1]], ![[10, 25, 1], [7, 5, 34], [7, 18, 11], [19, 18, 1], [35, 22, 25], [13, 11, 36]], ![[0, 1], [4, 26, 31], [34, 33, 35], [29, 35, 7], [12, 15, 11], [10, 25, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 22], []]
 b := ![[], [8, 20, 22], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [23, 19, 14, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2835985, -3298400, -4581564, 44602, -3224998]
  a := ![-5, -11, -10, 6, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2764743, 1374528, 884750, 44602, -3224998]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 50653 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, -7, -5, -2, -7]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-5, -7, -5, -2, -7]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![26, 11, 1, 0, 0], ![14, 7, 0, 1, 0], ![31, 7, 0, 0, 1]] where
  M :=![![![-5, -7, -5, -2, -7], ![-32, -55, -38, -8, -30], ![-36, -46, -49, -10, -20], ![-220, -284, -282, -67, -170], ![-154, -206, -192, -48, -129]]]
  hmulB := by decide  
  f := ![![![-1411, -69, -331, -60, 223]], ![![188, 9, 38, 12, -34]], ![![-918, -45, -217, -38, 144]], ![![-478, -23, -114, -19, 74]], ![![-1143, -56, -269, -48, 180]]]
  g := ![![![10, 3, -5, -2, -7], ![54, 17, -38, -8, -30], ![54, 19, -49, -10, -20], ![360, 121, -282, -67, -170], ![257, 85, -192, -48, -129]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P1 : CertificateIrreducibleZModOfList' 37 2 2 5 [33, 28, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 36], [0, 1]]
 g := ![![[30, 9], [10], [7, 21], [7], [1]], ![[0, 28], [10], [11, 16], [7], [1]]]
 h' := ![![[9, 36], [10, 3], [28, 11], [7, 24], [4, 9], [0, 1]], ![[0, 1], [0, 34], [16, 26], [1, 13], [11, 28], [9, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32]]
 b := ![[], [2, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N1 : CertifiedPrimeIdeal' SI37N1 37 where
  n := 2
  hpos := by decide
  P := [33, 28, 1]
  hirr := P37P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![425383, 473515, 764002, -89775, 609424]
  a := ![46, 95, 92, -54, 215]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1001999, -312650, 764002, -89775, 609424]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N1 B_one_repr
lemma NI37N1 : Nat.card (O ⧸ I37N1) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![1411, 69, 331, 60, -223]] ![![-5, -7, -5, -2, -7]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-21, -1400, 78, 253, -47]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![-21, -1400, 78, 253, -47]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![24, 1, 28, 33, 1]] where
  M :=![![![-21, -1400, 78, 253, -47], ![-2388, -1022, -4713, -475, 1930], ![824, 3820, 1303, -466, -444], ![4256, 2077, 8259, 850, -3130], ![1502, -2927, 3201, 989, -1205]]]
  hmulB := by decide  
  f := ![![![-104043, -5038, -24546, -4371, 16387]], ![![13956, 674, 3297, 583, -2194]], ![![48064, 2330, 11333, 2024, -7576]], ![![55576, 2681, 13137, 2316, -8730]], ![![17230, 828, 4081, 712, -2699]]]
  g := ![![![27, -33, 34, 44, -47], ![-1188, -72, -1433, -1565, 1930], ![280, 104, 335, 346, -444], ![1936, 127, 2339, 2540, -3130], ![742, -42, 901, 994, -1205]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 4 2 5 [22, 8, 36, 38, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 4, 15, 30], [4, 16, 31, 36], [2, 20, 36, 16], [0, 1]]
 g := ![![[2, 0, 35, 2], [29, 4, 39], [2, 5, 32], [3, 1], []], ![[10, 13, 26, 13, 37, 27], [22, 11, 40], [26, 4, 2], [21, 30, 18, 27, 28, 28], [21, 33, 39]], ![[33, 29, 18, 23, 14, 9], [4, 32, 9], [24, 2, 40], [0, 36, 8, 15, 1, 25], [16, 11, 25]], ![[17, 31, 35, 39, 35, 25], [33, 18, 37], [0, 24, 36], [21, 11, 11, 13, 11, 20], [38, 34, 10]]]
 h' := ![![[38, 4, 15, 30], [26, 22, 10, 24], [7, 1, 7, 30], [16, 36, 7, 14], [0, 0, 1], [0, 1]], ![[4, 16, 31, 36], [12, 38, 37, 28], [39, 9, 22, 32], [18, 21, 29, 24], [39, 25, 16, 20], [38, 4, 15, 30]], ![[2, 20, 36, 16], [31, 30, 39, 21], [23, 22, 6, 38], [10, 17, 39, 9], [33, 4, 28, 35], [4, 16, 31, 36]], ![[0, 1], [8, 33, 37, 9], [18, 9, 6, 23], [31, 8, 7, 35], [29, 12, 37, 27], [2, 20, 36, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [19, 34, 14], []]
 b := ![[], [], [29, 25, 1, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 4
  hpos := by decide
  P := [22, 8, 36, 38, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1396404440807, 1625426375331, 2243231897258, -7563533476, 1566211563426]
  a := ![-27, -60, -55, 38, -147]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-882748123937, 1444263705, -1014894923870, -1260793783574, 1566211563426]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 2825761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![104043, 5038, 24546, 4371, -16387]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![104043, 5038, 24546, 4371, -16387]] 
 ![![41, 0, 0, 0, 0], ![21, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![25, 0, 0, 1, 0], ![11, 0, 0, 0, 1]] where
  M :=![![![104043, 5038, 24546, 4371, -16387], ![-13956, -674, -3297, -583, 2194], ![-48064, -2330, -11333, -2024, 7576], ![-55576, -2681, -13137, -2316, 8730], ![-9706, -473, -2283, -413, 1535]]]
  hmulB := by decide  
  f := ![![![21, 1400, -78, -253, 47]], ![![69, 742, 75, -118, -23]], ![![-16, 180, -47, -38, 20]], ![![-91, 803, -249, -175, 105]], ![![-31, 447, -99, -92, 42]]]
  g := ![![![-3101, 5038, 24546, 4371, -16387], ![415, -674, -3297, -583, 2194], ![1434, -2330, -11333, -2024, 7576], ![1651, -2681, -13137, -2316, 8730], ![291, -473, -2283, -413, 1535]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![-21, -1400, 78, 253, -47]] ![![104043, 5038, 24546, 4371, -16387]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13, -37, -27, -7, -26]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![-13, -37, -27, -7, -26]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![22, 13, 6, 35, 1]] where
  M :=![![![-13, -37, -27, -7, -26], ![-140, -200, -175, -39, -108], ![-132, -164, -165, -38, -92], ![-860, -1161, -1075, -258, -688], ![-620, -855, -775, -185, -509]]]
  hmulB := by decide  
  f := ![![![5, 1, 1, 1, -2]], ![![0, -4, 5, -3, 4]], ![![-4, 2, -9, 4, -4]], ![![0, -7, 25, -20, 24]], ![![2, -6, 21, -16, 19]]]
  g := ![![![13, 7, 3, 21, -26], ![52, 28, 11, 87, -108], ![44, 24, 9, 74, -92], ![332, 181, 71, 554, -688], ![246, 134, 53, 410, -509]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 4 2 5 [7, 35, 12, 38, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 18, 20, 1], [31, 39, 25, 4], [14, 28, 41, 38], [0, 1]]
 g := ![![[18, 14, 25, 6], [14, 22, 18, 17], [31, 9, 40], [5, 1], []], ![[39, 16, 15, 2, 16, 4], [11, 34, 27, 0, 14, 17], [17, 2, 38], [35, 1, 3, 34, 32, 1], [4, 2, 1]], ![[40, 35, 17, 42, 0, 35], [12, 31, 29, 40, 24, 25], [31, 9, 40], [40, 34, 19, 13, 26, 35], [38, 22, 16]], ![[30, 9, 25, 5, 42, 13], [8, 28, 37, 29, 5, 1], [17, 2, 38], [40, 30, 39, 23, 4, 36], [20, 16, 25]]]
 h' := ![![[3, 18, 20, 1], [31, 18, 15, 7], [19, 25, 21, 24], [8, 33, 34, 13], [0, 0, 1], [0, 1]], ![[31, 39, 25, 4], [42, 37, 22, 2], [21, 18, 22, 19], [21, 18, 20, 34], [24, 40, 18, 42], [3, 18, 20, 1]], ![[14, 28, 41, 38], [13, 21, 4, 27], [19, 25, 21, 24], [35, 10, 9, 30], [7, 31, 13, 16], [31, 39, 25, 4]], ![[0, 1], [12, 10, 2, 7], [21, 18, 22, 19], [22, 25, 23, 9], [13, 15, 11, 28], [14, 28, 41, 38]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [11, 20, 31], []]
 b := ![[], [], [35, 22, 15, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 4
  hpos := by decide
  P := [7, 35, 12, 38, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1066663613, -2671200768, 8022157418, -5483751926, 6946170080]
  a := ![2, 16, 14, -18, 32]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3529048329, -2162125856, -782671234, -5781388482, 6946170080]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 3418801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, -1, -1, -1, 2]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-5, -1, -1, -1, 2]] 
 ![![43, 0, 0, 0, 0], ![19, 1, 0, 0, 0], ![13, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![35, 0, 0, 0, 1]] where
  M :=![![![-5, -1, -1, -1, 2], ![0, 4, -5, 3, -4], ![4, -2, 9, -4, 4], ![0, 7, -25, 20, -24], ![0, -5, 5, -5, 7]]]
  hmulB := by decide  
  f := ![![![13, 37, 27, 7, 26]], ![![9, 21, 16, 4, 14]], ![![7, 15, 12, 3, 10]], ![![20, 27, 25, 6, 16]], ![![25, 50, 40, 10, 33]]]
  g := ![![![-1, -1, -1, -1, 2], ![3, 4, -5, 3, -4], ![-5, -2, 9, -4, 4], ![24, 7, -25, 20, -24], ![-5, -5, 5, -5, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![-13, -37, -27, -7, -26]] ![![-5, -1, -1, -1, 2]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-245, -385, -457, 2, 179]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-245, -385, -457, 2, 179]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![20, 11, 25, 1, 0], ![16, 40, 25, 0, 1]] where
  M :=![![![-245, -385, -457, 2, 179], ![-408, 907, -896, -282, 374], ![724, 664, 1395, 80, -560], ![684, -1556, 1520, 473, -666], ![-414, -1586, -682, 172, 235]]]
  hmulB := by decide  
  f := ![![![-7393, -361, -1737, -316, 1171]], ![![988, 61, 200, 66, -186]], ![![3420, 148, 849, 112, -500]], ![![-1012, -55, -225, -53, 172]], ![![158, 8, 35, 8, -27]]]
  g := ![![![-67, -161, -106, 2, 179], ![-16, -233, -68, -282, 374], ![172, 472, 285, 80, -560], ![40, 423, 135, 473, -666], ![-162, -274, -231, 172, 235]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [40, 35, 8, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [32, 30, 40], [7, 16, 7], [0, 1]]
 g := ![![[18, 27, 12], [20, 32, 36], [23, 24, 17], [29, 39, 1], []], ![[0, 17, 17, 33], [21, 24, 26, 11], [6, 39, 6, 46], [24, 36, 26, 41], [34, 2]], ![[45, 18, 8, 2], [14, 16, 0, 4], [7, 36, 1, 36], [19, 8, 25, 2], [20, 2]]]
 h' := ![![[32, 30, 40], [46, 18, 23], [20, 11, 6], [15, 10, 8], [0, 0, 1], [0, 1]], ![[7, 16, 7], [38, 27, 7], [1, 0, 19], [44, 1, 11], [40, 39, 16], [32, 30, 40]], ![[0, 1], [7, 2, 17], [9, 36, 22], [46, 36, 28], [1, 8, 30], [7, 16, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21, 36], []]
 b := ![[], [34, 29, 32], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [40, 35, 8, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3399045470, 4109178167, 5226138365, 177241628, 3632449053]
  a := ![60, 102, 106, -52, 251]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1239680254, -3045498763, -1915236780, 177241628, 3632449053]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 103823 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-91, -5, -23, -4, 15]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-91, -5, -23, -4, 15]] 
 ![![47, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![20, 0, 1, 0, 0], ![18, 0, 0, 1, 0], ![39, 0, 0, 0, 1]] where
  M :=![![![-91, -5, -23, -4, 15], ![12, 5, 2, 0, -2], ![44, 2, 15, 2, -8], ![48, -4, 10, 5, -10], ![6, -4, -2, 0, 1]]]
  hmulB := by decide  
  f := ![![![169, 235, 213, 50, 139]], ![![54, 75, 68, 16, 44]], ![![88, 122, 111, 26, 72]], ![![178, 246, 224, 53, 144]], ![![223, 309, 281, 66, 182]]]
  g := ![![![-2, -5, -23, -4, 15], ![0, 5, 2, 0, -2], ![0, 2, 15, 2, -8], ![4, -4, 10, 5, -10], ![1, -4, -2, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1

def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-87, 6, -16, 0, 18]] i)))

def SI47N2: IdealEqSpanCertificate' Table ![![-87, 6, -16, 0, 18]] 
 ![![47, 0, 0, 0, 0], ![12, 1, 0, 0, 0], ![32, 0, 1, 0, 0], ![36, 0, 0, 1, 0], ![17, 0, 0, 0, 1]] where
  M :=![![![-87, 6, -16, 0, 18], ![48, 43, 58, 2, 36], ![72, 50, 33, 22, 4], ![272, 272, 350, 17, 224], ![164, 224, 182, 60, 109]]]
  hmulB := by decide  
  f := ![![![1263, 2338, 2328, -76, -910]], ![![380, 503, 718, 14, -284]], ![![776, 1498, 1425, -58, -556]], ![![868, 1948, 1570, -115, -608]], ![![493, 1034, 898, -52, -349]]]
  g := ![![![1, 6, -16, 0, 18], ![-64, 43, 58, 2, 36], ![-52, 50, 33, 22, 4], ![-396, 272, 350, 17, 224], ![-263, 224, 182, 60, 109]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N2 : Nat.card (O ⧸ I47N2) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N2)

lemma isPrimeI47N2 : Ideal.IsPrime I47N2 := prime_ideal_of_norm_prime hp47.out _ NI47N2
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-245, -385, -457, 2, 179]] ![![-91, -5, -23, -4, 15]]
  ![![-1263, -2338, -2328, 76, 910]] where
 M := ![![![-1263, -2338, -2328, 76, 910]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![-1263, -2338, -2328, 76, 910]] ![![-87, 6, -16, 0, 18]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0, 0, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0, 0, 0]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![0, 0, 0, 0, 53]] where
  M :=![![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![0, 0, 0, 0, 53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 5 2 5 [46, 6, 15, 6, 13, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 39, 4, 51, 20], [44, 33, 49, 13, 49], [25, 49, 48, 14, 19], [2, 37, 5, 28, 18], [0, 1]]
 g := ![![[41, 9, 5, 14, 28], [42, 46, 22, 29], [14, 6, 0, 31, 16], [40, 1], []], ![[32, 14, 2, 9, 50, 4, 5, 26], [13, 21, 1, 52], [19, 38, 6, 1, 47, 38, 3, 48], [17, 4, 42, 37], [1, 47, 4, 39, 41, 29, 24, 50]], ![[45, 1, 39, 44, 3, 32, 17, 16], [21, 10, 29, 49], [37, 2, 13, 30, 31, 39, 1, 42], [39, 29, 22, 47], [19, 9, 43, 30, 12, 12, 25, 42]], ![[30, 23, 48, 11, 11, 21, 24, 27], [30, 18, 50, 38], [39, 7, 20, 0, 45, 9, 49, 19], [52, 42, 24, 13], [23, 19, 21, 7, 13, 16, 36, 22]], ![[30, 21, 25, 21, 20, 43, 27, 18], [11, 43, 31, 11], [17, 25, 0, 41, 9, 34, 17, 50], [43, 13, 8, 28], [10, 49, 20, 2, 6, 1, 1, 2]]]
 h' := ![![[22, 39, 4, 51, 20], [40, 4, 7, 21, 9], [45, 24, 25, 6, 20], [15, 32, 30, 10, 4], [0, 0, 0, 1], [0, 1]], ![[44, 33, 49, 13, 49], [27, 24, 35, 40, 7], [25, 15, 47, 21, 30], [17, 42, 26, 52, 38], [2, 29, 31, 13, 14], [22, 39, 4, 51, 20]], ![[25, 49, 48, 14, 19], [37, 38, 49, 49, 7], [46, 16, 29, 40, 7], [18, 31, 15, 52, 49], [40, 18, 9, 29, 10], [44, 33, 49, 13, 49]], ![[2, 37, 5, 28, 18], [42, 26, 10, 1, 31], [37, 24, 41, 48, 41], [4, 17, 7, 40, 52], [45, 21, 46, 13, 38], [25, 49, 48, 14, 19]], ![[0, 1], [52, 14, 5, 48, 52], [44, 27, 17, 44, 8], [25, 37, 28, 5, 16], [25, 38, 20, 50, 44], [2, 37, 5, 28, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45, 30, 47, 22], [], [], []]
 b := ![[], [24, 4, 13, 32, 36], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 5
  hpos := by decide
  P := [46, 6, 15, 6, 13, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![741622216, -1070488117, 4316421442, -2720288229, 3688967374]
  a := ![0, 3, 2, -4, 9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![13992872, -20197889, 81441914, -51326193, 69603158]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 418195493 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def PBC53 : ContainsPrimesAboveP 53 ![I53N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![53, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 53 (by decide) 𝕀

instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5417, 268, 1264, 238, -866]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![5417, 268, 1264, 238, -866]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![4, 28, 1, 0, 0], ![25, 50, 0, 1, 0], ![35, 31, 0, 0, 1]] where
  M :=![![![5417, 268, 1264, 238, -866], ![-720, -61, -106, -78, 172], ![-2512, -88, -675, -44, 320], ![-2856, -286, -314, -389, 780], ![-516, 14, -218, 50, -7]]]
  hmulB := by decide  
  f := ![![![-149, -92, -288, -26, 110]], ![![-16, 629, -74, -126, 12]], ![![-12, 292, -43, -60, 8]], ![![-79, 472, -186, -115, 54]], ![![-105, 263, -224, -82, 75]]]
  g := ![![![419, -342, 1264, 238, -866], ![-74, 25, -106, -78, 172], ![-168, 188, -675, -44, 320], ![-325, 64, -314, -389, 780], ![-11, 65, -218, 50, -7]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [6, 14, 1] where
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
 g := ![![[22, 21], [17, 25], [45], [54, 51], [45, 1]], ![[23, 38], [21, 34], [45], [48, 8], [31, 58]]]
 h' := ![![[45, 58], [16, 32], [40, 54], [30, 35], [25, 13], [0, 1]], ![[0, 1], [40, 27], [51, 5], [12, 24], [20, 46], [45, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48]]
 b := ![[], [50, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [6, 14, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![416711, 453698, 764554, -102158, 613214]
  a := ![45, 91, 91, -56, 217]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-365255, -590772, 764554, -102158, 613214]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 3, -1, 0, 3]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![-1, 3, -1, 0, 3]] 
 ![![59, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![25, 0, 1, 0, 0], ![47, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![-1, 3, -1, 0, 3], ![12, 21, 16, 2, 6], ![12, 8, 17, 4, 4], ![56, 68, 68, 19, 50], ![38, 56, 44, 12, 39]]]
  hmulB := by decide  
  f := ![![![-25, -121, 283, -218, 271]], ![![-4, 1, -4, 2, -2]], ![![-7, -63, 150, -114, 141]], ![![-33, -45, 95, -79, 101]], ![![2, -22, 54, -40, 49]]]
  g := ![![![0, 3, -1, 0, 3], ![-10, 21, 16, 2, 6], ![-11, 8, 17, 4, 4], ![-51, 68, 68, 19, 50], ![-34, 56, 44, 12, 39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1645, -80, -388, -69, 259]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![-1645, -80, -388, -69, 259]] 
 ![![59, 0, 0, 0, 0], ![28, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![38, 0, 0, 1, 0], ![56, 0, 0, 0, 1]] where
  M :=![![![-1645, -80, -388, -69, 259], ![220, 10, 51, 9, -34], ![760, 38, 179, 32, -120], ![880, 43, 211, 36, -138], ![154, 7, 37, 7, -25]]]
  hmulB := by decide  
  f := ![![![143, 206, 180, 41, 111]], ![![80, 114, 101, 23, 62]], ![![20, 28, 25, 6, 16]], ![![166, 235, 209, 48, 132]], ![![190, 271, 239, 55, 149]]]
  g := ![![![-165, -80, -388, -69, 259], ![22, 10, 51, 9, -34], ![76, 38, 179, 32, -120], ![88, 43, 211, 36, -138], ![16, 7, 37, 7, -25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2

def I59N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-25, 4, -2, 0, 8]] i)))

def SI59N3: IdealEqSpanCertificate' Table ![![-25, 4, -2, 0, 8]] 
 ![![59, 0, 0, 0, 0], ![34, 1, 0, 0, 0], ![57, 0, 1, 0, 0], ![41, 0, 0, 1, 0], ![31, 0, 0, 0, 1]] where
  M :=![![![-25, 4, -2, 0, 8], ![24, 29, 26, 6, 16], ![32, 26, 27, 6, 12], ![144, 176, 166, 39, 100], ![96, 128, 118, 28, 75]]]
  hmulB := by decide  
  f := ![![![13, -80, 198, -156, 192]], ![![6, -39, 98, -78, 96]], ![![15, -86, 213, -166, 204]], ![![-1, -20, 44, -41, 52]], ![![9, -52, 128, -100, 123]]]
  g := ![![![-5, 4, -2, 0, 8], ![-54, 29, 26, 6, 16], ![-51, 26, 27, 6, 12], ![-339, 176, 166, 39, 100], ![-245, 128, 118, 28, 75]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N3 : Nat.card (O ⧸ I59N3) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N3)

lemma isPrimeI59N3 : Ideal.IsPrime I59N3 := prime_ideal_of_norm_prime hp59.out _ NI59N3
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![5417, 268, 1264, 238, -866]] ![![-1, 3, -1, 0, 3]]
  ![![-6613, -321, -1561, -278, 1041]] where
 M := ![![![-6613, -321, -1561, -278, 1041]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![-6613, -321, -1561, -278, 1041]] ![![-1645, -80, -388, -69, 259]]
  ![![9537079, 461845, 2249913, 400735, -1502194]] where
 M := ![![![9537079, 461845, 2249913, 400735, -1502194]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI59N2 : IdealMulLeCertificate' Table 
  ![![9537079, 461845, 2249913, 400735, -1502194]] ![![-25, 4, -2, 0, 8]]
  ![![59, 0, 0, 0, 0]] where
 M := ![![![-241850263, -11711913, -57055419, -10162219, 38094058]]]
 hmul := by decide  
 g := ![![![![-4099157, -198507, -967041, -172241, 645662]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0, 0, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0, 0, 0]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![0, 0, 0, 0, 61]] where
  M :=![![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![0, 0, 0, 0, 61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 5 2 5 [41, 47, 10, 19, 2, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [59, 23, 1, 22, 3], [23, 42, 14, 19, 54], [31, 23, 54, 50, 29], [7, 33, 53, 31, 36], [0, 1]]
 g := ![![[6, 48, 42, 42, 27], [1, 10, 10, 57], [10, 30, 48, 20, 9], [46, 59, 1], []], ![[24, 1, 60, 49, 58, 45, 5, 52], [42, 1, 38, 48], [60, 7, 11, 56, 6, 41, 24, 58], [22, 20, 9, 27, 57, 15, 54, 39], [17, 36, 45, 47, 8, 45, 52, 27]], ![[22, 57, 0, 0, 22, 16, 52, 28], [47, 56, 25, 47], [26, 54, 24, 12, 39, 44, 55, 21], [6, 35, 35, 10, 32, 41, 33, 43], [35, 44, 39, 21, 40, 14, 2, 23]], ![[16, 30, 31, 53, 34, 54, 23, 32], [46, 37, 51, 19], [55, 55, 23, 5, 49, 52, 14, 31], [17, 27, 53, 34, 55, 0, 8, 33], [36, 1, 4, 4, 4, 42, 24, 50]], ![[55, 34, 17, 31, 56, 17, 44, 9], [16, 59, 45, 27], [29, 18, 58, 54, 46, 16, 53, 25], [3, 35, 13, 57, 40, 29, 31, 45], [49, 19, 8, 1, 54, 1, 10, 52]]]
 h' := ![![[59, 23, 1, 22, 3], [4, 55, 16, 59, 37], [17, 33, 0, 25, 22], [5, 55, 20, 14, 58], [0, 0, 0, 1], [0, 1]], ![[23, 42, 14, 19, 54], [25, 56, 28, 12, 27], [51, 52, 60, 4, 32], [19, 42, 1, 53, 50], [27, 14, 24, 49, 14], [59, 23, 1, 22, 3]], ![[31, 23, 54, 50, 29], [12, 10, 49, 41, 39], [32, 41, 59, 21, 13], [0, 44, 27, 23, 34], [57, 9, 44, 50, 9], [23, 42, 14, 19, 54]], ![[7, 33, 53, 31, 36], [44, 50, 14, 6, 50], [10, 37, 40, 55, 18], [4, 14, 23, 20, 52], [11, 38, 19, 31, 51], [31, 23, 54, 50, 29]], ![[0, 1], [28, 12, 15, 4, 30], [14, 20, 24, 17, 37], [25, 28, 51, 12, 50], [42, 0, 35, 52, 48], [7, 33, 53, 31, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35, 7, 6, 14], [], [], []]
 b := ![[], [46, 8, 55, 50, 36], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 5
  hpos := by decide
  P := [41, 47, 10, 19, 2, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![457051090814891, 561308823366881, 686252909733184, 39405169450230, 468261856976887]
  a := ![18, 39, 36, -24, 95]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![7492640833031, 9201783989621, 11250047700544, 645986384430, 7676423884867]
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



lemma PB853I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB853I1 : PrimesBelowBoundCertificateInterval O 23 61 853 where
  m := 9
  g := ![2, 1, 2, 2, 2, 3, 1, 4, 1]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB853I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0, I29N1]
    · exact ![I31N0]
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1, I47N2]
    · exact ![I53N0]
    · exact ![I59N0, I59N1, I59N2, I59N3]
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
    · exact ![707281, 29]
    · exact ![28629151]
    · exact ![50653, 1369]
    · exact ![2825761, 41]
    · exact ![3418801, 43]
    · exact ![103823, 47, 47]
    · exact ![418195493]
    · exact ![3481, 59, 59, 59]
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
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
      exact NI47N2
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
      exact NI59N2
      exact NI59N3
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
  β := ![I29N1, I41N1, I43N1, I47N1, I47N2, I59N1, I59N2, I59N3]
  Il := ![[I29N1], [], [], [I41N1], [I43N1], [I47N1, I47N2], [], [I59N1, I59N2, I59N3], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
