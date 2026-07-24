
import IdealArithmetic.Examples.NF5_1_2025000000_5.RI5_1_2025000000_5
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0, 0, 0], ![-76, 2, 1, 10, 0]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0, 0, 0], ![-76, 2, 1, 10, 0]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![4, 6, 3, 1, 0], ![18, 5, 10, 0, 1]] where
  M :=![![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![0, 0, 0, 29, 0], ![0, 0, 0, 0, 29]], ![![-76, 2, 1, 10, 0], ![0, -75, -6, -16, 10], ![580, 4, -31, -102, -16], ![-522, 150, 12, 119, -20], ![-1624, -226, -32, 166, 63]]]
  hmulB := by decide  
  f := ![![![-2431, 139, 38, 336, -10], ![-928, 29, 0, 0, 0]], ![![152, -3, -2, -20, 0], ![58, 0, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![-220, 81, 9, 45, -10], ![-84, 29, 0, 0, 0]], ![![-1446, 121, 26, 208, -11], ![-552, 32, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-4, -6, -3, 29, 0], ![-18, -5, -10, 0, 29]], ![![-4, -2, -1, 10, 0], ![-4, -1, -2, -16, 10], ![44, 24, 15, -102, -16], ![-22, -16, -5, 119, -20], ![-118, -53, -40, 166, 63]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 3 2 4 [23, 5, 16, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [23, 28, 28], [19, 0, 1], [0, 1]]
 g := ![![[28, 23, 6], [12, 22], [20, 8, 24], [1]], ![[13, 18, 26, 25], [25, 24], [17, 27, 21, 4], [25, 8, 13, 28]], ![[11, 1, 13, 7], [12, 1], [8, 3, 11, 5], [1, 18, 13, 1]]]
 h' := ![![[23, 28, 28], [1, 2, 8], [4, 13, 14], [6, 24, 13], [0, 1]], ![[19, 0, 1], [11, 6, 27], [8, 1, 16], [21, 18, 5], [23, 28, 28]], ![[0, 1], [13, 21, 23], [17, 15, 28], [21, 16, 11], [19, 0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19], []]
 b := ![[], [5, 19], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 3
  hpos := by decide
  P := [23, 5, 16, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-65489285, 2867449, -4051636, 9582701, -317563]
  a := ![0, -9, -8, -9, -13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3382895, -1828998, -1021521, 9582701, -317563]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 24389 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![29, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] 
 ![![29, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![0, 0, 0, 29, 0], ![0, 0, 0, 0, 29]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 1, 2, 4, 0], ![0, 0, -1, -2, 1], ![58, 1, 4, -11, 0]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, 0, 0, 0]], ![![0, -2, -2, -3, 0], ![36, 14, 22, 0, 0]], ![![0, -4, -3, -6, 0], ![72, 0, 44, 1, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![0, 0, 0, 29, 0], ![0, 0, 0, 0, 29]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 1, 2, 4, 0], ![0, 0, -1, -2, 1], ![2, 1, 4, -11, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1

def I29N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0, 0, 0], ![-10, 1, 0, 0, 0]] i)))

def SI29N2: IdealEqSpanCertificate' Table ![![29, 0, 0, 0, 0], ![-10, 1, 0, 0, 0]] 
 ![![29, 0, 0, 0, 0], ![19, 1, 0, 0, 0], ![16, 0, 1, 0, 0], ![20, 0, 0, 1, 0], ![24, 0, 0, 0, 1]] where
  M :=![![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![0, 0, 0, 29, 0], ![0, 0, 0, 0, 29]], ![![-10, 1, 0, 0, 0], ![0, -10, 1, 0, 0], ![0, 1, -8, 4, 0], ![0, 0, -1, -12, 1], ![58, 1, 4, -11, -10]]]
  hmulB := by decide  
  f := ![![![5431, -7603, 70152, -30160, -400], ![15747, 4872, 253460, 11600, 0]], ![![3741, -5227, 48184, -20712, -275], ![10847, 3335, 174087, 7975, 0]], ![![3064, -4278, 39506, -16988, -225], ![8884, 2756, 142738, 6525, 0]], ![![3740, -5231, 48222, -20731, -275], ![10844, 3337, 174225, 7975, 0]], ![![4496, -6294, 58057, -24960, -331], ![13036, 4027, 209760, 9600, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-19, 29, 0, 0, 0], ![-16, 0, 29, 0, 0], ![-20, 0, 0, 29, 0], ![-24, 0, 0, 0, 29]], ![![-1, 1, 0, 0, 0], ![6, -10, 1, 0, 0], ![1, 1, -8, 4, 0], ![8, 0, -1, -12, 1], ![15, 1, 4, -11, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N2 : Nat.card (O ⧸ I29N2) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N2)

lemma isPrimeI29N2 : Ideal.IsPrime I29N2 := prime_ideal_of_norm_prime hp29.out _ NI29N2
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![29, 0, 0, 0, 0], ![-76, 2, 1, 10, 0]] ![![29, 0, 0, 0, 0], ![0, 1, 0, 0, 0]]
  ![![29, 0, 0, 0, 0], ![-58, 7, 11, 10, 1]] where
 M := ![![![841, 0, 0, 0, 0], ![0, 29, 0, 0, 0]], ![![-2204, 58, 29, 290, 0], ![0, -75, -6, -16, 10]]]
 hmul := by decide  
 g := ![![![![29, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![58, -6, -11, -10, -1], ![29, 0, 0, 0, 0]]], ![![![40, -12, -21, -10, -2], ![58, 0, 0, 0, 0]], ![![20, -5, -4, -4, 0], ![10, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI29N1 : IdealMulLeCertificate' Table 
  ![![29, 0, 0, 0, 0], ![-58, 7, 11, 10, 1]] ![![29, 0, 0, 0, 0], ![-10, 1, 0, 0, 0]]
  ![![29, 0, 0, 0, 0]] where
 M := ![![![841, 0, 0, 0, 0], ![-290, 29, 0, 0, 0]], ![![-1682, 203, 319, 290, 29], ![638, -116, -87, -87, 0]]]
 hmul := by decide  
 g := ![![![![29, 0, 0, 0, 0]], ![![-10, 1, 0, 0, 0]]], ![![![-58, 7, 11, 10, 1]], ![![22, -4, -3, -3, 0]]]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0], ![-38, -9, 1, 5, 0]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0, 0, 0], ![-38, -9, 1, 5, 0]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![11, 23, 25, 1, 0], ![7, 14, 9, 0, 1]] where
  M :=![![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]], ![![-38, -9, 1, 5, 0], ![0, -37, -12, -6, 5], ![290, -7, -35, -91, -6], ![-232, 75, 18, 74, -21], ![-1392, -92, -46, 212, 26]]]
  hmulB := by decide  
  f := ![![![1, -74, -24, -12, 10], ![0, -62, 0, 0, 0]], ![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![-7, -1, 1, 1, 0], ![-6, 0, 0, 0, 0]], ![![37, 2, -3, -6, 1], ![30, -6, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-11, -23, -25, 31, 0], ![-7, -14, -9, 0, 31]], ![![-3, -4, -4, 5, 0], ![1, 1, 3, -6, 5], ![43, 70, 74, -91, -6], ![-29, -43, -53, 74, -21], ![-126, -172, -180, 212, 26]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 3 2 4 [6, 23, 29, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [27, 24, 20], [6, 6, 11], [0, 1]]
 g := ![![[11, 17, 7], [19, 14, 2], [28, 9, 4], [1]], ![[19, 21, 30, 20], [25, 3, 28, 14], [0, 24, 29, 14], [28, 26, 5, 2]], ![[10, 17, 7, 29], [5, 27, 27, 23], [16, 14, 8, 3], [21, 10, 4, 29]]]
 h' := ![![[27, 24, 20], [10, 20, 21], [18, 20, 8], [25, 8, 2], [0, 1]], ![[6, 6, 11], [1, 21, 30], [30, 4, 14], [16, 11, 17], [27, 24, 20]], ![[0, 1], [14, 21, 11], [20, 7, 9], [28, 12, 12], [6, 6, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 28], []]
 b := ![[], [29, 7, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 3
  hpos := by decide
  P := [6, 23, 29, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-41322507319, 6328000667, -5421869602, 6749960271, -2881384404]
  a := ![3, -125, -127, -194, -121]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3077496112, -3502635610, -4781884411, 6749960271, -2881384404]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 29791 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0], ![-3, 1, 0, 0, 0]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![31, 0, 0, 0, 0], ![-3, 1, 0, 0, 0]] 
 ![![31, 0, 0, 0, 0], ![28, 1, 0, 0, 0], ![22, 0, 1, 0, 0], ![14, 0, 0, 1, 0], ![30, 0, 0, 0, 1]] where
  M :=![![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]], ![![-3, 1, 0, 0, 0], ![0, -3, 1, 0, 0], ![0, 1, -1, 4, 0], ![0, 0, -1, -5, 1], ![58, 1, 4, -11, -3]]]
  hmulB := by decide  
  f := ![![![2050, -5788, 4867, -22072, 280], ![21173, 651, 160208, -8680, 0]], ![![1942, -5483, 4610, -20914, 266], ![20058, 620, 151776, -8246, 0]], ![![1528, -4320, 3633, -16486, 210], ![15782, 497, 119629, -6510, 0]], ![![926, -2604, 2190, -9935, 126], ![9564, 318, 72114, -3906, 0]], ![![1986, -5602, 4710, -21360, 271], ![20512, 630, 155040, -8400, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-28, 31, 0, 0, 0], ![-22, 0, 31, 0, 0], ![-14, 0, 0, 31, 0], ![-30, 0, 0, 0, 31]], ![![-1, 1, 0, 0, 0], ![2, -3, 1, 0, 0], ![-2, 1, -1, 4, 0], ![2, 0, -1, -5, 1], ![6, 1, 4, -11, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1

def I31N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0], ![-2, 1, 0, 0, 0]] i)))

def SI31N2: IdealEqSpanCertificate' Table ![![31, 0, 0, 0, 0], ![-2, 1, 0, 0, 0]] 
 ![![31, 0, 0, 0, 0], ![29, 1, 0, 0, 0], ![27, 0, 1, 0, 0], ![16, 0, 0, 1, 0], ![29, 0, 0, 0, 1]] where
  M :=![![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]], ![![-2, 1, 0, 0, 0], ![0, -2, 1, 0, 0], ![0, 1, 0, 4, 0], ![0, 0, -1, -4, 1], ![58, 1, 4, -11, -2]]]
  hmulB := by decide  
  f := ![![![181, -1215, -19, -4588, 16], ![2790, 93, 35061, -496, 0]], ![![175, -1183, -19, -4472, 16], ![2698, 93, 34162, -496, 0]], ![![165, -1120, -19, -4240, 16], ![2544, 94, 32364, -496, 0]], ![![96, -620, -10, -2337, 8], ![1480, 62, 17864, -248, 0]], ![![171, -1137, -18, -4292, 15], ![2636, 94, 32799, -464, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-29, 31, 0, 0, 0], ![-27, 0, 31, 0, 0], ![-16, 0, 0, 31, 0], ![-29, 0, 0, 0, 31]], ![![-1, 1, 0, 0, 0], ![1, -2, 1, 0, 0], ![-3, 1, 0, 4, 0], ![2, 0, -1, -4, 1], ![5, 1, 4, -11, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N2 : Nat.card (O ⧸ I31N2) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N2)

lemma isPrimeI31N2 : Ideal.IsPrime I31N2 := prime_ideal_of_norm_prime hp31.out _ NI31N2
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![31, 0, 0, 0, 0], ![-38, -9, 1, 5, 0]] ![![31, 0, 0, 0, 0], ![-3, 1, 0, 0, 0]]
  ![![31, 0, 0, 0, 0], ![-33, -2, -3, 2, 1]] where
 M := ![![![961, 0, 0, 0, 0], ![-93, 31, 0, 0, 0]], ![![-1178, -279, 31, 155, 0], ![114, -10, -15, -21, 5]]]
 hmul := by decide  
 g := ![![![![31, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![30, 3, 3, -2, -1], ![31, 0, 0, 0, 0]]], ![![![-5, -7, 4, 3, -1], ![31, 0, 0, 0, 0]], ![![9, 0, 0, -1, 0], ![5, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI31N1 : IdealMulLeCertificate' Table 
  ![![31, 0, 0, 0, 0], ![-33, -2, -3, 2, 1]] ![![31, 0, 0, 0, 0], ![-2, 1, 0, 0, 0]]
  ![![31, 0, 0, 0, 0]] where
 M := ![![![961, 0, 0, 0, 0], ![-62, 31, 0, 0, 0]], ![![-1023, -62, -93, 62, 31], ![124, -31, 0, -31, 0]]]
 hmul := by decide  
 g := ![![![![31, 0, 0, 0, 0]], ![![-2, 1, 0, 0, 0]]], ![![![-33, -2, -3, 2, 1]], ![![4, -1, 0, -1, 0]]]]
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

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0, 0, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0, 0, 0]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![0, 0, 0, 0, 37]] where
  M :=![![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![0, 0, 0, 0, 37]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 5 2 5 [24, 28, 7, 20, 36, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 12, 26, 32, 9], [1, 9, 27, 14, 29], [7, 20, 13, 26, 22], [8, 32, 8, 2, 14], [0, 1]]
 g := ![![[33, 18, 29, 9, 10], [22, 10, 29, 25], [3, 28, 18, 1, 1], [], []], ![[31, 6, 0, 28, 34, 4], [31, 2, 27, 21], [23, 11, 13, 9, 17, 19, 16, 28], [18, 6, 13, 36], [24, 11, 28, 7]], ![[23, 5, 23, 10, 35, 28, 17, 18], [9, 5, 28, 30], [4, 32, 36, 26, 2, 19, 0, 19], [11, 20, 24, 28], [23, 26, 25, 27]], ![[18, 26, 30, 27, 21, 17, 30, 14], [16, 14, 13, 34], [28, 33, 20, 8, 20, 33, 31, 5], [0, 31, 20, 36], [22, 4, 0, 3]], ![[26, 1, 0, 14, 13, 29, 10, 5], [3, 21, 31, 16], [27, 3, 3, 19, 20, 26, 31, 17], [10, 5, 8, 28], [30, 1, 30, 11]]]
 h' := ![![[22, 12, 26, 32, 9], [31, 5, 24, 5, 11], [2, 21, 21, 30, 5], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[1, 9, 27, 14, 29], [30, 4, 2, 13], [16, 1, 8, 14, 24], [3, 17, 16, 19, 31], [19, 36, 29, 5, 31], [22, 12, 26, 32, 9]], ![[7, 20, 13, 26, 22], [2, 2, 4, 3, 9], [25, 6, 25, 24, 20], [11, 16, 7, 11, 17], [4, 8, 15, 4, 18], [1, 9, 27, 14, 29]], ![[8, 32, 8, 2, 14], [11, 12, 8, 36, 2], [32, 24, 27, 18, 21], [4, 7, 23, 30, 30], [2, 12, 20, 11, 6], [7, 20, 13, 26, 22]], ![[0, 1], [35, 14, 36, 17, 15], [12, 22, 30, 25, 4], [8, 34, 28, 14, 32], [10, 18, 9, 17, 19], [8, 32, 8, 2, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 8, 14, 31], [], [], []]
 b := ![[], [11, 5, 8, 5, 13], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 5
  hpos := by decide
  P := [24, 28, 7, 20, 36, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3018791258410, -1009453927460, -443101679294, -129704052928, 131833467234]
  a := ![1, -9, -9, -13, -10]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-81588952930, -27282538580, -11975721062, -3505514944, 3563066682]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0, 0, 0], ![-7, 14, 0, 1, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0, 0, 0], ![-7, 14, 0, 1, 0]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![14, 0, 1, 0, 0], ![34, 14, 0, 1, 0], ![9, 21, 0, 0, 1]] where
  M :=![![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![0, 0, 0, 0, 41]], ![![-7, 14, 0, 1, 0], ![0, -7, 13, -2, 1], ![58, 14, 25, 45, -2], ![-58, 15, -13, -14, 12], ![638, -15, 50, -139, 8]]]
  hmulB := by decide  
  f := ![![![2655309, -5310060, 56516, -375684, 3500], ![15479140, -161212, -8856, 0, 0]], ![![1327542, -2654805, 28258, -187826, 1750], ![7738914, -80606, -4428, 0, 0]], ![![898602, -1797012, 19120, -127137, 1184], ![5238406, -54538, -2997, 0, 0]], ![![2655274, -5309990, 56516, -375679, 3500], ![15478936, -161212, -8856, 0, 0]], ![![1262837, -2525411, 26884, -178672, 1665], ![7361716, -76688, -4212, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-14, 0, 41, 0, 0], ![-34, -14, 0, 41, 0], ![-9, -21, 0, 0, 41]], ![![-1, 0, 0, 1, 0], ![-3, 0, 13, -2, 1], ![-44, -14, 25, 45, -2], ![12, -1, -13, -14, 12], ![112, 43, 50, -139, 8]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [29, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 40], [0, 1]]
 g := ![![[19, 32], [16], [10], [9, 37], [1]], ![[17, 9], [16], [10], [40, 4], [1]]]
 h' := ![![[23, 40], [30, 27], [17, 37], [26, 16], [12, 23], [0, 1]], ![[0, 1], [36, 14], [7, 4], [25, 25], [8, 18], [23, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [35, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [29, 18, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![814716, -293770, 132749, -204156, 132814]
  a := ![1, 45, 41, 55, 53]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![114688, -5480, 132749, -204156, 132814]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0, 0, 0], ![2, -17, 0, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0, 0, 0], ![2, -17, 0, 1, 0]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![17, 12, 1, 0, 0], ![2, 24, 0, 1, 0], ![23, 20, 0, 0, 1]] where
  M :=![![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![0, 0, 0, 0, 41]], ![![2, -17, 0, 1, 0], ![0, 2, -18, -2, 1], ![58, -17, -28, -79, -2], ![-58, 15, 18, 57, -19], ![-1160, -46, -74, 202, 17]]]
  hmulB := by decide  
  f := ![![![466115, -3905833, 48056, 224761, -3132], ![-9400767, 117752, -5330, 0, 0]], ![![573604, -4806541, 59132, 276590, -3854], ![-11568642, 144894, -6560, 0, 0]], ![![360713, -3022612, 37193, 173936, -2424], ![-7274983, 91134, -4125, 0, 0]], ![![358506, -3004118, 36962, 172871, -2409], ![-7230472, 90569, -4100, 0, 0]], ![![541285, -4535723, 55804, 261007, -3637], ![-10916821, 136738, -6190, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-17, -12, 41, 0, 0], ![-2, -24, 0, 41, 0], ![-23, -20, 0, 0, 41]], ![![0, -1, 0, 1, 0], ![7, 6, -18, -2, 1], ![18, 55, -28, -79, -2], ![-1, -29, 18, 57, -19], ![-17, -106, -74, 202, 17]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P1 : CertificateIrreducibleZModOfList' 41 2 2 5 [15, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 40], [0, 1]]
 g := ![![[3, 37], [10], [8], [15, 16], [1]], ![[19, 4], [10], [8], [33, 25], [1]]]
 h' := ![![[37, 40], [22, 23], [34, 16], [21, 7], [26, 37], [0, 1]], ![[0, 1], [12, 18], [11, 25], [34, 34], [1, 4], [37, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [15, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N1 : CertifiedPrimeIdeal' SI41N1 41 where
  n := 2
  hpos := by decide
  P := [15, 4, 1]
  hirr := P41P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![257767, -6804, 5776, -43076, -7768]
  a := ![0, -2, -14, -36, 14]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![10351, 27148, 5776, -43076, -7768]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N1 B_one_repr
lemma NI41N1 : Nat.card (O ⧸ I41N1) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0, 0, 0], ![-12, 1, 0, 0, 0]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![41, 0, 0, 0, 0], ![-12, 1, 0, 0, 0]] 
 ![![41, 0, 0, 0, 0], ![29, 1, 0, 0, 0], ![20, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![24, 0, 0, 0, 1]] where
  M :=![![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![0, 0, 0, 0, 41]], ![![-12, 1, 0, 0, 0], ![0, -12, 1, 0, 0], ![0, 1, -10, 4, 0], ![0, 0, -1, -14, 1], ![58, 1, 4, -11, -12]]]
  hmulB := by decide  
  f := ![![![-66287, 20650, -175984, 77736, -504], ![-226484, -8692, -724470, 20664, 0]], ![![-46907, 14611, -124513, 55006, -357], ![-160268, -6150, -512582, 14637, 0]], ![![-33212, 10350, -88182, 38944, -252], ![-113476, -4345, -363014, 10332, 0]], ![![-19308, 6024, -51314, 22667, -147], ![-65970, -2519, -211242, 6027, 0]], ![![-38808, 12088, -103015, 45504, -295], ![-132596, -5089, -424080, 12096, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-29, 41, 0, 0, 0], ![-20, 0, 41, 0, 0], ![-12, 0, 0, 41, 0], ![-24, 0, 0, 0, 41]], ![![-1, 1, 0, 0, 0], ![8, -12, 1, 0, 0], ![3, 1, -10, 4, 0], ![4, 0, -1, -14, 1], ![9, 1, 4, -11, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0, 0, 0], ![-7, 14, 0, 1, 0]] ![![41, 0, 0, 0, 0], ![2, -17, 0, 1, 0]]
  ![![41, 0, 0, 0, 0], ![-43, 25, 14, 12, 1]] where
 M := ![![![1681, 0, 0, 0, 0], ![82, -697, 0, 41, 0]], ![![-287, 574, 0, 41, 0], ![-72, 162, -234, 22, -5]]]
 hmul := by decide  
 g := ![![![![41, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![2, -17, 0, 1, 0], ![0, 0, 0, 0, 0]]], ![![![36, -11, -14, -11, -1], ![41, 0, 0, 0, 0]], ![![36, -18, -18, -10, -1], ![36, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![41, 0, 0, 0, 0], ![-43, 25, 14, 12, 1]] ![![41, 0, 0, 0, 0], ![-12, 1, 0, 0, 0]]
  ![![41, 0, 0, 0, 0]] where
 M := ![![![1681, 0, 0, 0, 0], ![-492, 41, 0, 0, 0]], ![![-1763, 1025, 574, 492, 41], ![574, -328, -123, -123, 0]]]
 hmul := by decide  
 g := ![![![![41, 0, 0, 0, 0]], ![![-12, 1, 0, 0, 0]]], ![![![-43, 25, 14, 12, 1]], ![![14, -8, -3, -3, 0]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-21245, -9479, -8330, -3859, -1189]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![-21245, -9479, -8330, -3859, -1189]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![26, 18, 1, 0, 0], ![42, 35, 0, 1, 0], ![17, 16, 0, 0, 1]] where
  M :=![![![-21245, -9479, -8330, -3859, -1189], ![-68962, -30764, -27036, -12523, -3859], ![-223822, -99857, -87749, -40649, -12523], ![-52432, -23404, -20566, -9531, -2936], ![-498974, -222599, -195630, -90617, -27926]]]
  hmulB := by decide  
  f := ![![![-1763, -27, 70, 137, 33]], ![![1914, -1660, 108, -357, 137]], ![![-80, -661, 75, -75, 69]], ![![-388, -1352, 162, -136, 145]], ![![-175, -744, 88, -78, 79]]]
  g := ![![![8782, 6850, -8330, -3859, -1189], ![28501, 22231, -27036, -12523, -3859], ![92507, 72156, -87749, -40649, -12523], ![21686, 16915, -20566, -9531, -2936], ![206234, 160864, -195630, -90617, -27926]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [27, 27, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 42], [0, 1]]
 g := ![![[1, 15], [35, 36], [21], [7, 41], [1]], ![[26, 28], [9, 7], [21], [18, 2], [1]]]
 h' := ![![[16, 42], [1, 31], [23, 6], [26, 35], [16, 16], [0, 1]], ![[0, 1], [24, 12], [33, 37], [27, 8], [14, 27], [16, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36]]
 b := ![[], [28, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [27, 27, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![144619, -29885, 5286, -34679, 4825]
  a := ![13, -7, -2, 3, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![32132, 23524, 5286, -34679, 4825]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23745, 16065, -2636, 81, -2057]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![23745, 16065, -2636, 81, -2057]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![35, 9, 1, 0, 0], ![22, 38, 0, 1, 0], ![39, 23, 0, 0, 1]] where
  M :=![![![23745, 16065, -2636, 81, -2057], ![-119306, 19052, 2484, 11921, 81], ![4698, -116741, 12423, -14797, 11921], ![200332, 60868, -14186, -8543, -9680], ![-156078, 181461, -13630, 34939, -15982]]]
  hmulB := by decide  
  f := ![![![-61289, 7469, -264, 12053, 429]], ![![24882, -61124, -3396, -29881, 12053]], ![![-28421, -5934, -689, 1547, 2177]], ![![-27718, -46280, -3114, -15909, 10646]], ![![-75769, -35862, -3046, -4497, 10022]]]
  g := ![![![4522, 1954, -2636, 81, -2057], ![-10969, -10655, 2484, 11921, 81], ![-13244, 1385, 12423, -14797, 11921], ![29356, 17112, -14186, -8543, -9680], ![4084, -15255, -13630, 34939, -15982]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P1 : CertificateIrreducibleZModOfList' 43 2 2 5 [37, 40, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 42], [0, 1]]
 g := ![![[22, 41], [10, 1], [11], [20, 9], [1]], ![[16, 2], [13, 42], [11], [4, 34], [1]]]
 h' := ![![[3, 42], [17, 16], [18, 42], [34, 21], [6, 3], [0, 1]], ![[0, 1], [22, 27], [15, 1], [11, 22], [15, 40], [3, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [4, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N1 : CertifiedPrimeIdeal' SI43N1 43 where
  n := 2
  hpos := by decide
  P := [37, 40, 1]
  hirr := P43P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3362, 1632, 319, 106, -444]
  a := ![-1, -3, -5, -11, 1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![167, 115, 319, 106, -444]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N1 B_one_repr
lemma NI43N1 : Nat.card (O ⧸ I43N1) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N1

def I43N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-44871, -20017, -17592, -8149, -2511]] i)))

def SI43N2: IdealEqSpanCertificate' Table ![![-44871, -20017, -17592, -8149, -2511]] 
 ![![43, 0, 0, 0, 0], ![16, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![30, 0, 0, 1, 0], ![12, 0, 0, 0, 1]] where
  M :=![![![-44871, -20017, -17592, -8149, -2511], ![-145638, -64974, -57096, -26449, -8149], ![-472642, -210883, -185313, -85847, -26449], ![-110780, -49416, -43434, -20119, -6200], ![-1053802, -470129, -413146, -191383, -58968]]]
  hmulB := by decide  
  f := ![![![2311, 1447, 116, 291, -381]], ![![346, 586, 40, 203, -135]], ![![500, -443, -21, -263, 77]], ![![2918, 1368, 118, 169, -384]], ![![-3206, 1835, 74, 1253, -282]]]
  g := ![![![13609, -20017, -17592, -8149, -2511], ![44172, -64974, -57096, -26449, -8149], ![143370, -210883, -185313, -85847, -26449], ![33598, -49416, -43434, -20119, -6200], ![319620, -470129, -413146, -191383, -58968]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N2 : Nat.card (O ⧸ I43N2) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N2)

lemma isPrimeI43N2 : Ideal.IsPrime I43N2 := prime_ideal_of_norm_prime hp43.out _ NI43N2
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![-21245, -9479, -8330, -3859, -1189]] ![![23745, 16065, -2636, 81, -2057]]
  ![![-199737, -89044, -77762, -36028, -11046]] where
 M := ![![![-199737, -89044, -77762, -36028, -11046]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![-199737, -89044, -77762, -36028, -11046]] ![![-44871, -20017, -17592, -8149, -2511]]
  ![![43, 0, 0, 0, 0]] where
 M := ![![![74315654935, 33155768813, 29136589902, 13497279933, 4158620429]]]
 hmul := by decide  
 g := ![![![![1728271045, 771064391, 677595114, 313890231, 96712103]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0, 0, 0], ![120, -9, 1, -17, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0, 0, 0], ![120, -9, 1, -17, 0]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![4, 42, 11, 1, 0], ![20, 37, 24, 0, 1]] where
  M :=![![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![0, 0, 0, 0, 47]], ![![120, -9, 1, -17, 0], ![0, 121, 10, 38, -17], ![-986, -7, 35, 151, 38], ![1044, -255, -4, -230, 23], ![2436, 546, 86, -118, -146]]]
  hmulB := by decide  
  f := ![![![-34439, 2583, -287, 4879, 0], ![13489, 0, 0, 0, 0]], ![![960, -192, -2, -174, 17], ![-376, 47, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![-2068, 156, -17, 293, 0], ![810, 0, 0, 0, 0]], ![![-13940, 1018, -118, 1966, 4], ![5460, 11, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-4, -42, -11, 47, 0], ![-20, -37, -24, 0, 47]], ![![4, 15, 4, -17, 0], ![4, -18, 0, 38, -17], ![-50, -165, -54, 151, 38], ![32, 182, 42, -230, 23], ![124, 232, 104, -118, -146]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [17, 34, 15, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 29, 7], [39, 17, 40], [0, 1]]
 g := ![![[17, 10, 8], [39, 30, 24], [10, 14, 14], [3, 32, 1], []], ![[37, 6, 33, 21], [29, 40, 5, 16], [13, 7, 0, 25], [31, 5, 28, 2], [0, 2]], ![[45, 29, 11, 15], [42, 25, 33, 45], [10, 38, 15, 45], [23, 30, 8, 35], [14, 2]]]
 h' := ![![[40, 29, 7], [42, 39, 33], [18, 2, 27], [43, 12, 25], [0, 0, 1], [0, 1]], ![[39, 17, 40], [23, 6, 35], [11, 22, 3], [9, 17, 39], [2, 30, 17], [40, 29, 7]], ![[0, 1], [4, 2, 26], [4, 23, 17], [15, 18, 30], [14, 17, 29], [39, 17, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38, 45], []]
 b := ![[], [25, 38, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [17, 34, 15, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![271057365, 23958438, 13668720, -26201458, -9400004]
  a := ![3, 10, 6, -2, 21]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![11997091, 31323826, 11223082, -26201458, -9400004]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 103823 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0, 0, 0], ![23, 1, 0, 0, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0, 0, 0], ![23, 1, 0, 0, 0]] 
 ![![47, 0, 0, 0, 0], ![23, 1, 0, 0, 0], ![35, 0, 1, 0, 0], ![34, 0, 0, 1, 0], ![26, 0, 0, 0, 1]] where
  M :=![![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![0, 0, 0, 0, 47]], ![![23, 1, 0, 0, 0], ![0, 23, 1, 0, 0], ![0, 1, 25, 4, 0], ![0, 0, -1, 21, 1], ![58, 1, 4, -11, 23]]]
  hmulB := by decide  
  f := ![![![257946, 20075, 371154, 50666, -414], ![-527105, 12220, -697480, 19458, 0]], ![![128616, 10002, 185077, 25253, -207], ![-262823, 6110, -347800, 9729, 0]], ![![201584, 15672, 290118, 39638, -322], ![-411931, 9589, -545200, 15134, 0]], ![![186242, 14475, 268004, 36584, -299], ![-380580, 8865, -503640, 14053, 0]], ![![142672, 11099, 205319, 28028, -229], ![-291546, 6771, -385840, 10764, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-23, 47, 0, 0, 0], ![-35, 0, 47, 0, 0], ![-34, 0, 0, 47, 0], ![-26, 0, 0, 0, 47]], ![![0, 1, 0, 0, 0], ![-12, 23, 1, 0, 0], ![-22, 1, 25, 4, 0], ![-15, 0, -1, 21, 1], ![-7, 1, 4, -11, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1

def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0, 0, 0], ![-18, 1, 0, 0, 0]] i)))

def SI47N2: IdealEqSpanCertificate' Table ![![47, 0, 0, 0, 0], ![-18, 1, 0, 0, 0]] 
 ![![47, 0, 0, 0, 0], ![29, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![25, 0, 0, 0, 1]] where
  M :=![![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![0, 0, 0, 0, 47]], ![![-18, 1, 0, 0, 0], ![0, -18, 1, 0, 0], ![0, 1, -16, 4, 0], ![0, 0, -1, -20, 1], ![58, 1, 4, -11, -18]]]
  hmulB := by decide  
  f := ![![![4573, -588, 7051, -2068, 15], ![11938, 282, 20774, -705, 0]], ![![3511, -456, 5596, -1704, 15], ![9166, 235, 16497, -705, 0]], ![![2023, -279, 3518, -1184, 15], ![5282, 142, 10387, -705, 0]], ![![95, -9, 84, -21, 0], ![248, 4, 247, 0, 0]], ![![2447, -304, 3750, -1100, 8], ![6388, 175, 11050, -375, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-29, 47, 0, 0, 0], ![-5, 0, 47, 0, 0], ![-1, 0, 0, 47, 0], ![-25, 0, 0, 0, 47]], ![![-1, 1, 0, 0, 0], ![11, -18, 1, 0, 0], ![1, 1, -16, 4, 0], ![0, 0, -1, -20, 1], ![10, 1, 4, -11, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N2 : Nat.card (O ⧸ I47N2) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N2)

lemma isPrimeI47N2 : Ideal.IsPrime I47N2 := prime_ideal_of_norm_prime hp47.out _ NI47N2
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0, 0, 0], ![120, -9, 1, -17, 0]] ![![47, 0, 0, 0, 0], ![23, 1, 0, 0, 0]]
  ![![47, 0, 0, 0, 0], ![186, -53, -13, -29, 1]] where
 M := ![![![2209, 0, 0, 0, 0], ![1081, 47, 0, 0, 0]], ![![5640, -423, 47, -799, 0], ![2760, -86, 33, -353, -17]]]
 hmul := by decide  
 g := ![![![![-139, 53, 13, 29, -1], ![47, 0, 0, 0, 0]], ![![-163, 54, 13, 29, -1], ![47, 0, 0, 0, 0]]], ![![![-66, 44, 14, 12, -1], ![47, 0, 0, 0, 0]], ![![-60, 32, 9, 11, -1], ![30, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![47, 0, 0, 0, 0], ![186, -53, -13, -29, 1]] ![![47, 0, 0, 0, 0], ![-18, 1, 0, 0, 0]]
  ![![47, 0, 0, 0, 0]] where
 M := ![![![2209, 0, 0, 0, 0], ![-846, 47, 0, 0, 0]], ![![8742, -2491, -611, -1363, 47], ![-3290, 1128, 188, 517, -47]]]
 hmul := by decide  
 g := ![![![![47, 0, 0, 0, 0]], ![![-18, 1, 0, 0, 0]]], ![![![186, -53, -13, -29, 1]], ![![-70, 24, 4, 11, -1]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0, 0, 0], ![12, 17, 0, 1, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0, 0, 0], ![12, 17, 0, 1, 0]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![2, 27, 1, 0, 0], ![12, 17, 0, 1, 0], ![45, 38, 0, 0, 1]] where
  M :=![![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![0, 0, 0, 0, 53]], ![![12, 17, 0, 1, 0], ![0, 12, 16, -2, 1], ![58, 17, 50, 57, -2], ![-58, 15, -16, -1, 15], ![812, -12, 62, -172, 27]]]
  hmulB := by decide  
  f := ![![![-7616499, -10702469, 126072, -646495, 7531], ![33656961, -406351, -3604, 0, 0]], ![![-36169018, -50823558, 598726, -3070057, 35765], ![159829238, -1929783, -17119, 0, 0]], ![![-18677230, -26244659, 309165, -1585338, 18468], ![82533826, -996484, -8840, 0, 0]], ![![-13325878, -18725102, 220590, -1131112, 13177], ![58886446, -710995, -6307, 0, 0]], ![![-32399335, -45526525, 536316, -2750083, 32037], ![143171181, -1728628, -15334, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-2, -27, 53, 0, 0], ![-12, -17, 0, 53, 0], ![-45, -38, 0, 0, 53]], ![![0, 0, 0, 1, 0], ![-1, -8, 16, -2, 1], ![-12, -42, 50, 57, -2], ![-13, -2, -16, -1, 15], ![29, 4, 62, -172, 27]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [30, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [43, 52], [0, 1]]
 g := ![![[18, 44], [47], [40, 16], [24], [43, 1]], ![[2, 9], [47], [39, 37], [24], [33, 52]]]
 h' := ![![[43, 52], [11, 16], [19, 10], [28, 49], [35, 17], [0, 1]], ![[0, 1], [10, 37], [25, 43], [15, 4], [24, 36], [43, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32]]
 b := ![[], [27, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [30, 10, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![80197, -15886, 2801, -19316, 2982]
  a := ![1, 5, 1, -3, 11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3249, 2331, 2801, -19316, 2982]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0, 0, 0], ![12, -3, 0, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0, 0, 0], ![12, -3, 0, 1, 0]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![32, 23, 1, 0, 0], ![12, 50, 0, 1, 0], ![46, 45, 0, 0, 1]] where
  M :=![![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![0, 0, 0, 0, 53]], ![![12, -3, 0, 1, 0], ![0, 12, -4, -2, 1], ![58, -3, 10, -23, -2], ![-58, 15, 4, 39, -5], ![-348, -32, -18, 48, 27]]]
  hmulB := by decide  
  f := ![![![20311965, -5263899, 71708, 1705403, -17575], ![-89530833, 856851, -37312, 0, 0]], ![![32313688, -8374169, 114076, 2713072, -27959], ![-142431882, 1363107, -59360, 0, 0]], ![![26269320, -6807755, 92737, 2205584, -22729], ![-115789590, 1108125, -48256, 0, 0]], ![![35083540, -9091988, 123856, 2945631, -30356], ![-154640802, 1479972, -64448, 0, 0]], ![![45065406, -11678805, 159092, 3783712, -38992], ![-198638750, 1901009, -82784, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-32, -23, 53, 0, 0], ![-12, -50, 0, 53, 0], ![-46, -45, 0, 0, 53]], ![![0, -1, 0, 1, 0], ![2, 3, -4, -2, 1], ![2, 19, 10, -23, -2], ![-8, -34, 4, 39, -5], ![-30, -61, -18, 48, 27]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P1 : CertificateIrreducibleZModOfList' 53 2 2 5 [33, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [37, 52], [0, 1]]
 g := ![![[31, 4], [1], [3, 43], [15], [37, 1]], ![[20, 49], [1], [4, 10], [15], [21, 52]]]
 h' := ![![[37, 52], [16, 51], [7, 1], [39, 34], [51, 11], [0, 1]], ![[0, 1], [48, 2], [44, 52], [25, 19], [34, 42], [37, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41]]
 b := ![[], [5, 47]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N1 : CertifiedPrimeIdeal' SI53N1 53 where
  n := 2
  hpos := by decide
  P := [33, 16, 1]
  hirr := P53P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7015, -1059, 213, -1465, 42]
  a := ![4, -1, 0, 2, -3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![299, 1234, 213, -1465, 42]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N1 B_one_repr
lemma NI53N1 : Nat.card (O ⧸ I53N1) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N1

def I53N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0, 0, 0], ![3, 1, 0, 0, 0]] i)))

def SI53N2: IdealEqSpanCertificate' Table ![![53, 0, 0, 0, 0], ![3, 1, 0, 0, 0]] 
 ![![53, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![44, 0, 1, 0, 0], ![37, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  M :=![![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![0, 0, 0, 0, 53]], ![![3, 1, 0, 0, 0], ![0, 3, 1, 0, 0], ![0, 1, 5, 4, 0], ![0, 0, -1, 1, 1], ![58, 1, 4, -11, 3]]]
  hmulB := by decide  
  f := ![![![-6149, -56560, -275809, -218837, 1075], ![108650, -8268, 2913834, -56975, 0]], ![![-429, -3935, -19175, -15213, 75], ![7580, -530, 202566, -3975, 0]], ![![-5150, -47338, -230825, -183144, 900], ![90998, -6889, 2438583, -47700, 0]], ![![-4291, -39462, -192430, -152681, 750], ![75820, -5765, 2032961, -39750, 0]], ![![-817, -7473, -36428, -28903, 142], ![14436, -1071, 384846, -7525, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-3, 53, 0, 0, 0], ![-44, 0, 53, 0, 0], ![-37, 0, 0, 53, 0], ![-7, 0, 0, 0, 53]], ![![0, 1, 0, 0, 0], ![-1, 3, 1, 0, 0], ![-7, 1, 5, 4, 0], ![0, 0, -1, 1, 1], ![5, 1, 4, -11, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N2 : Nat.card (O ⧸ I53N2) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N2)

lemma isPrimeI53N2 : Ideal.IsPrime I53N2 := prime_ideal_of_norm_prime hp53.out _ NI53N2
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0, 0, 0], ![12, 17, 0, 1, 0]] ![![53, 0, 0, 0, 0], ![12, -3, 0, 1, 0]]
  ![![53, 0, 0, 0, 0], ![-90, 2, -23, -3, 1]] where
 M := ![![![2809, 0, 0, 0, 0], ![636, -159, 0, 53, 0]], ![![636, 901, 0, 53, 0], ![86, 183, -64, 17, 12]]]
 hmul := by decide  
 g := ![![![![53, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![12, -3, 0, 1, 0], ![0, 0, 0, 0, 0]]], ![![![12, 17, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![22, 3, 4, 1, 0], ![12, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI53N1 : IdealMulLeCertificate' Table 
  ![![53, 0, 0, 0, 0], ![-90, 2, -23, -3, 1]] ![![53, 0, 0, 0, 0], ![3, 1, 0, 0, 0]]
  ![![53, 0, 0, 0, 0]] where
 M := ![![![2809, 0, 0, 0, 0], ![159, 53, 0, 0, 0]], ![![-4770, 106, -1219, -159, 53], ![-212, -106, -106, -106, 0]]]
 hmul := by decide  
 g := ![![![![53, 0, 0, 0, 0]], ![![3, 1, 0, 0, 0]]], ![![![-90, 2, -23, -3, 1]], ![![-4, -2, -2, -2, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0, 0, 0], ![92, 19, 1, -9, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0, 0, 0], ![92, 19, 1, -9, 0]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![16, 11, 13, 1, 0], ![26, 10, 35, 0, 1]] where
  M :=![![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![0, 0, 0, 0, 59]], ![![92, 19, 1, -9, 0], ![0, 93, 30, 22, -9], ![-522, 21, 95, 175, 22], ![580, -135, -24, -146, 35], ![2668, 342, 150, -306, -54]]]
  hmulB := by decide  
  f := ![![![32109, 6352, 259, -3207, 27], ![-20591, 177, 0, 0, 0]], ![![-736, -244, -38, 50, 9], ![472, 59, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![8536, 1670, 63, -857, 9], ![-5474, 59, 0, 0, 0]], ![![14078, 2701, 87, -1426, 20], ![-9028, 131, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-16, -11, -13, 59, 0], ![-26, -10, -35, 0, 59]], ![![4, 2, 2, -9, 0], ![-2, -1, 1, 22, -9], ![-66, -36, -50, 175, 22], ![34, 19, 11, -146, 35], ![152, 72, 102, -306, -54]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [28, 26, 20, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [57, 16, 8], [41, 42, 51], [0, 1]]
 g := ![![[38, 45, 41], [53, 55, 4], [15, 5], [29, 2, 46], [1]], ![[56, 47, 26, 8], [57, 30], [32, 41], [42, 52, 25, 34], [34, 49, 30, 40]], ![[17, 15, 41, 1], [55, 54, 31, 27], [53, 29], [43, 56, 34, 7], [40, 44, 14, 19]]]
 h' := ![![[57, 16, 8], [50, 58, 10], [12, 40, 57], [14, 33, 8], [31, 33, 39], [0, 1]], ![[41, 42, 51], [13, 41, 58], [46, 15], [23, 19, 10], [43, 1, 14], [57, 16, 8]], ![[0, 1], [47, 19, 50], [16, 4, 2], [5, 7, 41], [10, 25, 6], [41, 42, 51]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42, 13], []]
 b := ![[], [27, 16, 50], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [28, 26, 20, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8650692783, 223082836, -588172259, 1180157030, -30924235]
  a := ![7, -44, -45, -44, -67]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-453036867, -211006816, -251658736, 1180157030, -30924235]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 205379 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0, 0, 0], ![14, 1, 0, 0, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0, 0, 0], ![14, 1, 0, 0, 0]] 
 ![![59, 0, 0, 0, 0], ![14, 1, 0, 0, 0], ![40, 0, 1, 0, 0], ![43, 0, 0, 1, 0], ![55, 0, 0, 0, 1]] where
  M :=![![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![0, 0, 0, 0, 59]], ![![14, 1, 0, 0, 0], ![0, 14, 1, 0, 0], ![0, 1, 16, 4, 0], ![0, 0, -1, 12, 1], ![58, 1, 4, -11, 14]]]
  hmulB := by decide  
  f := ![![![-130759, -38080, -519317, -122484, 605], ![551060, -15576, 1913724, -35695, 0]], ![![-35602, -10358, -141261, -33312, 165], ![150038, -4248, 520557, -9735, 0]], ![![-94804, -27595, -376424, -88764, 440], ![399534, -11327, 1387149, -25960, 0]], ![![-95111, -27697, -377724, -89089, 440], ![400828, -11332, 1391943, -25960, 0]], ![![-121903, -35498, -484109, -114180, 564], ![513738, -14524, 1783980, -33275, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-14, 59, 0, 0, 0], ![-40, 0, 59, 0, 0], ![-43, 0, 0, 59, 0], ![-55, 0, 0, 0, 59]], ![![0, 1, 0, 0, 0], ![-4, 14, 1, 0, 0], ![-14, 1, 16, 4, 0], ![-9, 0, -1, 12, 1], ![-7, 1, 4, -11, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0, 0, 0], ![-5, 1, 0, 0, 0]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![59, 0, 0, 0, 0], ![-5, 1, 0, 0, 0]] 
 ![![59, 0, 0, 0, 0], ![54, 1, 0, 0, 0], ![34, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![0, 0, 0, 0, 59]], ![![-5, 1, 0, 0, 0], ![0, -5, 1, 0, 0], ![0, 1, -3, 4, 0], ![0, 0, -1, -7, 1], ![58, 1, 4, -11, -5]]]
  hmulB := by decide  
  f := ![![![151, -454, 1286, -1716, 0], ![1770, 59, 25311, 0, 0]], ![![136, -425, 1208, -1612, 0], ![1594, 59, 23777, 0, 0]], ![![86, -259, 740, -988, 0], ![1008, 60, 14573, 0, 0]], ![![38, -91, 261, -349, 0], ![446, 45, 5148, 0, 0]], ![![0, 2, -1, 1, 0], ![0, 21, -13, 1, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-54, 59, 0, 0, 0], ![-34, 0, 59, 0, 0], ![-12, 0, 0, 59, 0], ![0, 0, 0, 0, 59]], ![![-1, 1, 0, 0, 0], ![4, -5, 1, 0, 0], ![0, 1, -3, 4, 0], ![2, 0, -1, -7, 1], ![0, 1, 4, -11, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0, 0, 0], ![92, 19, 1, -9, 0]] ![![59, 0, 0, 0, 0], ![14, 1, 0, 0, 0]]
  ![![59, 0, 0, 0, 0], ![-130, 6, -18, 5, 1]] where
 M := ![![![3481, 0, 0, 0, 0], ![826, 59, 0, 0, 0]], ![![5428, 1121, 59, -531, 0], ![1288, 359, 44, -104, -9]]]
 hmul := by decide  
 g := ![![![![59, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![14, 1, 0, 0, 0], ![0, 0, 0, 0, 0]]], ![![![92, 19, 1, -9, 0], ![0, 0, 0, 0, 0]], ![![132, 1, 16, -6, -1], ![50, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![59, 0, 0, 0, 0], ![-130, 6, -18, 5, 1]] ![![59, 0, 0, 0, 0], ![-5, 1, 0, 0, 0]]
  ![![59, 0, 0, 0, 0]] where
 M := ![![![3481, 0, 0, 0, 0], ![-295, 59, 0, 0, 0]], ![![-7670, 354, -1062, 295, 59], ![708, -177, 59, -118, 0]]]
 hmul := by decide  
 g := ![![![![59, 0, 0, 0, 0]], ![![-5, 1, 0, 0, 0]]], ![![![-130, 6, -18, 5, 1]], ![![12, -3, 1, -2, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0, 0, 0], ![150, -8, 1, -20, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0, 0, 0], ![150, -8, 1, -20, 0]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![23, 37, 3, 1, 0], ![14, 22, 12, 0, 1]] where
  M :=![![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![0, 0, 0, 0, 61]], ![![150, -8, 1, -20, 0], ![0, 151, 14, 44, -20], ![-1160, -6, 55, 188, 44], ![1218, -300, -8, -265, 30], ![3016, 634, 108, -174, -161]]]
  hmulB := by decide  
  f := ![![![-31049, 1958, -179, 4228, -40], ![12627, -122, 0, 0, 0]], ![![300, -166, -12, -84, 20], ![-122, 61, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![-11407, 609, -76, 1521, 0], ![4639, 0, 0, 0, 0]], ![![-7126, 373, -48, 948, 1], ![2898, 3, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-23, -37, -3, 61, 0], ![-14, -22, -12, 0, 61]], ![![10, 12, 1, -20, 0], ![-12, -17, 2, 44, -20], ![-100, -130, -17, 188, 44], ![113, 145, 7, -265, 30], ![152, 174, 42, -174, -161]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [36, 26, 30, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [39, 52, 39], [53, 8, 22], [0, 1]]
 g := ![![[4, 58, 20], [60, 42], [57], [22, 58, 46], [1]], ![[29, 44, 33, 20], [39, 36], [29, 11, 2, 14], [55, 39, 26, 5], [5, 26, 30, 27]], ![[10, 12, 54, 27], [7, 14], [9, 10, 11, 47], [0, 1, 7, 15], [6, 11, 43, 34]]]
 h' := ![![[39, 52, 39], [32, 23, 9], [22, 44, 15], [1, 39], [25, 35, 31], [0, 1]], ![[53, 8, 22], [56, 53, 54], [39, 17, 6], [58, 15, 57], [30, 18, 27], [39, 52, 39]], ![[0, 1], [57, 46, 59], [59, 0, 40], [55, 7, 4], [4, 8, 3], [53, 8, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 32], []]
 b := ![[], [52, 60, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [36, 26, 30, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-115792499, -972341, -6911963, 14498383, 1128530]
  a := ![1, -9, -9, -7, -16]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-7623848, -9217052, -1048352, 14498383, 1128530]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 226981 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0, 0, 0], ![-6, 1, 0, 0, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0, 0, 0], ![-6, 1, 0, 0, 0]] 
 ![![61, 0, 0, 0, 0], ![55, 1, 0, 0, 0], ![25, 0, 1, 0, 0], ![57, 0, 0, 1, 0], ![54, 0, 0, 0, 1]] where
  M :=![![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![0, 0, 0, 0, 61]], ![![-6, 1, 0, 0, 0], ![0, -6, 1, 0, 0], ![0, 1, -4, 4, 0], ![0, 0, -1, -8, 1], ![58, 1, 4, -11, -6]]]
  hmulB := by decide  
  f := ![![![31507, -36757, 127334, -133224, 645], ![320311, 5185, 1952976, -39345, 0]], ![![29365, -34270, 118742, -124240, 602], ![298535, 4880, 1821216, -36722, 0]], ![![14623, -17077, 59179, -61928, 301], ![148663, 2441, 907680, -18361, 0]], ![![29403, -34303, 118849, -124347, 602], ![298921, 4881, 1822848, -36722, 0]], ![![27894, -32534, 112721, -117936, 571], ![283580, 4645, 1728864, -34830, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-55, 61, 0, 0, 0], ![-25, 0, 61, 0, 0], ![-57, 0, 0, 61, 0], ![-54, 0, 0, 0, 61]], ![![-1, 1, 0, 0, 0], ![5, -6, 1, 0, 0], ![-3, 1, -4, 4, 0], ![7, 0, -1, -8, 1], ![14, 1, 4, -11, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0, 0, 0], ![-4, 1, 0, 0, 0]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![61, 0, 0, 0, 0], ![-4, 1, 0, 0, 0]] 
 ![![61, 0, 0, 0, 0], ![57, 1, 0, 0, 0], ![45, 0, 1, 0, 0], ![54, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![0, 0, 0, 0, 61]], ![![-4, 1, 0, 0, 0], ![0, -4, 1, 0, 0], ![0, 1, -2, 4, 0], ![0, 0, -1, -6, 1], ![58, 1, 4, -11, -4]]]
  hmulB := by decide  
  f := ![![![8209, -22386, 39781, -88572, 1118], ![125172, 2013, 1248426, -68198, 0]], ![![7885, -21517, 38241, -85146, 1075], ![120232, 1952, 1200114, -65575, 0]], ![![6305, -17208, 30579, -68088, 860], ![96140, 1526, 959652, -52460, 0]], ![![7262, -19802, 35191, -78353, 989], ![110732, 1800, 1104390, -60329, 0]], ![![407, -1100, 1956, -4356, 55], ![6206, 126, 61398, -3354, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-57, 61, 0, 0, 0], ![-45, 0, 61, 0, 0], ![-54, 0, 0, 61, 0], ![-3, 0, 0, 0, 61]], ![![-1, 1, 0, 0, 0], ![3, -4, 1, 0, 0], ![-3, 1, -2, 4, 0], ![6, 0, -1, -6, 1], ![7, 1, 4, -11, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0, 0, 0], ![150, -8, 1, -20, 0]] ![![61, 0, 0, 0, 0], ![-6, 1, 0, 0, 0]]
  ![![61, 0, 0, 0, 0], ![45, -13, 24, 4, 1]] where
 M := ![![![3721, 0, 0, 0, 0], ![-366, 61, 0, 0, 0]], ![![9150, -488, 61, -1220, 0], ![-900, 199, 8, 164, -20]]]
 hmul := by decide  
 g := ![![![![16, 13, -24, -4, -1], ![61, 0, 0, 0, 0]], ![![-6, 1, 0, 0, 0], ![0, 0, 0, 0, 0]]], ![![![60, 18, -47, -28, -2], ![122, 0, 0, 0, 0]], ![![-45, 12, -16, 0, -1], ![41, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![61, 0, 0, 0, 0], ![45, -13, 24, 4, 1]] ![![61, 0, 0, 0, 0], ![-4, 1, 0, 0, 0]]
  ![![61, 0, 0, 0, 0]] where
 M := ![![![3721, 0, 0, 0, 0], ![-244, 61, 0, 0, 0]], ![![2745, -793, 1464, 244, 61], ![-122, 122, -61, 61, 0]]]
 hmul := by decide  
 g := ![![![![61, 0, 0, 0, 0]], ![![-4, 1, 0, 0, 0]]], ![![![45, -13, 24, 4, 1]], ![![-2, 2, -1, 1, 0]]]]
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


lemma PB2802I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB2802I1 : PrimesBelowBoundCertificateInterval O 23 61 2802 where
  m := 9
  g := ![3, 3, 1, 3, 3, 3, 3, 3, 3]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB2802I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0, I29N1, I29N2]
    · exact ![I31N0, I31N1, I31N2]
    · exact ![I37N0]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0, I43N1, I43N2]
    · exact ![I47N0, I47N1, I47N2]
    · exact ![I53N0, I53N1, I53N2]
    · exact ![I59N0, I59N1, I59N2]
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
    · exact ![24389, 29, 29]
    · exact ![29791, 31, 31]
    · exact ![69343957]
    · exact ![1681, 1681, 41]
    · exact ![1849, 1849, 43]
    · exact ![103823, 47, 47]
    · exact ![2809, 2809, 53]
    · exact ![205379, 59, 59]
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
      exact NI29N2
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
      exact NI31N2
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
      exact NI43N1
      exact NI43N2
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
      exact NI61N1
      exact NI61N2
  β := ![I29N1, I29N2, I31N1, I31N2, I41N0, I41N1, I41N2, I43N0, I43N1, I43N2, I47N1, I47N2, I53N2, I59N1, I59N2, I61N1, I61N2]
  Il := ![[I29N1, I29N2], [I31N1, I31N2], [], [I41N0, I41N1, I41N2], [I43N0, I43N1, I43N2], [I47N1, I47N2], [I53N2], [I59N1, I59N2], [I61N1, I61N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
