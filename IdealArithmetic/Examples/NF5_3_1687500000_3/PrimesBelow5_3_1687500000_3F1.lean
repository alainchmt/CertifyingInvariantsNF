
import IdealArithmetic.Examples.NF5_3_1687500000_3.RI5_3_1687500000_3
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


def P29P0 : CertificateIrreducibleZModOfList' 29 5 2 4 [14, 12, 13, 20, 14, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 19, 23, 0, 20], [1, 15, 8, 20, 16], [21, 13, 23, 0, 13], [3, 10, 4, 9, 9], [0, 1]]
 g := ![![[9, 25, 5, 24, 23], [7, 9, 3, 20], [2, 15, 1], []], ![[1, 19, 12, 26, 26, 5, 20, 16], [9, 12, 11, 20], [10, 28, 26, 0, 8, 14, 19, 20], [17, 20, 16, 24, 3, 13, 27, 25]], ![[1, 16, 7, 8, 25, 24, 5, 5], [8, 5, 18, 16], [21, 2, 19, 12, 22, 0, 0, 25], [11, 4, 23, 3, 21, 7, 8, 7]], ![[28, 26, 21, 23, 1, 3, 15, 5], [8, 2, 26, 23], [6, 4, 18, 6, 1, 25, 10, 24], [19, 24, 23, 5, 4, 18, 11, 22]], ![[1, 1, 18, 4, 27, 8, 7, 25], [16, 1, 11, 24], [9, 17, 25, 28, 0, 12, 20, 22], [21, 19, 22, 23, 21, 12, 14, 4]]]
 h' := ![![[19, 19, 23, 0, 20], [19, 18, 19, 16, 9], [1, 27, 12, 14, 7], [0, 0, 0, 1], [0, 1]], ![[1, 15, 8, 20, 16], [10, 25, 0, 23, 13], [7, 7, 22, 2, 22], [9, 25, 25, 14, 1], [19, 19, 23, 0, 20]], ![[21, 13, 23, 0, 13], [8, 19, 27, 11, 19], [2, 10, 6, 23, 4], [21, 2, 12, 27, 23], [1, 15, 8, 20, 16]], ![[3, 10, 4, 9, 9], [11, 11, 7, 24, 25], [6, 4, 4, 0, 9], [5, 18, 25, 2, 10], [21, 13, 23, 0, 13]], ![[0, 1], [13, 14, 5, 13, 21], [11, 10, 14, 19, 16], [23, 13, 25, 14, 24], [3, 10, 4, 9, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 20, 25, 9], [], [], []]
 b := ![[], [10, 24, 25, 20, 1], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 5
  hpos := by decide
  P := [14, 12, 13, 20, 14, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-36438651781871908, -25855415098449704, 53641960937070920, 38892062390782988, -87262734738600586]
  a := ![-189, -11, 173, 177, -387]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1256505233857652, -891566037877576, 1849722790933480, 1341105599682172, -3009059818572434]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-364191, 213767, 59279, 90624, -196516]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![-364191, 213767, 59279, 90624, -196516]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![15, 3, 1, 0, 0], ![24, 19, 0, 1, 0], ![0, 12, 0, 0, 1]] where
  M :=![![![-364191, 213767, 59279, 90624, -196516], ![-124112, 72852, 20203, 30886, -66976], ![-42308, 24839, 6890, 10534, -22844], ![54830, -32179, -8921, -13637, 29570], ![187280, -109922, -30480, -46596, 101041]]]
  hmulB := by decide  
  f := ![![![-29, 35, 1, 24, -40]], ![![208, 60, -221, -238, 464]], ![![-17, -8, 26, 12, -36]], ![![-22, 129, -80, 9, 22]], ![![24, 44, -54, -32, 73]]]
  g := ![![![-110592, 21686, 59279, 90624, -196516], ![-37691, 7391, 20203, 30886, -66976], ![-12854, 2521, 6890, 10534, -22844], ![16643, -3263, -8921, -13637, 29570], ![56864, -11150, -30480, -46596, 101041]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [27, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [24, 30], [0, 1]]
 g := ![![[6, 14], [1, 1], [30, 19], [24, 1]], ![[1, 17], [25, 30], [21, 12], [17, 30]]]
 h' := ![![[24, 30], [4, 13], [27, 30], [3, 22], [0, 1]], ![[0, 1], [6, 18], [3, 1], [4, 9], [24, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [8, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [27, 7, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3677787, -1159726, 4152008, 4040750, -8165706]
  a := ![171, -54, -156, -226, 350]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5255997, 245112, 4152008, 4040750, -8165706]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![44, -24, -8, -13, 29]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![44, -24, -8, -13, 29]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![19, 0, 1, 0, 0], ![0, 10, 0, 1, 0], ![26, 9, 0, 0, 1]] where
  M :=![![![44, -24, -8, -13, 29], ![34, -19, -10, -18, 42], ![84, -54, -31, -56, 132], ![127, -86, -52, -90, 211], ![80, -56, -36, -64, 151]]]
  hmulB := by decide  
  f := ![![![-6, 6, 4, 5, -11]], ![![-10, 19, -2, 6, -10]], ![![-2, 4, 1, 1, -3]], ![![-9, 2, 8, 8, -17]], ![![-10, 9, 6, 8, -17]]]
  g := ![![![-18, -5, -8, -13, 29], ![-28, -7, -10, -18, 42], ![-89, -22, -31, -56, 132], ![-141, -35, -52, -90, 211], ![-102, -25, -36, -64, 151]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P1 : CertificateIrreducibleZModOfList' 31 2 2 4 [28, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 30], [0, 1]]
 g := ![![[12, 10], [13, 16], [17, 9], [5, 1]], ![[0, 21], [0, 15], [0, 22], [10, 30]]]
 h' := ![![[5, 30], [8, 17], [20, 27], [15, 28], [0, 1]], ![[0, 1], [0, 14], [0, 4], [0, 3], [5, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20]]
 b := ![[], [6, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N1 : CertifiedPrimeIdeal' SI31N1 31 where
  n := 2
  hpos := by decide
  P := [28, 26, 1]
  hirr := P31P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![58669, -12310, -41081, -60640, 114370]
  a := ![-62, -6, 57, 55, -127]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-68852, -14040, -41081, -60640, 114370]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N1 B_one_repr
lemma NI31N1 : Nat.card (O ⧸ I31N1) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N1

def I31N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![60, 21, -71, -63, 133]] i)))

def SI31N2: IdealEqSpanCertificate' Table ![![60, 21, -71, -63, 133]] 
 ![![31, 0, 0, 0, 0], ![28, 1, 0, 0, 0], ![22, 0, 1, 0, 0], ![19, 0, 0, 1, 0], ![24, 0, 0, 0, 1]] where
  M :=![![![60, 21, -71, -63, 133], ![14, -270, 217, -16, -98], ![-2632, 297, 2020, 2838, -5296], ![6631, 5315, -10285, -7068, 16163], ![2168, 2208, -3766, -2304, 5503]]]
  hmulB := by decide  
  f := ![![![7988922, -4689177, -1300337, -1987917, 4310749]], ![![7303622, -4286934, -1188793, -1817392, 3940970]], ![![5699492, -3345375, -927694, -1418232, 3075402]], ![![4857637, -2851240, -790668, -1208751, 2621148]], ![![6052448, -3552546, -985144, -1506060, 3265855]]]
  g := ![![![-31, 21, -71, -63, 133], ![176, -270, 217, -16, -98], ![574, 297, 2020, 2838, -5296], ![-5469, 5315, -10285, -7068, 16163], ![-2100, 2208, -3766, -2304, 5503]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N2 : Nat.card (O ⧸ I31N2) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N2)

lemma isPrimeI31N2 : Ideal.IsPrime I31N2 := prime_ideal_of_norm_prime hp31.out _ NI31N2
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![-364191, 213767, 59279, 90624, -196516]] ![![44, -24, -8, -13, 29]]
  ![![-7988922, 4689177, 1300337, 1987917, -4310749]] where
 M := ![![![-7988922, 4689177, 1300337, 1987917, -4310749]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI31N1 : IdealMulLeCertificate' Table 
  ![![-7988922, 4689177, 1300337, 1987917, -4310749]] ![![60, 21, -71, -63, 133]]
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

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8864, -15198, -5270, -8211, 18551]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![8864, -15198, -5270, -8211, 18551]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![14, 27, 1, 1, 0], ![17, 16, 33, 0, 1]] where
  M :=![![![8864, -15198, -5270, -8211, 18551], ![26158, -31379, -10336, -16018, 35894], ![45124, -52108, -16875, -26044, 58212], ![22117, -25336, -7830, -11894, 26401], ![26144, -27680, -8600, -13136, 29169]]]
  hmulB := by decide  
  f := ![![![126, 740, -742, -127, 605]], ![![6766, -1475, -4592, -7294, 13278]], ![![-40788, -25692, 57265, 43572, -96164]], ![![2531, 1229, -3241, -2708, 5797]], ![![-34158, -22248, 48583, 36481, -80874]]]
  g := ![![![-5177, -2441, -16466, -8211, 18551], ![-9724, -4681, -31860, -16018, 35894], ![-15672, -7576, -51671, -26044, 58212], ![-7032, -3422, -23437, -11894, 26401], ![-7725, -3776, -25893, -13136, 29169]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [6, 35, 13, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 7, 7], [7, 29, 30], [0, 1]]
 g := ![![[28, 8, 26], [12, 27], [25, 13, 11], [24, 1], []], ![[14, 10, 3, 10], [], [24, 29, 13, 7], [33, 27], [16, 12]], ![[18, 24, 34, 11], [36, 27], [23, 30, 29, 16], [32, 12], [30, 12]]]
 h' := ![![[17, 7, 7], [6, 21, 10], [35, 25, 8], [4, 5, 23], [0, 0, 1], [0, 1]], ![[7, 29, 30], [36, 18, 30], [6, 20], [14, 1, 36], [8, 13, 29], [17, 7, 7]], ![[0, 1], [27, 35, 34], [13, 29, 29], [23, 31, 15], [17, 24, 7], [7, 29, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 23], []]
 b := ![[], [10, 1, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [6, 35, 13, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-824323825, -5594115959, 5482578438, 872656937, -4327208238]
  a := ![295, 33, -270, -263, 604]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1635703219, 1083229150, 3983994415, 872656937, -4327208238]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 50653 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-16, 19, 7, 7, -19]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-16, 19, 7, 7, -19]] 
 ![![37, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![21, 0, 1, 0, 0], ![30, 0, 0, 1, 0], ![10, 0, 0, 0, 1]] where
  M :=![![![-16, 19, 7, 7, -19], ![-86, 24, 69, 76, -158], ![32, 293, -254, -58, 216], ![985, -289, -593, -1076, 1905], ![400, -54, -288, -444, 807]]]
  hmulB := by decide  
  f := ![![![16758, -10077, -3141, -4977, 11011]], ![![2114, -1288, -425, -684, 1526]], ![![10094, -6130, -1995, -3199, 7123]], ![![14313, -8697, -2837, -4552, 10139]], ![![4932, -3038, -1048, -1706, 3829]]]
  g := ![![![-7, 19, 7, 7, -19], ![-63, 24, 69, 76, -158], ![102, 293, -254, -58, 216], ![752, -289, -593, -1076, 1905], ![322, -54, -288, -444, 807]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, 1, 5, 4, -10]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![-7, 1, 5, 4, -10]] 
 ![![37, 0, 0, 0, 0], ![31, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![-7, 1, 5, 4, -10], ![-32, 16, 15, 30, -56], ![140, 99, -202, -162, 340], ![14, -371, 311, -37, -138], ![24, -124, 90, -40, -5]]]
  hmulB := by decide  
  f := ![![![329129, -369221, -121599, -188948, 423250]], ![![290059, -325391, -107164, -166518, 373006]], ![![31889, -35772, -11781, -18306, 41006]], ![![64704, -72585, -23905, -37145, 83206]], ![![37919, -42537, -14009, -21768, 48761]]]
  g := ![![![-1, 1, 5, 4, -10], ![-15, 16, 15, 30, -56], ![-75, 99, -202, -162, 340], ![320, -371, 311, -37, -138], ![109, -124, 90, -40, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![8864, -15198, -5270, -8211, 18551]] ![![-16, 19, 7, 7, -19]]
  ![![329129, -369221, -121599, -188948, 423250]] where
 M := ![![![329129, -369221, -121599, -188948, 423250]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![329129, -369221, -121599, -188948, 423250]] ![![-7, 1, 5, 4, -10]]
  ![![37, 0, 0, 0, 0]] where
 M := ![![![37, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1660, 1172, 644, 1131, -2637]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![-1660, 1172, 644, 1131, -2637]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![11, 36, 23, 36, 1]] where
  M :=![![![-1660, 1172, 644, 1131, -2637], ![-5238, 3883, 1892, 3514, -8214], ![-16692, 11896, 6475, 11076, -26356], ![-28345, 17204, 13046, 20402, -46745], ![-20728, 13574, 8834, 14476, -33555]]]
  hmulB := by decide  
  f := ![![![-9010, 5106, 1396, 2131, -4607]], ![![-2638, 1255, 316, 478, -1014]], ![![-204, -352, -149, -236, 548]], ![![1843, -1314, -390, -600, 1319]], ![![-3102, 1040, 203, 297, -584]]]
  g := ![![![667, 2344, 1495, 2343, -2637], ![2076, 7307, 4654, 7298, -8214], ![6664, 23432, 14943, 23412, -26356], ![11850, 41464, 26541, 41542, -46745], ![8497, 29794, 19039, 29816, -33555]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 4 2 5 [36, 2, 7, 13, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 39, 4, 40], [25, 1, 39, 12], [25, 0, 39, 30], [0, 1]]
 g := ![![[12, 30, 8, 8], [6, 6, 21], [35, 2, 4], [28, 1], []], ![[8, 10, 40, 28, 14, 31], [9, 14, 9], [7, 34, 23], [24, 36, 21, 35, 13, 8], [40, 20, 1]], ![[7, 4, 18, 7, 10, 28], [25, 7, 23], [29, 5, 23], [10, 11, 1, 20, 5, 28], [36, 7, 21]], ![[36, 37, 3, 14, 26, 6], [13, 1, 8], [5, 5, 4], [2, 39, 34, 1, 21, 3], [10, 29, 39]]]
 h' := ![![[19, 39, 4, 40], [35, 32, 33, 34], [13, 10, 27, 12], [17, 31, 7, 39], [0, 0, 1], [0, 1]], ![[25, 1, 39, 12], [25, 4, 31, 25], [12, 39, 15, 3], [10, 29, 8, 8], [28, 26, 5, 22], [19, 39, 4, 40]], ![[25, 0, 39, 30], [4, 29, 29, 4], [24, 18, 27, 33], [17, 22, 22, 33], [26, 13, 27, 37], [25, 1, 39, 12]], ![[0, 1], [40, 17, 30, 19], [4, 15, 13, 34], [15, 0, 4, 2], [19, 2, 8, 23], [25, 0, 39, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [23, 16, 3], []]
 b := ![[], [], [3, 3, 21, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 4
  hpos := by decide
  P := [36, 2, 7, 13, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-44500483152075, 209126507795870, -140386732097045, 50280342105146, 5617682914314]
  a := ![-421, -19, 386, 404, -862]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2592560858769, 168046899526, -6575449734787, -3706249824638, 5617682914314]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 2825761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9010, 5106, 1396, 2131, -4607]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-9010, 5106, 1396, 2131, -4607]] 
 ![![41, 0, 0, 0, 0], ![21, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![28, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![-9010, 5106, 1396, 2131, -4607], ![-2638, 1255, 316, 478, -1014], ![-204, -352, -149, -236, 548], ![1843, -1314, -390, -600, 1319], ![5240, -3306, -942, -1444, 3149]]]
  hmulB := by decide  
  f := ![![![-1660, 1172, 644, 1131, -2637]], ![![-978, 695, 376, 665, -1551]], ![![-812, 576, 315, 546, -1286]], ![![-1825, 1220, 758, 1270, -2941]], ![![-708, 474, 294, 491, -1140]]]
  g := ![![![-4069, 5106, 1396, 2131, -4607], ![-987, 1255, 316, 478, -1014], ![306, -352, -149, -236, 548], ![1062, -1314, -390, -600, 1319], ![2653, -3306, -942, -1444, 3149]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![-1660, 1172, 644, 1131, -2637]] ![![-9010, 5106, 1396, 2131, -4607]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![142, 54, -168, -149, 313]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![142, 54, -168, -149, 313]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![25, 2, 1, 0, 0], ![18, 11, 0, 1, 0], ![12, 15, 0, 0, 1]] where
  M :=![![![142, 54, -168, -149, 313], ![2, -637, 544, -10, -294], ![-6300, 820, 4751, 6780, -12620], ![16179, 12634, -24802, -17264, 39287], ![5304, 5278, -9102, -5652, 13413]]]
  hmulB := by decide  
  f := ![![![-6840980, 7673808, 2527264, 3927017, -8796639]], ![![-10998066, 12336957, 4063008, 6313350, -14142098]], ![![-4900044, 5496578, 1810223, 2812835, -6300837]], ![![-5879771, 6595573, 2172162, 3375238, -7560637]], ![![-5946514, 6670439, 2196818, 3413550, -7646457]]]
  g := ![![![76, -62, -168, -149, 313], ![-230, 65, 544, -10, -294], ![-2225, 2466, 4751, 6780, -12620], ![11059, -7841, -24802, -17264, 39287], ![4038, -2687, -9102, -5652, 13413]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [40, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 42], [0, 1]]
 g := ![![[40, 14], [13, 11], [35], [34, 38], [1]], ![[0, 29], [0, 32], [35], [36, 5], [1]]]
 h' := ![![[34, 42], [39, 33], [17, 21], [16, 32], [3, 34], [0, 1]], ![[0, 1], [0, 10], [0, 22], [29, 11], [41, 9], [34, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [11, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [40, 9, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-683474, -850924, 1319284, 725500, -1807462]
  a := ![210, 0, -192, -220, 430]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-582210, 363766, 1319284, 725500, -1807462]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![12, 36, -38, -15, 43]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![12, 36, -38, -15, 43]] 
 ![![43, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![34, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![0, 0, 0, 0, 43]] where
  M :=![![![12, 36, -38, -15, 43], ![230, -99, -110, -250, 430], ![-1900, -810, 2341, 2040, -4300], ![-275, 4460, -3580, 366, 1505], ![-472, 1638, -994, 540, -215]]]
  hmulB := by decide  
  f := ![![![-8820690, 5177382, 1435714, 2194875, -4759529]], ![![-685300, 402243, 111544, 170525, -369779]], ![![-6998320, 4107726, 1139093, 1741410, -3776202]], ![![-2430695, 1426718, 395636, 604836, -1311571]], ![![4536296, -2662614, -738358, -1128780, 2447731]]]
  g := ![![![32, 36, -38, -15, 1], ![169, -99, -110, -250, 10], ![-2408, -810, 2341, 2040, -100], ![2411, 4460, -3580, 366, 35], ![510, 1638, -994, 540, -5]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P1 : CertificateIrreducibleZModOfList' 43 2 2 5 [33, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 42], [0, 1]]
 g := ![![[15, 9], [33, 9], [21], [6, 11], [1]], ![[32, 34], [7, 34], [21], [22, 32], [1]]]
 h' := ![![[21, 42], [29, 40], [26, 40], [17, 35], [10, 21], [0, 1]], ![[0, 1], [9, 3], [6, 3], [21, 8], [21, 22], [21, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [8, 32]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N1 : CertifiedPrimeIdeal' SI43N1 43 where
  n := 2
  hpos := by decide
  P := [33, 22, 1]
  hirr := P43P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-141083, -47721, 161987, 157092, -315577]
  a := ![-29, 11, 29, 41, -60]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-171874, -47721, 161987, 157092, -7339]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N1 B_one_repr
lemma NI43N1 : Nat.card (O ⧸ I43N1) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N1

def I43N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-22, 7, 9, 7, -17]] i)))

def SI43N2: IdealEqSpanCertificate' Table ![![-22, 7, 9, 7, -17]] 
 ![![43, 0, 0, 0, 0], ![35, 1, 0, 0, 0], ![22, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![-22, 7, 9, 7, -17], ![-46, 18, 23, 44, -78], ![288, 143, -372, -310, 664], ![153, -693, 461, -170, -11], ![128, -258, 112, -132, 131]]]
  hmulB := by decide  
  f := ![![![-5452, 3277, 2099, 3841, -9073]], ![![-4906, 2979, 1888, 3449, -8143]], ![![-4400, 2791, 1690, 3064, -7218]], ![![-3211, 2191, 1229, 2198, -5157]], ![![-2144, 1486, 820, 1462, -3427]]]
  g := ![![![-11, 7, 9, 7, -17], ![-30, 18, 23, 44, -78], ![93, 143, -372, -310, 664], ![356, -693, 461, -170, -11], ![168, -258, 112, -132, 131]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N2 : Nat.card (O ⧸ I43N2) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N2)

lemma isPrimeI43N2 : Ideal.IsPrime I43N2 := prime_ideal_of_norm_prime hp43.out _ NI43N2
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![142, 54, -168, -149, 313]] ![![12, 36, -38, -15, 43]]
  ![![226563, -16000, -182326, -243864, 460186]] where
 M := ![![![226563, -16000, -182326, -243864, 460186]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![226563, -16000, -182326, -243864, 460186]] ![![-22, 7, 9, 7, -17]]
  ![![43, 0, 0, 0, 0]] where
 M := ![![![-35165658, 25495087, 8615867, 38115329, -60701165]]]
 hmul := by decide  
 g := ![![![![-817806, 592909, 200369, 886403, -1411655]]]]
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


def P47P0 : CertificateIrreducibleZModOfList' 47 5 2 5 [38, 30, 5, 45, 43, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [35, 11, 12, 7, 17], [28, 31, 44, 34, 11], [35, 39, 20, 29, 41], [0, 12, 18, 24, 25], [0, 1]]
 g := ![![[30, 1, 5, 12, 27], [16, 29, 3, 9, 42], [23, 3, 34, 33, 16], [1], []], ![[30, 14, 2, 7, 44, 41, 11, 28], [23, 26, 31, 2, 19, 24, 46, 28], [29, 12, 24, 25, 12, 37, 23, 3], [33, 20, 12, 19, 9, 8, 7, 14], [35, 31, 31, 7]], ![[9, 14, 39, 15, 30, 34, 0, 15], [1, 4, 21, 23, 43, 31, 30, 31], [33, 38, 17, 13, 43, 46, 4, 41], [2, 45, 9, 3, 44, 41, 2, 45], [23, 9, 10, 27]], ![[27, 11, 36, 16, 25, 9, 32, 10], [3, 41, 20, 24, 13, 13, 7, 40], [32, 1, 16, 22, 40, 5, 14, 23], [22, 31, 19, 16, 24, 20, 26, 22], [2, 45, 31, 36]], ![[0, 13, 28, 15, 36, 21, 30, 1], [25, 39, 7, 18, 8, 25, 9, 21], [7, 5, 22, 30, 41, 30, 3, 42], [3, 23, 20, 4, 27, 17, 43, 14], [32, 42, 34, 14]]]
 h' := ![![[35, 11, 12, 7, 17], [3, 1, 38, 17, 11], [19, 29, 31, 24, 29], [9, 17, 42, 2, 4], [0, 0, 1], [0, 1]], ![[28, 31, 44, 34, 11], [13, 32, 9, 44, 31], [20, 34, 14, 34, 31], [20, 22, 5, 37, 25], [36, 46, 41, 37, 9], [35, 11, 12, 7, 17]], ![[35, 39, 20, 29, 41], [18, 34, 37, 8, 11], [40, 8, 5, 11, 15], [43, 6, 25, 13, 33], [4, 46, 28, 17, 9], [28, 31, 44, 34, 11]], ![[0, 12, 18, 24, 25], [19, 33, 21, 24, 22], [19, 41, 13, 12, 44], [29, 17, 0, 35, 45], [21, 20, 7, 37, 24], [35, 39, 20, 29, 41]], ![[0, 1], [37, 41, 36, 1, 19], [16, 29, 31, 13, 22], [27, 32, 22, 7, 34], [6, 29, 17, 3, 5], [0, 12, 18, 24, 25]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 0, 20, 36], [], [], []]
 b := ![[], [18, 20, 44, 35, 20], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 5
  hpos := by decide
  P := [38, 30, 5, 45, 43, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![464697361947472, -1659758859816778, 1017699497879744, -518928578869684, 185563328177114]
  a := ![83, -1, -76, -85, 170]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![9887177913776, -35314018293974, 21653180805952, -11041033592972, 3948155918662]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-908, 1015, 335, 521, -1167]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-908, 1015, 335, 521, -1167]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![7, 45, 36, 9, 1]] where
  M :=![![![-908, 1015, 335, 521, -1167], ![-1458, 1636, 535, 836, -1874], ![-2368, 2623, 890, 1362, -3064], ![-1309, 1337, 529, 808, -1777], ![-1224, 1308, 474, 728, -1621]]]
  hmulB := by decide  
  f := ![![![-66, 39, 11, 17, -37]], ![![-26, 16, 5, 8, -18]], ![![-24, 13, 10, 14, -32]], ![![-13, 15, 3, 14, -29]], ![![-49, 30, 13, 21, -47]]]
  g := ![![![137, 1010, 799, 208, -1167], ![220, 1622, 1283, 334, -1874], ![360, 2651, 2098, 546, -3064], ![210, 1534, 1217, 317, -1777], ![191, 1401, 1110, 289, -1621]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 4 2 5 [46, 43, 34, 50, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 3, 50, 37], [30, 27, 28, 18], [21, 22, 28, 51], [0, 1]]
 g := ![![[31, 11, 45, 4], [27, 19, 36], [52, 17, 45, 11], [28, 3, 1], []], ![[7, 31, 7, 23, 0, 16], [12, 45, 46], [19, 42, 0, 19, 5, 36], [41, 20, 38], [43, 42, 14, 52, 36, 38]], ![[6, 30, 7, 31, 6, 35], [3, 52, 10], [44, 4, 11, 3, 47, 32], [8, 43, 28], [44, 42, 40, 29, 33, 2]], ![[18, 17, 28, 24, 21, 45], [18, 20, 47], [36, 14, 43, 25, 52, 41], [42, 10, 29], [40, 8, 46, 1, 47, 45]]]
 h' := ![![[5, 3, 50, 37], [26, 10, 48, 2], [46, 47, 3, 47], [37, 36, 39, 45], [0, 0, 0, 1], [0, 1]], ![[30, 27, 28, 18], [44, 5, 35, 30], [15, 21, 45, 29], [26, 0, 49, 45], [2, 48, 26, 41], [5, 3, 50, 37]], ![[21, 22, 28, 51], [10, 23, 38, 23], [25, 0, 44, 40], [13, 28, 25, 34], [13, 17, 17, 44], [30, 27, 28, 18]], ![[0, 1], [10, 15, 38, 51], [19, 38, 14, 43], [30, 42, 46, 35], [1, 41, 10, 20], [21, 22, 28, 51]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [10, 45, 36], []]
 b := ![[], [], [43, 49, 39, 51], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 4
  hpos := by decide
  P := [46, 43, 34, 50, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7355461622762, 16828747155737, -20758920680249, -7716544396992, 23025802569324]
  a := ![213, 9, -193, -208, 436]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2902361440802, -19232686197431, -16031845531621, -4055637123036, 23025802569324]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 7890481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![66, -39, -11, -17, 37]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![66, -39, -11, -17, 37]] 
 ![![53, 0, 0, 0, 0], ![34, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![25, 0, 0, 1, 0], ![22, 0, 0, 0, 1]] where
  M :=![![![66, -39, -11, -17, 37], ![26, -16, -5, -8, 18], ![24, -13, -10, -14, 32], ![13, -15, -3, -14, 29], ![-16, 6, 0, -4, 9]]]
  hmulB := by decide  
  f := ![![![908, -1015, -335, -521, 1167]], ![![610, -682, -225, -350, 784]], ![![216, -241, -80, -124, 278]], ![![453, -504, -168, -261, 584]], ![![400, -446, -148, -230, 515]]]
  g := ![![![21, -39, -11, -17, 37], ![8, -16, -5, -8, 18], ![4, -13, -10, -14, 32], ![5, -15, -3, -14, 29], ![-6, 6, 0, -4, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-908, 1015, 335, 521, -1167]] ![![66, -39, -11, -17, 37]]
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


def P59P0 : CertificateIrreducibleZModOfList' 59 5 2 5 [30, 2, 3, 46, 42, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [18, 44, 41, 14, 7], [55, 54, 27, 33, 55], [54, 32, 38, 38, 57], [8, 46, 12, 33, 58], [0, 1]]
 g := ![![[23, 35, 32, 24, 46], [28, 16, 37, 26, 27], [41, 28, 22, 53], [7, 17, 1], []], ![[29, 27, 49, 20, 45, 24, 29, 22], [57, 20, 21, 47, 17, 35, 54, 15], [3, 47, 4, 1], [58, 15, 55, 7, 26, 25, 4, 15], [25, 51, 40, 11, 38, 35, 42, 48]], ![[58, 2, 50, 33, 40, 7, 22, 42], [37, 13, 27, 41, 58, 40, 1, 11], [11, 18, 45, 35], [13, 2, 31, 13, 50, 10, 17, 38], [4, 27, 8, 55, 2, 17, 24, 54]], ![[35, 49, 45, 16, 32, 57, 5, 7], [5, 2, 10, 26, 35, 54, 35, 4], [48, 22, 33, 3], [36, 20, 2, 21, 52, 57, 8, 29], [19, 53, 37, 8, 14, 19, 25, 51]], ![[27, 57, 46, 30, 8, 45, 24, 55], [2, 20, 40, 32, 28, 35, 30, 13], [23, 32, 38, 21], [48, 10, 18, 58, 8, 12, 22, 38], [7, 25, 27, 27, 14, 38, 23, 58]]]
 h' := ![![[18, 44, 41, 14, 7], [45, 52, 16, 16, 39], [36, 32, 41, 14, 33], [26, 7, 33, 38, 42], [0, 0, 0, 1], [0, 1]], ![[55, 54, 27, 33, 55], [25, 6, 54, 57, 16], [32, 41, 53, 37, 45], [2, 25, 16, 36, 58], [8, 6, 3, 38, 14], [18, 44, 41, 14, 7]], ![[54, 32, 38, 38, 57], [42, 23, 44, 26, 14], [40, 57, 4, 51, 37], [4, 11, 30, 11, 34], [52, 4, 41, 54, 43], [55, 54, 27, 33, 55]], ![[8, 46, 12, 33, 58], [15, 39, 37, 9, 47], [47, 22, 20, 13, 23], [22, 15, 2, 26, 11], [13, 5, 23, 33, 29], [54, 32, 38, 38, 57]], ![[0, 1], [36, 57, 26, 10, 2], [37, 25, 0, 3, 39], [14, 1, 37, 7, 32], [7, 44, 51, 51, 32], [8, 46, 12, 33, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51, 52, 20, 30], [], [], []]
 b := ![[], [56, 23, 19, 28, 21], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 5
  hpos := by decide
  P := [30, 2, 3, 46, 42, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![246807575071878426, 77220654200426858, -279583026116907474, -264555504524214470, 545419123442873394]
  a := ![253, 13, -232, -241, 518]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![4183179238506414, 1308824647464862, -4738695357913686, -4483991602105330, 9244391922760566]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![98, -60, -20, -31, 71]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![98, -60, -20, -31, 71]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![56, 44, 29, 1, 0], ![37, 45, 33, 0, 1]] where
  M :=![![![98, -60, -20, -31, 71], ![118, -55, -58, -78, 174], ![204, -270, 29, -128, 252], ![-227, -110, 248, 360, -551], ![-16, -128, 84, 80, -77]]]
  hmulB := by decide  
  f := ![![![-14724, 16518, 5440, 8453, -18935]], ![![-23674, 26557, 8746, 13590, -30442]], ![![-38060, 42694, 14061, 21848, -48940]], ![![-48995, 54962, 18101, 28126, -63003]], ![![-47290, 53049, 17471, 27147, -60810]]]
  g := ![![![-13, -31, -24, -31, 71], ![-32, -73, -58, -78, 174], ![-32, -98, -75, -128, 252], ![0, 145, 131, 360, -551], ![-27, -3, 5, 80, -77]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [45, 21, 18, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [7, 3, 2], [36, 57, 59], [0, 1]]
 g := ![![[50, 13, 5], [39, 25], [37, 34, 4], [5, 48, 19], [1]], ![[11, 37, 2, 35], [50, 48], [2, 36, 45, 24], [60, 1, 21, 31], [4, 23, 14, 8]], ![[36, 18, 3, 50], [55, 58], [39, 29, 12, 35], [44, 18, 35, 17], [19, 57, 35, 53]]]
 h' := ![![[7, 3, 2], [33, 36, 26], [43, 6, 56], [19, 4, 59], [16, 40, 43], [0, 1]], ![[36, 57, 59], [23, 0, 29], [4, 20, 32], [39, 25, 16], [41, 54, 30], [7, 3, 2]], ![[0, 1], [17, 25, 6], [28, 35, 34], [34, 32, 47], [51, 28, 49], [36, 57, 59]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 39], []]
 b := ![[], [34, 29, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [45, 21, 18, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![41483985, -55963839, 11660085, -44224950, 59165124]
  a := ![67, 8, -61, -58, 137]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![5392977, -12663879, -10791237, -44224950, 59165124]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 226981 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-14724, 16518, 5440, 8453, -18935]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![-14724, 16518, 5440, 8453, -18935]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![8, 3, 1, 0, 0], ![49, 0, 0, 1, 0], ![34, 36, 0, 0, 1]] where
  M :=![![![-14724, 16518, 5440, 8453, -18935], ![-23674, 26557, 8746, 13590, -30442], ![-38060, 42694, 14061, 21848, -48940], ![-18755, 21040, 6928, 10766, -24115], ![-18592, 20856, 6868, 10672, -23905]]]
  hmulB := by decide  
  f := ![![![98, -60, -20, -31, 71]], ![![118, -55, -58, -78, 174]], ![![22, -15, -5, -10, 22]], ![![75, -50, -12, -19, 48]], ![![124, -68, -44, -62, 141]]]
  g := ![![![2809, 11178, 5440, 8453, -18935], ![4516, 17971, 8746, 13590, -30442], ![7260, 28891, 14061, 21848, -48940], ![3577, 14236, 6928, 10766, -24115], ![3546, 14112, 6868, 10672, -23905]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P1 : CertificateIrreducibleZModOfList' 61 2 2 5 [50, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [37, 60], [0, 1]]
 g := ![![[20, 48], [52], [10, 3], [58, 41], [37, 1]], ![[27, 13], [52], [60, 58], [50, 20], [13, 60]]]
 h' := ![![[37, 60], [45, 32], [49, 28], [28, 8], [41, 38], [0, 1]], ![[0, 1], [9, 29], [48, 33], [19, 53], [44, 23], [37, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [22, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N1 : CertifiedPrimeIdeal' SI61N1 61 where
  n := 2
  hpos := by decide
  P := [50, 24, 1]
  hirr := P61P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-45225, -1042210, 927841, 45564, -582516]
  a := ![-287, -5, 258, 282, -588]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![165655, 281063, 927841, 45564, -582516]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N1 B_one_repr
lemma NI61N1 : Nat.card (O ⧸ I61N1) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![98, -60, -20, -31, 71]] ![![-14724, 16518, 5440, 8453, -18935]]
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


lemma PB2009I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB2009I1 : PrimesBelowBoundCertificateInterval O 23 61 2009 where
  m := 9
  g := ![1, 3, 3, 2, 3, 1, 2, 1, 2]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB2009I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0]
    · exact ![I31N0, I31N1, I31N2]
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1, I43N2]
    · exact ![I47N0]
    · exact ![I53N0, I53N1]
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
    · exact ![20511149]
    · exact ![961, 961, 31]
    · exact ![50653, 37, 37]
    · exact ![2825761, 41]
    · exact ![1849, 1849, 43]
    · exact ![229345007]
    · exact ![7890481, 53]
    · exact ![714924299]
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
      exact NI31N2
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
      exact NI43N2
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
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
      exact NI61N1
  β := ![I31N0, I31N1, I31N2, I37N1, I37N2, I41N1, I43N0, I43N1, I43N2, I53N1]
  Il := ![[], [I31N0, I31N1, I31N2], [I37N1, I37N2], [I41N1], [I43N0, I43N1, I43N2], [], [I53N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
