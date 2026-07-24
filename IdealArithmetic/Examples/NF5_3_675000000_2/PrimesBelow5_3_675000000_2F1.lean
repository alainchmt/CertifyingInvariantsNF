
import IdealArithmetic.Examples.NF5_3_675000000_2.RI5_3_675000000_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19177, 6175, 301, -2660, 2116]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![-19177, 6175, 301, -2660, 2116]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![14, 12, 20, 1, 0], ![4, 11, 4, 0, 1]] where
  M :=![![![-19177, 6175, 301, -2660, 2116], ![-27568, -18216, 13611, -3398, -40384], ![309480, -3295, -51804, 41750, 120760], ![-66124, 30405, -3409, -9253, 21988], ![64568, -17094, -2824, 8952, -1125]]]
  hmulB := by decide  
  f := ![![![-296445, -92117, -39705, 85084, 150068]], ![![-860208, -259818, -112217, 243422, 420736]], ![![-2392200, -757135, -325926, 692990, 1238120]], ![![-2158618, -676873, -291565, 622387, 1104764]], ![![-703756, -218050, -94005, 201694, 355011]]]
  g := ![![![331, 511, 1553, -2660, 2116], ![6260, 16096, 8383, -3398, -40384], ![-26140, -63195, -47236, 41750, 120760], ![-846, -3463, 3231, -9253, 21988], ![-1940, -3867, -6116, 8952, -1125]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 3 2 4 [4, 28, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 1, 16], [17, 27, 13], [0, 1]]
 g := ![![[5, 6, 5], [16, 28], [17, 25, 9], [1]], ![[2, 18, 19, 13], [6, 16], [15, 8, 15, 1], [21, 28, 22, 7]], ![[27, 24, 20, 13], [26, 24], [23, 7, 26, 24], [23, 2, 22, 22]]]
 h' := ![![[9, 1, 16], [7, 26, 11], [19, 20, 17], [25, 1, 26], [0, 1]], ![[17, 27, 13], [21, 4, 17], [4, 15, 25], [7, 7, 22], [9, 1, 16]], ![[0, 1], [7, 28, 1], [16, 23, 16], [7, 21, 10], [17, 27, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24, 17], []]
 b := ![[], [12, 8, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 3
  hpos := by decide
  P := [4, 28, 3, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10663226, -419617, 1785297, -12568322, -18290349]
  a := ![-25, -8, 9, -28, -75]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![8957970, 12123934, 11252177, -12568322, -18290349]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 24389 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![296445, 92117, 39705, -85084, -150068]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![296445, 92117, 39705, -85084, -150068]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![14, 3, 1, 0, 0], ![19, 1, 0, 1, 0], ![0, 4, 0, 0, 1]] where
  M :=![![![296445, 92117, 39705, -85084, -150068], ![860208, 259818, 112217, -243422, -420736], ![2392200, 757135, 325926, -692990, -1238120], ![283196, 79163, 34391, -77183, -125972], ![192056, 68444, 29234, -59188, -114471]]]
  hmulB := by decide  
  f := ![![![19177, -6175, -301, 2660, -2116]], ![![27568, 18216, -13611, 3398, 40384]], ![![1438, -983, 233, 196, -1008]], ![![15795, -4466, -549, 2179, -752]], ![![1576, 3102, -1780, 160, 5609]]]
  g := ![![![46799, 22702, 39705, -85084, -150068], ![134972, 63777, 112217, -243422, -420736], ![379174, 187063, 325926, -692990, -1238120], ![43731, 19209, 34391, -77183, -125972], ![31288, 17166, 29234, -59188, -114471]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P1 : CertificateIrreducibleZModOfList' 29 2 2 4 [19, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [23, 28], [0, 1]]
 g := ![![[11, 23], [5], [25, 28], [23, 1]], ![[18, 6], [5], [2, 1], [17, 28]]]
 h' := ![![[23, 28], [26, 9], [18, 18], [27, 17], [0, 1]], ![[0, 1], [1, 20], [26, 11], [12, 12], [23, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [19, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N1 : CertifiedPrimeIdeal' SI29N1 29 where
  n := 2
  hpos := by decide
  P := [19, 6, 1]
  hirr := P29P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-309394, -96784, -142508, 893820, 1555440]
  a := ![-169, -58, 56, -170, -510]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-527478, -233960, -142508, 893820, 1555440]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N1 B_one_repr
lemma NI29N1 : Nat.card (O ⧸ I29N1) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![-19177, 6175, 301, -2660, 2116]] ![![296445, 92117, 39705, -85084, -150068]]
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


def P31P0 : CertificateIrreducibleZModOfList' 31 5 2 4 [8, 8, 5, 8, 25, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 1, 27, 8, 7], [28, 12, 2, 15, 4], [30, 20, 12, 5, 19], [30, 28, 21, 3, 1], [0, 1]]
 g := ![![[18, 27, 18, 25, 19], [17, 26, 2, 25, 19], [28, 6, 1], []], ![[4, 3, 28, 26, 29, 14, 18, 2], [8, 4, 16, 22, 3, 2, 27, 18], [22, 25, 24, 24, 8, 12, 22, 16], [28, 14, 20, 16, 26, 25, 10, 2]], ![[18, 3, 8, 19, 16, 10, 22, 16], [0, 12, 29, 24, 25, 16, 26, 1], [11, 18, 26, 14, 10, 18, 2, 4], [14, 14, 7, 27, 18, 11, 19, 2]], ![[19, 25, 22, 9, 3, 0, 25, 9], [3, 7, 0, 21, 8, 25, 2, 16], [9, 11, 8, 7, 14, 6, 16, 9], [24, 21, 21, 22, 6, 15, 7, 8]], ![[24, 19, 12, 3, 8, 2, 2, 9], [18, 20, 27, 22, 22, 6, 25, 1], [9, 28, 26, 27, 20, 18, 6, 9], [16, 0, 2, 8, 1, 17, 15, 1]]]
 h' := ![![[11, 1, 27, 8, 7], [19, 15, 27, 17, 22], [24, 7, 21, 17, 22], [0, 0, 0, 1], [0, 1]], ![[28, 12, 2, 15, 4], [11, 14, 6, 9, 24], [2, 1, 4, 26, 21], [22, 27, 29, 13, 12], [11, 1, 27, 8, 7]], ![[30, 20, 12, 5, 19], [2, 9, 29, 20, 29], [12, 29, 18, 25, 15], [16, 7, 8, 7, 1], [28, 12, 2, 15, 4]], ![[30, 28, 21, 3, 1], [29, 13, 18, 8, 21], [3, 30, 14, 17, 3], [24, 10, 23, 13, 21], [30, 20, 12, 5, 19]], ![[0, 1], [26, 11, 13, 8, 28], [27, 26, 5, 8, 1], [26, 18, 2, 28, 28], [30, 28, 21, 3, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19, 20, 26, 12], [], [], []]
 b := ![[], [6, 28, 8, 6, 16], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 5
  hpos := by decide
  P := [8, 8, 5, 8, 25, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![305190547346, -24686822720, 33524224848, -278938121334, -365871321452]
  a := ![-14, -5, 5, -16, -43]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![9844856366, -796349120, 1081426608, -8998003914, -11802300692]
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

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1407, 457, -465, 182, 1305]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![1407, 457, -465, 182, 1305]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![9, 2, 7, 1, 0], ![25, 13, 0, 0, 1]] where
  M :=![![![1407, 457, -465, 182, 1305], ![-9712, 569, 1398, -1312, -3036], ![19040, -7070, 157, 2660, -3600], ![8800, 1604, -2298, 1157, 6150], ![-3134, -1528, 1284, -398, -3725]]]
  hmulB := by decide  
  f := ![![![357, 85, 39, -100, -147]], ![![776, 305, 138, -304, -612]], ![![3680, 550, 301, -1060, -1200]], ![![829, 145, 76, -247, -309]], ![![531, 164, 75, -178, -314]]]
  g := ![![![-888, -456, -47, 182, 1305], ![2108, 1153, 286, -1312, -3036], ![2300, 930, -499, 2660, -3600], ![-4199, -2180, -281, 1157, 6150], ![2529, 1289, 110, -398, -3725]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [3, 26, 31, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 16, 8], [18, 20, 29], [0, 1]]
 g := ![![[4, 30, 34], [34, 9], [33, 10, 26], [6, 1], []], ![[21, 13, 17, 8], [19, 34], [35, 35, 2, 8], [36, 30], [11, 27]], ![[24, 5, 35, 13], [3, 21], [28, 21, 7, 31], [1, 34], [27, 27]]]
 h' := ![![[25, 16, 8], [5, 20, 16], [12, 28, 34], [19, 26, 10], [0, 0, 1], [0, 1]], ![[18, 20, 29], [24, 33, 36], [9, 0, 16], [3, 10, 1], [0, 26, 20], [25, 16, 8]], ![[0, 1], [35, 21, 22], [9, 9, 24], [31, 1, 26], [21, 11, 16], [18, 20, 29]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 29], []]
 b := ![[], [4, 24, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [3, 26, 31, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-309698447, -7994662, -80435846, 493207538, 785530228]
  a := ![90, 27, -31, 89, 269]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-659103297, -302873046, -95483476, 493207538, 785530228]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 50653 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-35, 12, 8, -12, -19]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-35, 12, 8, -12, -19]] 
 ![![37, 0, 0, 0, 0], ![20, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![13, 0, 0, 1, 0], ![17, 0, 0, 0, 1]] where
  M :=![![![-35, 12, 8, -12, -19], ![104, -26, 17, -6, -68], ![520, 115, -82, 10, 200], ![-208, 45, 21, -35, -34], ![170, -12, -18, 18, 33]]]
  hmulB := by decide  
  f := ![![![-825, 144, 6, 318, 113]], ![![-436, 68, -7, 214, 152]], ![![-715, 119, -2, 308, 163]], ![![-309, 37, -19, 215, 235]], ![![-555, 100, 8, 196, 40]]]
  g := ![![![4, 12, 8, -12, -19], ![47, -26, 17, -6, -68], ![-128, 115, -82, 10, 200], ![-6, 45, 21, -35, -34], ![-7, -12, -18, 18, 33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1135, 517, 405, -1348, -3436]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![-1135, 517, 405, -1348, -3436]] 
 ![![37, 0, 0, 0, 0], ![21, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![35, 0, 0, 1, 0], ![31, 0, 0, 0, 1]] where
  M :=![![![-1135, 517, 405, -1348, -3436], ![22096, -3894, -223, -8214, -2432], ![-13400, 10335, 10102, -39950, -88840], ![44044, -7221, 251, -19539, -11188], ![-17432, 5496, 3206, -7180, -25539]]]
  hmulB := by decide  
  f := ![![![-59523, -55943, 37487, -7156, -113932]], ![![-9923, -31567, 17072, -862, -54668]], ![![-71997, 11498, 6821, -9834, -10828]], ![![-70665, -58922, 40858, -8607, -123240]], ![![-48033, -42099, 28769, -5820, -87055]]]
  g := ![![![3797, 517, 405, -1348, -3436], ![12633, -3894, -223, -8214, -2432], ![105177, 10335, 10102, -39950, -88840], ![33125, -7221, 251, -19539, -11188], ![24339, 5496, 3206, -7180, -25539]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![1407, 457, -465, 182, 1305]] ![![-35, 12, 8, -12, -19]]
  ![![-59523, -55943, 37487, -7156, -113932]] where
 M := ![![![-59523, -55943, 37487, -7156, -113932]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![-59523, -55943, 37487, -7156, -113932]] ![![-1135, 517, 405, -1348, -3436]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1373, -360, -62, 190, -18]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![1373, -360, -62, 190, -18]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![35, 6, 1, 0, 0], ![20, 25, 0, 1, 0], ![12, 40, 0, 0, 1]] where
  M :=![![![1373, -360, -62, 190, -18], ![904, 1235, -758, 104, 2352], ![-18400, -430, 3379, -2460, -8160], ![5092, -1830, 12, 711, -864], ![-4484, 972, 300, -616, -263]]]
  hmulB := by decide  
  f := ![![![2349, -576, -222, 14, 1530]], ![![-12184, 2783, 926, 896, -5952]], ![![1471, -392, -175, 166, 1278]], ![![-6800, 1533, 494, 599, -3120]], ![![-10640, 2412, 788, 872, -5015]]]
  g := ![![![-1, -98, -62, 190, -18], ![-70, -2217, -758, 104, 2352], ![255, 8956, 3379, -2460, -8160], ![20, 363, 12, 711, -864], ![12, 612, 300, -616, -263]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [39, 31, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 40], [0, 1]]
 g := ![![[5, 20], [9], [20], [15, 18], [1]], ![[0, 21], [9], [20], [31, 23], [1]]]
 h' := ![![[10, 40], [27, 26], [38, 38], [30, 26], [2, 10], [0, 1]], ![[0, 1], [0, 15], [8, 3], [3, 15], [20, 31], [10, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [13, 22]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [39, 31, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1037, -7587, -4977, 27032, 53818]
  a := ![-37, -7, 14, -32, -110]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-24664, -68445, -4977, 27032, 53818]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-451, -139, -61, 130, 229]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-451, -139, -61, 130, 229]] 
 ![![41, 0, 0, 0, 0], ![14, 1, 0, 0, 0], ![9, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-451, -139, -61, 130, 229], ![-1312, -397, -170, 368, 644], ![-3680, -1150, -489, 1060, 1840], ![-392, -124, -58, 119, 214], ![-326, -100, -40, 90, 153]]]
  hmulB := by decide  
  f := ![![![387, -67, -1, -156, -67]], ![![130, -19, 4, -72, -62]], ![![323, -53, 2, -144, -83]], ![![59, -3, 9, -65, -93]], ![![74, -14, -2, -22, 3]]]
  g := ![![![34, -139, -61, 130, 229], ![96, -397, -170, 368, 644], ![281, -1150, -489, 1060, 1840], ![31, -124, -58, 119, 214], ![24, -100, -40, 90, 153]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-115, 1, 19, -14, -43]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![-115, 1, 19, -14, -43]] 
 ![![41, 0, 0, 0, 0], ![24, 1, 0, 0, 0], ![39, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![23, 0, 0, 0, 1]] where
  M :=![![![-115, 1, 19, -14, -43], ![288, -77, -14, 48, 4], ![160, 270, -169, 60, 560], ![-568, 32, 78, -57, -154], ![314, 8, -60, 50, 153]]]
  hmulB := by decide  
  f := ![![![518707, 159457, 68783, -148076, -259187]], ![![339760, 104447, 45054, -96992, -169772]], ![![596573, 183393, 79108, -170304, -298093]], ![![24047, 7393, 3189, -6865, -12017]], ![![299863, 92181, 39763, -85602, -149834]]]
  g := ![![![3, 1, 19, -14, -43], ![62, -77, -14, 48, 4], ![-309, 270, -169, 60, 560], ![-19, 32, 78, -57, -154], ![-27, 8, -60, 50, 153]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2

def I41N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7863, -1562, 2116, -1032, -5702]] i)))

def SI41N3: IdealEqSpanCertificate' Table ![![-7863, -1562, 2116, -1032, -5702]] 
 ![![41, 0, 0, 0, 0], ![38, 1, 0, 0, 0], ![32, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![19, 0, 0, 0, 1]] where
  M :=![![![-7863, -1562, 2116, -1032, -5702], ![41488, -4017, -5200, 5628, 10424], ![-60880, 31540, -4849, -8640, 25840], ![-44872, -4784, 10066, -5951, -25916], ![19268, 5506, -6002, 2504, 16665]]]
  hmulB := by decide  
  f := ![![![-26711, 2626, -2312, 21536, 26294]], ![![-27786, 2667, -2488, 22780, 28108]], ![![-39472, 3852, -3473, 32112, 39408]], ![![-12033, 1054, -1214, 10497, 13430]], ![![-16209, 1624, -1370, 12928, 15667]]]
  g := ![![![2423, -1562, 2116, -1032, -5702], ![3002, -4017, -5200, 5628, 10424], ![-37432, 31540, -4849, -8640, 25840], ![8509, -4784, 10066, -5951, -25916], ![-8099, 5506, -6002, 2504, 16665]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N3 : Nat.card (O ⧸ I41N3) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N3)

lemma isPrimeI41N3 : Ideal.IsPrime I41N3 := prime_ideal_of_norm_prime hp41.out _ NI41N3
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![1373, -360, -62, 190, -18]] ![![-451, -139, -61, 130, 229]]
  ![![12645, 1613, -2535, 1280, 6403]] where
 M := ![![![12645, 1613, -2535, 1280, 6403]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![12645, 1613, -2535, 1280, 6403]] ![![-115, 1, 19, -14, -43]]
  ![![-111729, -703822, 361748, -4516, -1174344]] where
 M := ![![![-111729, -703822, 361748, -4516, -1174344]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI41N2 : IdealMulLeCertificate' Table 
  ![![-111729, -703822, 361748, -4516, -1174344]] ![![-7863, -1562, 2116, -1032, -5702]]
  ![![41, 0, 0, 0, 0]] where
 M := ![![![-72769478489, 7966972072, 8672294416, -9884991268, -16805399554]]]
 hmul := by decide  
 g := ![![![![-1774865329, 194316392, 211519376, -241097348, -409887794]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2233, -632, -254, 574, 992]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![-2233, -632, -254, 574, 992]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![1, 14, 22, 1, 0], ![39, 6, 6, 0, 1]] where
  M :=![![![-2233, -632, -254, 574, 992], ![-5640, -1937, -788, 1740, 2920], ![-16400, -4920, -2497, 4920, 9200], ![-2572, -508, -162, 441, 764], ![-1024, -460, -264, 476, 891]]]
  hmulB := by decide  
  f := ![![![-2587, 224, -266, 2282, 2936]], ![![-14360, 1301, -1404, 12340, 15640]], ![![-75760, 6600, -7739, 66600, 85520]], ![![-44301, 3878, -4502, 38839, 49796]], ![![-15255, 1334, -1552, 13382, 17163]]]
  g := ![![![-965, -340, -438, 574, 992], ![-2820, -1019, -1316, 1740, 2920], ![-8840, -3000, -3859, 4920, 9200], ![-763, -262, -336, 441, 764], ![-843, -290, -374, 476, 891]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [37, 39, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 33, 5], [22, 9, 38], [0, 1]]
 g := ![![[10, 5, 11], [6, 30, 15], [4, 16], [20, 39, 1], []], ![[26, 20, 8, 28], [10, 32, 32, 28], [35, 24], [17, 29, 17, 18], [15, 25]], ![[31, 20, 33, 24], [15, 2, 23, 38], [20, 23], [4, 30, 33, 16], [25, 25]]]
 h' := ![![[17, 33, 5], [36, 6, 22], [19, 7, 31], [34, 13, 39], [0, 0, 1], [0, 1]], ![[22, 9, 38], [5, 4, 13], [19, 28, 13], [29, 3, 29], [35, 42, 9], [17, 33, 5]], ![[0, 1], [12, 33, 8], [4, 8, 42], [20, 27, 18], [32, 1, 33], [22, 9, 38]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26, 2], []]
 b := ![[], [32, 25, 34], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [37, 39, 4, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![24246873, -5790230, -2676350, 1326334, 18405948]
  a := ![28, -2, -10, 10, 84]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-16160731, -3134758, -3309102, 1326334, 18405948]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 79507 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, -1, -1, 2, 6]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![5, -1, -1, 2, 6]] 
 ![![43, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![42, 0, 1, 0, 0], ![34, 0, 0, 1, 0], ![11, 0, 0, 0, 1]] where
  M :=![![![5, -1, -1, 2, 6], ![-40, 8, 1, 10, 0], ![40, -25, -12, 50, 120], ![-56, 11, -1, 27, 12], ![28, -10, -4, 8, 37]]]
  hmulB := by decide  
  f := ![![![6567, 2017, 871, -1874, -3282]], ![![589, 181, 78, -168, -294]], ![![7658, 2353, 1016, -2186, -3828]], ![![5330, 1637, 707, -1521, -2664]], ![![1787, 549, 237, -510, -893]]]
  g := ![![![-2, -1, -1, 2, 6], ![-10, 8, 1, 10, 0], ![-57, -25, -12, 50, 120], ![-25, 11, -1, 27, 12], ![-11, -10, -4, 8, 37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1

def I43N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![87, -7, 9, -76, -98]] i)))

def SI43N2: IdealEqSpanCertificate' Table ![![87, -7, 9, -76, -98]] 
 ![![43, 0, 0, 0, 0], ![37, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![33, 0, 0, 1, 0], ![29, 0, 0, 0, 1]] where
  M :=![![![87, -7, 9, -76, -98], ![480, -42, 47, -410, -520], ![2520, -215, 258, -2210, -2840], ![1148, -103, 113, -989, -1256], ![476, -40, 50, -424, -549]]]
  hmulB := by decide  
  f := ![![![413, 79, -107, 52, 286]], ![![307, 73, -86, 38, 234]], ![![137, -24, -11, 18, 14]], ![![371, 66, -94, 47, 250]], ![![255, 47, -65, 32, 173]]]
  g := ![![![131, -7, 9, -76, -98], ![705, -42, 47, -410, -520], ![3813, -215, 258, -2210, -2840], ![1703, -103, 113, -989, -1256], ![733, -40, 50, -424, -549]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N2 : Nat.card (O ⧸ I43N2) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N2)

lemma isPrimeI43N2 : Ideal.IsPrime I43N2 := prime_ideal_of_norm_prime hp43.out _ NI43N2
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![-2233, -632, -254, 574, 992]] ![![5, -1, -1, 2, 6]]
  ![![-413, -79, 107, -52, -286]] where
 M := ![![![-413, -79, 107, -52, -286]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![-413, -79, 107, -52, -286]] ![![87, -7, 9, -76, -98]]
  ![![43, 0, 0, 0, 0]] where
 M := ![![![-43, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-285561, 25337, -28593, 248428, 317115]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-285561, 25337, -28593, 248428, 317115]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![41, 18, 1, 0, 0], ![39, 38, 0, 1, 0], ![21, 15, 0, 0, 1]] where
  M :=![![![-285561, 25337, -28593, 248428, 317115], ![-1543208, 137017, -154404, 1342012, 1712676], ![-8333360, 739460, -834331, 7249360, 9253440], ![-3731404, 331270, -373380, 3245095, 4141518], ![-1600618, 141982, -160314, 1392686, 1777895]]]
  hmulB := by decide  
  f := ![![![1287, 91, 537, -562, -1803]], ![![12176, 1607, -588, -484, 468]], ![![5665, 891, 308, -822, -1557]], ![![10855, 1347, 9, -879, -1233]], ![![4499, 592, 39, -412, -616]]]
  g := ![![![-328965, -290574, -28593, 248428, 317115], ![-1776964, -1569581, -154404, 1342012, 1712676], ![-9599427, -8479146, -834331, 7249360, 9253440], ![-4296881, -3795410, -373380, 3245095, 4141518], ![-1844219, -1628997, -160314, 1392686, 1777895]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [34, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 46], [0, 1]]
 g := ![![[20, 18], [3, 1], [37, 42], [13, 14], [1]], ![[0, 29], [28, 46], [6, 5], [34, 33], [1]]]
 h' := ![![[25, 46], [39, 21], [11, 46], [28, 18], [13, 25], [0, 1]], ![[0, 1], [0, 26], [33, 1], [8, 29], [27, 22], [25, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [31, 37]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [34, 22, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3614, 812, -479, 4115, 5332]
  a := ![10, 7, -2, 13, 17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5456, -4828, -479, 4115, 5332]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-25289, 5980, 2148, 886, -14346]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-25289, 5980, 2148, 886, -14346]] 
 ![![47, 0, 0, 0, 0], ![13, 1, 0, 0, 0], ![19, 0, 1, 0, 0], ![44, 0, 0, 1, 0], ![38, 0, 0, 0, 1]] where
  M :=![![![-25289, 5980, 2148, 886, -14346], ![118312, -28009, -10138, -3668, 68016], ![-558800, 131970, 47343, 19980, -316080], ![201700, -47814, -17338, -6047, 116400], ![-241412, 57054, 20522, 8292, -137213]]]
  hmulB := by decide  
  f := ![![![-160071, -28836, 41636, -21054, -111330]], ![![-27117, -9769, 9430, -3494, -26694]], ![![-88187, 1498, 14479, -11858, -33450]], ![![-169016, -28802, 43162, -22255, -114912]], ![![-120962, -21122, 31138, -15920, -83057]]]
  g := ![![![7709, 5980, 2148, 886, -14346], ![-37195, -28009, -10138, -3668, 68016], ![169319, 131970, 47343, 19980, -316080], ![-63924, -47814, -17338, -6047, 116400], ![73962, 57054, 20522, 8292, -137213]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1

def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1679, -399, -147, -36, 996]] i)))

def SI47N2: IdealEqSpanCertificate' Table ![![1679, -399, -147, -36, 996]] 
 ![![47, 0, 0, 0, 0], ![30, 1, 0, 0, 0], ![40, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![11, 0, 0, 0, 1]] where
  M :=![![![1679, -399, -147, -36, 996], ![-8112, 1904, 669, 378, -4416], ![36840, -8805, -3268, -630, 22200], ![-13956, 3255, 1131, 731, -7428], ![16104, -3828, -1398, -420, 9419]]]
  hmulB := by decide  
  f := ![![![-4055, 4479, -1479, -612, 5532]], ![![-3582, 2720, -705, -522, 2904]], ![![1040, 3255, -1762, 90, 5640]], ![![-522, 993, -393, -85, 1380]], ![![-539, 765, -279, -84, 1007]]]
  g := ![![![187, -399, -147, -36, 996], ![-972, 1904, 669, 378, -4416], ![4070, -8805, -3268, -630, 22200], ![-1692, 3255, 1131, 731, -7428], ![1825, -3828, -1398, -420, 9419]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N2 : Nat.card (O ⧸ I47N2) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N2)

lemma isPrimeI47N2 : Ideal.IsPrime I47N2 := prime_ideal_of_norm_prime hp47.out _ NI47N2

def I47N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-20191, -6206, -2678, 5764, 10091]] i)))

def SI47N3: IdealEqSpanCertificate' Table ![![-20191, -6206, -2678, 5764, 10091]] 
 ![![47, 0, 0, 0, 0], ![33, 1, 0, 0, 0], ![39, 0, 1, 0, 0], ![24, 0, 0, 1, 0], ![28, 0, 0, 0, 1]] where
  M :=![![![-20191, -6206, -2678, 5764, 10091], ![-57672, -17726, -7643, 16458, 28804], ![-164600, -50625, -21838, 47010, 82280], ![-18184, -5587, -2415, 5193, 9098], ![-14170, -4360, -1878, 4046, 7077]]]
  hmulB := by decide  
  f := ![![![3217, -422, 152, -2030, -2027]], ![![2431, -298, 141, -1652, -1769]], ![![4529, -579, 232, -2940, -3019]], ![![2124, -235, 155, -1587, -1834]], ![![2378, -320, 102, -1454, -1405]]]
  g := ![![![-2805, -6206, -2678, 5764, 10091], ![-8003, -17726, -7643, 16458, 28804], ![-22859, -50625, -21838, 47010, 82280], ![-2532, -5587, -2415, 5193, 9098], ![-1964, -4360, -1878, 4046, 7077]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N3 : Nat.card (O ⧸ I47N3) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N3)

lemma isPrimeI47N3 : Ideal.IsPrime I47N3 := prime_ideal_of_norm_prime hp47.out _ NI47N3
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-285561, 25337, -28593, 248428, 317115]] ![![-25289, 5980, 2148, 886, -14346]]
  ![![-250447107, 23605795, -23340567, 210042162, 262373643]] where
 M := ![![![-250447107, 23605795, -23340567, 210042162, 262373643]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![-250447107, 23605795, -23340567, 210042162, 262373643]] ![![1679, -399, -147, -36, 996]]
  ![![-177940655973, 29708453714, -355693152, 75987533934, 39255067389]] where
 M := ![![![-177940655973, 29708453714, -355693152, 75987533934, 39255067389]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI47N2 : IdealMulLeCertificate' Table 
  ![![-177940655973, 29708453714, -355693152, 75987533934, 39255067389]] ![![-20191, -6206, -2678, 5764, 10091]]
  ![![47, 0, 0, 0, 0]] where
 M := ![![![-686981751, 180348776, 81005816, -78503724, -595548562]]]
 hmul := by decide  
 g := ![![![![-14616633, 3837208, 1723528, -1670292, -12671246]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1, I47N2, I47N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
    exact isPrimeI47N2
    exact isPrimeI47N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0 ⊙ MulI47N1 ⊙ MulI47N2)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9545, -2566, -398, 1322, -232]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![9545, -2566, -398, 1322, -232]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![13, 17, 4, 24, 1]] where
  M :=![![![9545, -2566, -398, 1322, -232], ![7144, 8645, -5442, 844, 16792], ![-130960, -2430, 23749, -17460, -57040], ![35076, -12994, 266, 4935, -6532], ![-31296, 6962, 2006, -4288, -1539]]]
  hmulB := by decide  
  f := ![![![197557, 60734, 26198, -56398, -98720]], ![![564168, 173429, 74810, -161052, -281896]], ![![1610960, 495270, 213637, -459900, -805040]], ![![177988, 54706, 23598, -50805, -88916]], ![![434213, 133481, 57578, -123954, -216963]]]
  g := ![![![237, 26, 10, 130, -232], ![-3984, -5223, -1370, -7588, 16792], ![11520, 18250, 4753, 25500, -57040], ![2264, 1850, 498, 3051, -6532], ![-213, 625, 154, 616, -1539]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 4 2 5 [13, 48, 22, 5, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [34, 29, 14, 47], [12, 19, 24, 49], [2, 4, 15, 10], [0, 1]]
 g := ![![[30, 17, 35, 44], [46, 4, 47], [33, 14, 8, 36], [3, 48, 1], []], ![[26, 17, 23, 32, 16, 25], [30, 32, 52], [40, 41, 20, 7, 20, 38], [4, 1, 24], [33, 20, 36, 35, 48, 49]], ![[13, 39, 29, 16, 36, 6], [46, 4, 47], [2, 11, 8, 30, 4, 11], [47, 42, 9], [23, 32, 37, 26, 41, 42]], ![[5, 44, 34, 12, 39, 16], [30, 32, 52], [22, 46, 42, 10, 39, 47], [47, 41, 43], [10, 36, 23, 4, 30, 46]]]
 h' := ![![[34, 29, 14, 47], [10, 31, 3, 16], [48, 20, 49, 43], [14, 27, 2, 47], [0, 0, 0, 1], [0, 1]], ![[12, 19, 24, 49], [33, 33, 45, 26], [30, 20, 34, 23], [41, 18, 46, 33], [26, 42, 51, 36], [34, 29, 14, 47]], ![[2, 4, 15, 10], [1, 20, 37, 48], [49, 33, 4, 10], [29, 20, 12, 39], [51, 10, 12, 50], [12, 19, 24, 49]], ![[0, 1], [18, 22, 21, 16], [14, 33, 19, 30], [16, 41, 46, 40], [37, 1, 43, 19], [2, 4, 15, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [31, 41, 38], []]
 b := ![[], [], [46, 32, 22, 36], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 4
  hpos := by decide
  P := [13, 48, 22, 5, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![660953, -158850, -58776, -10382, 400826]
  a := ![2, -1, -1, 1, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-85845, -131564, -31360, -181702, 400826]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 7890481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-197557, -60734, -26198, 56398, 98720]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-197557, -60734, -26198, 56398, 98720]] 
 ![![53, 0, 0, 0, 0], ![34, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![37, 0, 0, 0, 1]] where
  M :=![![![-197557, -60734, -26198, 56398, 98720], ![-564168, -173429, -74810, 161052, 281896], ![-1610960, -495270, -213637, 459900, 805040], ![-177988, -54706, -23598, 50805, 88916], ![-138640, -42634, -18390, 39584, 69303]]]
  hmulB := by decide  
  f := ![![![-9545, 2566, 398, -1322, 232]], ![![-6258, 1483, 358, -864, -168]], ![![670, 530, -373, 80, 1120]], ![![-1022, 342, 10, -143, 132]], ![![-6073, 1660, 240, -842, 191]]]
  g := ![![![-30869, -60734, -26198, 56398, 98720], ![-88146, -173429, -74810, 161052, 281896], ![-251730, -495270, -213637, 459900, 805040], ![-27802, -54706, -23598, 50805, 88916], ![-21671, -42634, -18390, 39584, 69303]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![9545, -2566, -398, 1322, -232]] ![![-197557, -60734, -26198, 56398, 98720]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1479, -312, -124, 222, 165]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![1479, -312, -124, 222, 165]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![39, 26, 30, 11, 1]] where
  M :=![![![1479, -312, -124, 222, 165], ![-432, 1246, -591, -22, 2004], ![-16120, -1405, 3294, -1990, -8280], ![6044, -1615, -275, 853, -78], ![-4822, 758, 448, -646, -697]]]
  hmulB := by decide  
  f := ![![![-1133, 100, -114, 988, 1263]], ![![-6152, 548, -613, 5338, 6804]], ![![-33080, 2925, -3324, 28830, 36840]], ![![-14864, 1323, -1483, 12907, 16458]], ![![-23159, 2051, -2323, 20165, 25754]]]
  g := ![![![-84, -78, -86, -27, 165], ![-1332, -862, -1029, -374, 2004], ![5200, 3625, 4266, 1510, -8280], ![154, 7, 35, 29, -78], ![379, 320, 362, 119, -697]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 4 2 5 [54, 36, 48, 52, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [21, 56, 35, 40], [35, 26, 17, 57], [10, 35, 7, 21], [0, 1]]
 g := ![![[16, 6, 20, 7], [31, 40, 3, 12], [10, 52, 29], [48, 1, 7, 1], []], ![[17, 55, 19, 11, 40, 58], [23, 31, 14, 33, 28, 14], [33, 54, 16], [22, 26, 56, 56, 21, 18], [31, 37, 30, 24, 40, 44]], ![[58, 0, 20, 43, 2, 46], [35, 28, 39, 26, 14, 19], [3, 3, 27], [37, 25, 17, 49, 26, 45], [42, 3, 43, 57, 30, 51]], ![[27, 8, 4, 53, 23, 27], [57, 44, 8, 1, 36, 36], [5, 32, 7], [21, 44, 26, 19, 28, 5], [13, 46, 40, 52, 43, 57]]]
 h' := ![![[21, 56, 35, 40], [37, 18, 7, 19], [7, 40, 29, 22], [4, 47, 55, 41], [0, 0, 0, 1], [0, 1]], ![[35, 26, 17, 57], [13, 58, 32, 21], [37, 0, 35, 27], [52, 44, 37, 4], [35, 56, 11, 33], [21, 56, 35, 40]], ![[10, 35, 7, 21], [13, 13, 30, 53], [13, 56, 38, 43], [36, 16, 24, 33], [15, 7, 35, 40], [35, 26, 17, 57]], ![[0, 1], [4, 29, 49, 25], [54, 22, 16, 26], [18, 11, 2, 40], [3, 55, 13, 44], [10, 35, 7, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [29, 34, 11], []]
 b := ![[], [], [48, 52, 40, 35], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 4
  hpos := by decide
  P := [54, 36, 48, 52, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-84458171729, 2866430076, -14308284604, 99876136200, 146932731240]
  a := ![51, 13, -17, 50, 150]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-98556520171, -64701433596, -74954071556, -25701422160, 146932731240]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 12117361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1133, -100, 114, -988, -1263]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![1133, -100, 114, -988, -1263]] 
 ![![59, 0, 0, 0, 0], ![49, 1, 0, 0, 0], ![18, 0, 1, 0, 0], ![23, 0, 0, 1, 0], ![55, 0, 0, 0, 1]] where
  M :=![![![1133, -100, 114, -988, -1263], ![6152, -548, 613, -5338, -6804], ![33080, -2925, 3324, -28830, -36840], ![14864, -1323, 1483, -12907, -16458], ![6338, -558, 640, -5538, -7087]]]
  hmulB := by decide  
  f := ![![![-1479, 312, 124, -222, -165]], ![![-1221, 238, 113, -184, -171]], ![![-178, 119, -18, -34, 90]], ![![-679, 149, 53, -101, -63]], ![![-1297, 278, 108, -196, -142]]]
  g := ![![![1630, -100, 114, -988, -1263], ![8796, -548, 613, -5338, -6804], ![47557, -2925, 3324, -28830, -36840], ![21272, -1323, 1483, -12907, -16458], ![9141, -558, 640, -5538, -7087]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![1479, -312, -124, 222, 165]] ![![1133, -100, 114, -988, -1263]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2780455, 901593, 40771, -386588, 315753]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![-2780455, 901593, 40771, -386588, 315753]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![16, 22, 55, 1, 0], ![14, 5, 55, 0, 1]] where
  M :=![![![-2780455, 901593, 40771, -386588, 315753], ![-4072376, -2647435, 1990522, -507136, -5902068], ![45188000, -528970, -7535231, 6072540, 17522640], ![-9552908, 4434420, -510402, -1348119, 3229026], ![9379762, -2498214, -401898, 1296050, -193775]]]
  hmulB := by decide  
  f := ![![![-13646853, -4188819, -1807077, 3892822, 6806469]], ![![-38880464, -11982947, -5167994, 11113456, 19487988]], ![![-111450080, -34118990, -14721871, 31749860, 55409520]], ![![-118289536, -36245720, -15638507, 33713553, 58874670]], ![![-106965516, -32754391, -14132809, 30476146, 53196253]]]
  g := ![![![-16649, 128324, 64536, -386588, 315753], ![1420832, 623277, 5811422, -507136, -5902068], ![-4873600, -3635050, -21397871, 6072540, 17522640], ![-544088, 294228, -1704267, -1348119, 3229026], ![-141708, -492499, -1000443, 1296050, -193775]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [31, 26, 44, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [23, 21, 41], [55, 39, 20], [0, 1]]
 g := ![![[15, 22, 49], [25, 27], [59, 56, 25], [28, 3, 45], [1]], ![[8, 17, 44, 14], [4, 48], [59, 47, 47, 47], [37, 4, 1, 9], [41, 51, 37, 52]], ![[45, 19, 39, 60], [13, 3], [43, 23, 57, 27], [41, 6, 35, 9], [36, 28, 44, 9]]]
 h' := ![![[23, 21, 41], [19, 51, 7], [1, 37, 37], [47, 18, 5], [30, 35, 17], [0, 1]], ![[55, 39, 20], [17, 10, 46], [18, 14, 32], [40, 21, 18], [38, 58, 24], [23, 21, 41]], ![[0, 1], [46, 0, 8], [49, 10, 53], [20, 22, 38], [10, 29, 20], [55, 39, 20]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59, 22], []]
 b := ![[], [16, 25, 56], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [31, 26, 44, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1544443, -718122, -1266388, 6411421, 11732810]
  a := ![24, 5, -9, 21, 71]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4399779, -3285794, -16380313, 6411421, 11732810]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 226981 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0, 1]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![3, 0, 0, 0, 1]] 
 ![![61, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![12, 0, 1, 0, 0], ![43, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![3, 0, 0, 0, 1], ![-8, 4, 1, 2, -4], ![40, -5, -4, 10, 40], ![-24, 5, 1, 7, -2], ![18, -4, -2, 2, 15]]]
  hmulB := by decide  
  f := ![![![65, 12, -14, 6, 37]], ![![3, 2, -1, 0, 3]], ![![20, -1, -2, 2, 4]], ![![51, 9, -11, 5, 29]], ![![1, 0, 0, 0, 0]]]
  g := ![![![0, 0, 0, 0, 1], ![-2, 4, 1, 2, -4], ![-7, -5, -4, 10, 40], ![-6, 5, 1, 7, -2], ![-1, -4, -2, 2, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3684191, 1132071, 488343, -1051502, -1839940]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![3684191, 1132071, 488343, -1051502, -1839940]] 
 ![![61, 0, 0, 0, 0], ![53, 1, 0, 0, 0], ![58, 0, 1, 0, 0], ![26, 0, 0, 1, 0], ![60, 0, 0, 0, 1]] where
  M :=![![![3684191, 1132071, 488343, -1051502, -1839940], ![10513512, 3234464, 1395135, -3002458, -5258264], ![30056280, 9228465, 3981116, -8575010, -14996440], ![3310392, 1021809, 440637, -946947, -1662304], ![2594280, 792606, 342048, -738316, -1286649]]]
  hmulB := by decide  
  f := ![![![-1038397, -206565, 279585, -136286, -753484]], ![![-812333, -188167, 231648, -106220, -632068]], ![![-1119346, -128085, 255356, -148318, -660512]], ![![-539762, -98421, 140973, -70975, -377304]], ![![-979668, -191244, 262002, -128632, -705033]]]
  g := ![![![870426, 1132071, 488343, -1051502, -1839940], ![2487358, 3234464, 1395135, -3002458, -5258264], ![7094747, 9228465, 3981116, -8575010, -14996440], ![786171, 1021809, 440637, -946947, -1662304], ![608894, 792606, 342048, -738316, -1286649]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![-2780455, 901593, 40771, -386588, 315753]] ![![3, 0, 0, 0, 1]]
  ![![1038397, 206565, -279585, 136286, 753484]] where
 M := ![![![1038397, 206565, -279585, 136286, 753484]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![1038397, 206565, -279585, 136286, 753484]] ![![3684191, 1132071, 488343, -1051502, -1839940]]
  ![![61, 0, 0, 0, 0]] where
 M := ![![![-61, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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


lemma PB1271I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB1271I1 : PrimesBelowBoundCertificateInterval O 23 61 1271 where
  m := 9
  g := ![2, 1, 3, 4, 3, 4, 2, 2, 3]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB1271I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0, I29N1]
    · exact ![I31N0]
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0, I41N1, I41N2, I41N3]
    · exact ![I43N0, I43N1, I43N2]
    · exact ![I47N0, I47N1, I47N2, I47N3]
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
    · exact ![24389, 841]
    · exact ![28629151]
    · exact ![50653, 37, 37]
    · exact ![1681, 41, 41, 41]
    · exact ![79507, 43, 43]
    · exact ![2209, 47, 47, 47]
    · exact ![7890481, 53]
    · exact ![12117361, 59]
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
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
      exact NI37N2
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
      exact NI43N2
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
      exact NI47N2
      exact NI47N3
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
  β := ![I29N1, I37N1, I37N2, I41N1, I41N2, I41N3, I43N1, I43N2, I47N1, I47N2, I47N3, I53N1, I59N1, I61N1, I61N2]
  Il := ![[I29N1], [], [I37N1, I37N2], [I41N1, I41N2, I41N3], [I43N1, I43N2], [I47N1, I47N2, I47N3], [I53N1], [I59N1], [I61N1, I61N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
