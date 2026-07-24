
import IdealArithmetic.Examples.NF5_3_364500000_2.RI5_3_364500000_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3493, -1228, 1592, 211, -408]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![-3493, -1228, 1592, 211, -408]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![16, 14, 1, 0, 0], ![8, 1, 0, 1, 0], ![0, 17, 0, 0, 1]] where
  M :=![![![-3493, -1228, 1592, 211, -408], ![9792, 3009, -4510, -80, 844], ![-10128, -2081, 4777, -1134, -160], ![-2976, -4434, 988, 4177, -2690], ![6180, 6444, -2352, -5413, 3675]]]
  hmulB := by decide  
  f := ![![![-833, 254, 448, -31, -154]], ![![3696, 1247, -46, -336, -124]], ![![1376, 817, 271, -198, -168]], ![![112, 249, 170, -61, -82]], ![![2340, 889, 50, -247, -123]]]
  g := ![![![-1057, -579, 1592, 211, -408], ![2848, 1789, -4510, -80, 844], ![-2672, -2245, 4777, -1134, -160], ![-1800, 803, 988, 4177, -2690], ![3004, -610, -2352, -5413, 3675]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [21, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 28], [0, 1]]
 g := ![![[8, 1], [20], [6, 22], [6, 1]], ![[14, 28], [20], [22, 7], [12, 28]]]
 h' := ![![[6, 28], [28, 28], [19, 22], [19, 15], [0, 1]], ![[0, 1], [22, 1], [6, 7], [22, 14], [6, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [18, 23]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [21, 23, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-18111, -10363, -3300, 5710, 4418]
  a := ![0, -7, 2, -4, -9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-379, -1551, -3300, 5710, 4418]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-187, -42, 88, -16, -6]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![-187, -42, 88, -16, -6]] 
 ![![29, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![19, 0, 1, 0, 0], ![17, 0, 0, 1, 0], ![27, 0, 0, 0, 1]] where
  M :=![![![-187, -42, 88, -16, -6], ![144, -65, -76, 128, -64], ![768, 514, -321, -332, 256], ![-3144, -1484, 1396, 639, -632], ![4104, 1910, -1816, -796, 799]]]
  hmulB := by decide  
  f := ![![![93193, 54498, 15856, -24808, -19638]], ![![38747, 22653, 6588, -10312, -8162]], ![![102119, 59708, 17367, -27180, -21514]], ![![150277, 87854, 25548, -39993, -31654]], ![![220023, 128632, 37408, -58556, -46347]]]
  g := ![![![-39, -42, 88, -16, -6], ![55, -65, -76, 128, -64], ![69, 514, -321, -332, 256], ![-451, -1484, 1396, 639, -632], ![593, 1910, -1816, -796, 799]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1

def I29N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 37, 42, -3, -16]] i)))

def SI29N2: IdealEqSpanCertificate' Table ![![29, 37, 42, -3, -16]] 
 ![![29, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![11, 0, 0, 1, 0], ![23, 0, 0, 0, 1]] where
  M :=![![![29, 37, 42, -3, -16], ![384, 241, 16, -44, -12], ![144, 222, 261, -32, -88], ![864, 534, 70, -69, -58], ![228, 349, 366, -75, -107]]]
  hmulB := by decide  
  f := ![![![10489, 239, -2816, -209, 834]], ![![2565, 8, -728, -29, 230]], ![![1431, -53, -451, 9, 158]], ![![3463, -147, -1106, 30, 392]], ![![8383, -108, -2484, -36, 821]]]
  g := ![![![-1, 37, 42, -3, -16], ![-37, 241, 16, -44, -12], ![-9, 222, 261, -32, -88], ![-71, 534, 70, -69, -58], ![-25, 349, 366, -75, -107]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N2 : Nat.card (O ⧸ I29N2) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N2)

lemma isPrimeI29N2 : Ideal.IsPrime I29N2 := prime_ideal_of_norm_prime hp29.out _ NI29N2

def I29N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-35, -17, -4, 3, 2]] i)))

def SI29N3: IdealEqSpanCertificate' Table ![![-35, -17, -4, 3, 2]] 
 ![![29, 0, 0, 0, 0], ![14, 1, 0, 0, 0], ![18, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![18, 0, 0, 0, 1]] where
  M :=![![![-35, -17, -4, 3, 2], ![-48, -55, -32, 8, 12], ![-144, -98, -39, 16, 16], ![-168, -136, -66, 21, 26], ![-204, -141, -56, 23, 23]]]
  hmulB := by decide  
  f := ![![![-7, -3, -10, 1, 8]], ![![-10, -5, -4, 2, 4]], ![![-6, -4, -11, 2, 8]], ![![-36, -18, -2, 7, 6]], ![![-18, -13, -18, 7, 13]]]
  g := ![![![7, -17, -4, 3, 2], ![34, -55, -32, 8, 12], ![50, -98, -39, 16, 16], ![76, -136, -66, 21, 26], ![72, -141, -56, 23, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N3 : Nat.card (O ⧸ I29N3) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N3)

lemma isPrimeI29N3 : Ideal.IsPrime I29N3 := prime_ideal_of_norm_prime hp29.out _ NI29N3
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![-3493, -1228, 1592, 211, -408]] ![![-187, -42, 88, -16, -6]]
  ![![-638801, -47590, 310396, -170243, 47758]] where
 M := ![![![-638801, -47590, 310396, -170243, 47758]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI29N1 : IdealMulLeCertificate' Table 
  ![![-638801, -47590, 310396, -170243, 47758]] ![![29, 37, 42, -3, -16]]
  ![![-128303893, -40439135, 58984692, 2242608, -11758964]] where
 M := ![![![-128303893, -40439135, 58984692, 2242608, -11758964]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI29N2 : IdealMulLeCertificate' Table 
  ![![-128303893, -40439135, 58984692, 2242608, -11758964]] ![![-35, -17, -4, 3, 2]]
  ![![29, 0, 0, 0, 0]] where
 M := ![![![-40010401, -22161974, 17354760, 11968909, -10270698]]]
 hmul := by decide  
 g := ![![![![-1379669, -764206, 598440, 412721, -354162]]]]
 hle2 := by decide  


def PBC29 : ContainsPrimesAboveP 29 ![I29N0, I29N1, I29N2, I29N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N1
    exact isPrimeI29N2
    exact isPrimeI29N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 29 (by decide) (𝕀 ⊙ MulI29N0 ⊙ MulI29N1 ⊙ MulI29N2)
instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![143, 119, 74, -15, -30]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![143, 119, 74, -15, -30]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![19, 26, 12, 16, 1]] where
  M :=![![![143, 119, 74, -15, -30], ![720, 517, 148, -92, -60], ![720, 672, 489, -92, -184], ![1848, 1266, 322, -201, -154], ![924, 943, 750, -147, -263]]]
  hmulB := by decide  
  f := ![![![41, 15, 0, -7, -4]], ![![96, 71, 28, -32, -28]], ![![336, 184, 47, -84, -64]], ![![720, 424, 126, -193, -154]], ![![641, 378, 112, -172, -137]]]
  g := ![![![23, 29, 14, 15, -30], ![60, 67, 28, 28, -60], ![136, 176, 87, 92, -184], ![154, 170, 70, 73, -154], ![191, 251, 126, 131, -263]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 4 2 4 [9, 22, 14, 7, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 12, 4, 6], [28, 1, 24, 28], [19, 17, 3, 28], [0, 1]]
 g := ![![[6, 20, 13, 16], [29, 22, 25, 1], [17, 4, 24, 1], []], ![[0, 23, 4, 23, 27, 13], [11, 19, 24, 23, 12, 12], [17, 8, 17, 14, 22, 23], [4, 27, 6, 13, 5, 30]], ![[5, 6, 30, 8, 23, 25], [13, 30, 19, 20, 16, 8], [15, 8, 23, 24, 23, 18], [19, 19, 21, 26, 0, 4]], ![[25, 4, 14, 10, 2, 25], [28, 18, 23, 10], [22, 25, 6, 10, 22, 5], [17, 15, 3, 13, 22, 4]]]
 h' := ![![[8, 12, 4, 6], [18, 5, 4, 4], [2, 24, 16, 1], [0, 0, 0, 1], [0, 1]], ![[28, 1, 24, 28], [22, 1, 24, 11], [9, 0, 12, 23], [11, 20, 17, 3], [8, 12, 4, 6]], ![[19, 17, 3, 28], [12, 18, 24, 8], [22, 12, 13, 7], [19, 27, 14, 5], [28, 1, 24, 28]], ![[0, 1], [12, 7, 10, 8], [28, 26, 21], [10, 15, 0, 22], [19, 17, 3, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [7, 18, 7], []]
 b := ![[], [], [0, 2, 10, 23], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 4
  hpos := by decide
  P := [9, 22, 14, 7, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1417275736089, -884028285933, -342740088872, 457983514494, 343206656686]
  a := ![3, -62, -1, -65, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-256071039133, -316367785799, -143910321584, -162365257822, 343206656686]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 923521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-41, -15, 0, 7, 4]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![-41, -15, 0, 7, 4]] 
 ![![31, 0, 0, 0, 0], ![29, 1, 0, 0, 0], ![29, 0, 1, 0, 0], ![30, 0, 0, 1, 0], ![15, 0, 0, 0, 1]] where
  M :=![![![-41, -15, 0, 7, 4], ![-96, -71, -28, 32, 28], ![-336, -184, -47, 84, 64], ![-720, -424, -126, 193, 154], ![-1044, -595, -164, 271, 211]]]
  hmulB := by decide  
  f := ![![![-143, -119, -74, 15, 30]], ![![-157, -128, -74, 17, 30]], ![![-157, -133, -85, 17, 34]], ![![-198, -156, -82, 21, 34]], ![![-99, -88, -60, 12, 23]]]
  g := ![![![4, -15, 0, 7, 4], ![45, -71, -28, 32, 28], ![93, -184, -47, 84, 64], ![230, -424, -126, 193, 154], ![312, -595, -164, 271, 211]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![143, 119, 74, -15, -30]] ![![-41, -15, 0, 7, 4]]
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

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-645307, -27618, 163172, 18513, -44644]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![-645307, -27618, 163172, 18513, -44644]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![13, 31, 10, 28, 1]] where
  M :=![![![-645307, -27618, 163172, 18513, -44644], ![1071456, 45975, -270838, -30808, 74052], ![-888624, -37785, 224887, 25370, -61616], ![203664, 9402, -50968, -6173, 13714], ![-1062324, -44506, 269364, 30033, -74007]]]
  hmulB := by decide  
  f := ![![![1769, 644, -804, -133, 222]], ![![-5328, -1743, 2442, 168, -532]], ![![6384, 1651, -2975, 314, 336]], ![![-1368, 1042, 788, -1715, 894]], ![![-3139, -47, 1544, -1058, 365]]]
  g := ![![![-1755, 36658, 16476, 34285, -44644], ![2940, -60801, -27334, -56872, 74052], ![-2368, 50603, 22731, 47314, -61616], ![686, -11236, -5084, -10545, 13714], ![-2709, 60803, 27282, 56817, -74007]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 4 2 5 [29, 15, 31, 20, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 1, 19, 2], [11, 9, 35, 16], [36, 26, 20, 19], [0, 1]]
 g := ![![[24, 8, 30, 1], [28, 33, 34], [35, 4, 11, 30], [1], []], ![[1, 33, 24, 14, 4, 31], [5, 3, 36], [29, 6, 19, 1, 5, 6], [7], [25, 33, 4]], ![[6, 27, 33, 1, 32, 12], [23, 4, 3], [30, 30, 22, 23, 6, 16], [30, 15, 7], [21, 33, 34]], ![[14, 8, 33, 22, 12, 8], [22, 2, 25], [14, 20, 7, 34, 14, 8], [31, 11, 7], [35, 15, 28]]]
 h' := ![![[7, 1, 19, 2], [36, 30, 12, 36], [21, 15, 35, 16], [8, 22, 6, 17], [0, 0, 1], [0, 1]], ![[11, 9, 35, 16], [14, 31, 17, 16], [14, 32, 23, 31], [8, 22, 11, 15], [27, 14, 28], [7, 1, 19, 2]], ![[36, 26, 20, 19], [3, 18, 8, 26], [2, 18, 25, 22], [30, 17, 1, 1], [30, 36, 14, 28], [11, 9, 35, 16]], ![[0, 1], [1, 32, 0, 33], [11, 9, 28, 5], [29, 13, 19, 4], [22, 24, 31, 9], [36, 26, 20, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [20, 7, 1], []]
 b := ![[], [], [18, 32, 9, 30], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 4
  hpos := by decide
  P := [29, 15, 31, 20, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1059736464, -616611494, -177445481, 283894885, 224180074]
  a := ![1, -6, 1, -5, -4]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-107407498, -204491724, -65385033, -161976951, 224180074]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1874161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1769, -644, 804, 133, -222]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-1769, -644, 804, 133, -222]] 
 ![![37, 0, 0, 0, 0], ![36, 1, 0, 0, 0], ![18, 0, 1, 0, 0], ![28, 0, 0, 1, 0], ![35, 0, 0, 0, 1]] where
  M :=![![![-1769, -644, 804, 133, -222], ![5328, 1743, -2442, -168, 532], ![-6384, -1651, 2975, -314, -336], ![1368, -1042, -788, 1715, -894], ![-492, 1764, 436, -2255, 1281]]]
  hmulB := by decide  
  f := ![![![645307, 27618, -163172, -18513, 44644]], ![![598908, 25629, -151442, -17180, 41436]], ![![337950, 14457, -85459, -9692, 23384]], ![![482836, 20646, -122104, -13843, 33414]], ![![639137, 27328, -161632, -18324, 44231]]]
  g := ![![![297, -644, 804, 133, -222], ![-740, 1743, -2442, -168, 532], ![542, -1651, 2975, -314, -336], ![982, -1042, -788, 1715, -894], ![-1447, 1764, 436, -2255, 1281]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![-645307, -27618, 163172, 18513, -44644]] ![![-1769, -644, 804, 133, -222]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13925, 5193, -6314, -1192, 1832]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![13925, 5193, -6314, -1192, 1832]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![7, 33, 15, 1, 0], ![9, 25, 6, 0, 1]] where
  M :=![![![13925, 5193, -6314, -1192, 1832], ![-43968, -14925, 20098, 2028, -4768], ![57216, 16317, -26489, 1026, 4056], ![-26688, 1544, 13354, -11279, 4436], ![23976, -5551, -12446, 15048, -6867]]]
  hmulB := by decide  
  f := ![![![19957, 913, -5000, -596, 1352]], ![![-32448, -1107, 8426, 816, -2384]], ![![28608, 1917, -6691, -1110, 1632]], ![![-12325, 1, 3531, 135, -1116]], ![![-10323, -103, 2876, 156, -883]]]
  g := ![![![141, -31, 14, -1192, 1832], ![-372, 911, 446, 2028, -4768], ![330, -2901, -1615, 1026, 4056], ![301, 6411, 3803, -11279, 4436], ![-477, -8060, -4804, 15048, -6867]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [3, 28, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 8, 3], [25, 32, 38], [0, 1]]
 g := ![![[23, 27, 8], [1, 37], [16, 20], [22, 38, 1], []], ![[15, 5, 20, 14], [24, 10], [11, 21], [40, 1, 3, 38], [21, 9]], ![[28, 32, 4, 17], [29, 4], [31, 32], [34, 25, 21, 13], [27, 9]]]
 h' := ![![[13, 8, 3], [6, 30, 7], [3, 35, 18], [16, 8, 15], [0, 0, 1], [0, 1]], ![[25, 32, 38], [31, 15, 27], [29, 6, 25], [29, 27, 12], [24, 3, 32], [13, 8, 3]], ![[0, 1], [13, 37, 7], [10, 0, 39], [12, 6, 14], [11, 38, 8], [25, 32, 38]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31, 37], []]
 b := ![[], [15, 27, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [3, 28, 3, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-140209777, -79991569, -21758040, 38836694, 30052696]
  a := ![1, 25, -3, 18, 13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-16647339, -51534631, -19137186, 38836694, 30052696]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 68921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1265, -874, -1044, 372, 568]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![1265, -874, -1044, 372, 568]] 
 ![![41, 0, 0, 0, 0], ![16, 1, 0, 0, 0], ![36, 0, 1, 0, 0], ![32, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![1265, -874, -1044, 372, 568], ![-13632, -5283, -220, 2456, 1488], ![-17856, -12654, -4763, 5732, 4912], ![-52128, -29952, -8452, 13657, 10720], ![-66432, -41482, -13356, 18852, 15369]]]
  hmulB := by decide  
  f := ![![![113593, 40890, -51668, -7988, 13928]], ![![36176, 13341, -16420, -2920, 4656]], ![![109092, 38182, -49739, -6388, 12624]], ![![88000, 34168, -39756, -9127, 12512]], ![![12757, 1452, -6144, 2808, -607]]]
  g := ![![![929, -874, -1044, 372, 568], ![-176, -5283, -220, 2456, 1488], ![3612, -12654, -4763, 5732, 4912], ![5872, -29952, -8452, 13657, 10720], ![9707, -41482, -13356, 18852, 15369]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, 1, 0, 0, 0]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![-5, 1, 0, 0, 0]] 
 ![![41, 0, 0, 0, 0], ![36, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] where
  M :=![![![-5, 1, 0, 0, 0], ![0, -5, 2, 0, 0], ![0, 1, -5, 2, 0], ![0, 2, -2, -5, 4], ![-24, -11, 4, 8, -5]]]
  hmulB := by decide  
  f := ![![![-85, -47, -14, 20, 16]], ![![-84, -47, -14, 20, 16]], ![![-40, -23, -7, 10, 8]], ![![-58, -34, -10, 15, 12]], ![![-93, -54, -16, 24, 19]]]
  g := ![![![-1, 1, 0, 0, 0], ![4, -5, 2, 0, 0], ![0, 1, -5, 2, 0], ![-2, 2, -2, -5, 4], ![9, -11, 4, 8, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![13925, 5193, -6314, -1192, 1832]] ![![1265, -874, -1044, 372, 568]]
  ![![85, 47, 14, -20, -16]] where
 M := ![![![85, 47, 14, -20, -16]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![85, 47, 14, -20, -16]] ![![-5, 1, 0, 0, 0]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![91, 97, 50, -41, -40]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![91, 97, 50, -41, -40]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![36, 35, 10, 1, 0], ![35, 9, 10, 0, 1]] where
  M :=![![![91, 97, 50, -41, -40], ![960, 499, 116, -220, -164], ![1968, 1220, 391, -540, -440], ![4800, 2810, 822, -1259, -998], ![6492, 3881, 1174, -1745, -1397]]]
  hmulB := by decide  
  f := ![![![169, 69, -76, -21, 26]], ![![-624, -235, 284, 56, -84]], ![![1008, 348, -459, -52, 112]], ![![-156, -59, 72, 15, -22]], ![![269, 95, -122, -16, 31]]]
  g := ![![![69, 44, 20, -41, -40], ![340, 225, 92, -220, -164], ![856, 560, 237, -540, -440], ![1978, 1299, 544, -1259, -998], ![2749, 1803, 758, -1745, -1397]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [39, 29, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 8, 2], [29, 34, 41], [0, 1]]
 g := ![![[3, 41, 17], [37, 1, 13], [27, 31], [18, 41, 1], []], ![[35, 21, 34, 5], [40, 27, 26, 19], [28, 16], [5, 40, 4, 33], [24, 4]], ![[24, 34, 29, 15], [20, 33, 7, 14], [21, 11], [26, 34, 17, 1], [28, 4]]]
 h' := ![![[12, 8, 2], [19, 15, 24], [3, 34, 20], [29, 29, 26], [0, 0, 1], [0, 1]], ![[29, 34, 41], [25, 18, 29], [8, 15, 17], [38, 14, 39], [25, 28, 34], [12, 8, 2]], ![[0, 1], [20, 10, 33], [11, 37, 6], [20, 0, 21], [7, 15, 8], [29, 34, 41]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 7], []]
 b := ![[], [4, 37, 18], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [39, 29, 2, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![17116607, 11611283, 5489318, -6315811, -4480876]
  a := ![-1, -7, 5, 5, -19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![9332941, 6348664, 2638516, -6315811, -4480876]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 79507 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-295, 2, 86, 2, -28]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-295, 2, 86, 2, -28]] 
 ![![43, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![17, 0, 1, 0, 0], ![16, 0, 0, 1, 0], ![38, 0, 0, 0, 1]] where
  M :=![![![-295, 2, 86, 2, -28], ![672, 103, -112, -52, 8], ![-96, 184, 171, -80, -104], ![912, 478, 112, -219, -164], ![600, 638, 326, -286, -275]]]
  hmulB := by decide  
  f := ![![![-541, -278, 226, 130, -116]], ![![27, 9, -14, -2, 4]], ![![-359, -170, 153, 70, -68]], ![![32, -18, -24, 29, -12]], ![![-770, -354, 330, 138, -139]]]
  g := ![![![-17, 2, 86, 2, -28], ![65, 103, -112, -52, 8], ![39, 184, 171, -80, -104], ![170, 478, 112, -219, -164], ![190, 638, 326, -286, -275]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1

def I43N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-881, -823, 346, 659, -458]] i)))

def SI43N2: IdealEqSpanCertificate' Table ![![-881, -823, 346, 659, -458]] 
 ![![43, 0, 0, 0, 0], ![20, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![-881, -823, 346, 659, -458], ![10992, 5821, -4796, -2972, 2636], ![-31632, -14372, 14065, 5748, -5944], ![65832, 26746, -29610, -8225, 10178], ![-82380, -33143, 37094, 9911, -12515]]]
  hmulB := by decide  
  f := ![![![27853, 25745, 12120, -11557, -10752]], ![![18956, 15117, 6372, -6812, -6076]], ![![22617, 16825, 6657, -7597, -6624]], ![![39252, 25516, 8678, -11571, -9594]], ![![44306, 26701, 8156, -12141, -9745]]]
  g := ![![![79, -823, 346, 659, -458], ![-72, 5821, -4796, -2972, 2636], ![-285, -14372, 14065, 5748, -5944], ![1242, 26746, -29610, -8225, 10178], ![-1624, -33143, 37094, 9911, -12515]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N2 : Nat.card (O ⧸ I43N2) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N2)

lemma isPrimeI43N2 : Ideal.IsPrime I43N2 := prime_ideal_of_norm_prime hp43.out _ NI43N2
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![91, 97, 50, -41, -40]] ![![-295, 2, 86, 2, -28]]
  ![![-27853, -25745, -12120, 11557, 10752]] where
 M := ![![![-27853, -25745, -12120, 11557, 10752]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![-27853, -25745, -12120, 11557, 10752]] ![![-881, -823, 346, 659, -458]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![335, 197, 60, -90, -72]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![335, 197, 60, -90, -72]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![46, 12, 18, 1, 0], ![9, 26, 8, 0, 1]] where
  M :=![![![335, 197, 60, -90, -72], ![1728, 1007, 286, -456, -360], ![4320, 2531, 743, -1154, -912], ![10080, 5890, 1718, -2677, -2128], ![14064, 8225, 2384, -3746, -2953]]]
  hmulB := by decide  
  f := ![![![481, 23, -118, -14, 32]], ![![-768, -17, 202, 20, -56]], ![![672, 45, -149, -22, 40]], ![![530, 36, -120, -17, 32]], ![![-201, 4, 60, 4, -17]]]
  g := ![![![109, 67, 48, -90, -72], ![552, 337, 242, -456, -360], ![1396, 853, 613, -1154, -912], ![3242, 1986, 1424, -2677, -2128], ![4531, 2765, 1988, -3746, -2953]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [41, 17, 22, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 42, 16], [25, 4, 31], [0, 1]]
 g := ![![[0, 6, 18], [33, 26, 6], [14, 5, 12], [44, 25, 1], []], ![[12, 10, 6, 14], [29, 11, 10, 7], [45, 35, 20, 14], [26, 36, 42, 21], [36, 21]], ![[41, 25, 18, 44], [12, 24, 22, 41], [9, 28, 44, 35], [4, 26, 39, 23], [21, 21]]]
 h' := ![![[0, 42, 16], [10, 24, 26], [37, 22, 10], [29, 13, 23], [0, 0, 1], [0, 1]], ![[25, 4, 31], [33, 28, 18], [35, 12, 16], [15, 37, 18], [28, 31, 4], [0, 42, 16]], ![[0, 1], [20, 42, 3], [13, 13, 21], [2, 44, 6], [46, 16, 42], [25, 4, 31]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39, 27], []]
 b := ![[], [13, 27, 13], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [41, 17, 22, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![18221129, 5996612, -8236962, -681674, 1759434]
  a := ![0, -4, -2, -18, 10]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![717941, -671672, -213666, -681674, 1759434]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 103823 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![481, 23, -118, -14, 32]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![481, 23, -118, -14, 32]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![46, 29, 1, 0, 0], ![29, 5, 0, 1, 0], ![2, 32, 0, 0, 1]] where
  M :=![![![481, 23, -118, -14, 32], ![-768, -17, 202, 20, -56], ![672, 45, -149, -22, 40], ![-96, 28, 46, 1, -16], ![816, 63, -178, -30, 49]]]
  hmulB := by decide  
  f := ![![![335, 197, 60, -90, -72]], ![![1728, 1007, 286, -456, -360]], ![![1486, 868, 251, -394, -312]], ![![605, 354, 104, -161, -128]], ![![1490, 869, 248, -394, -311]]]
  g := ![![![133, 53, -118, -14, 32], ![-224, -89, 202, 20, -56], ![172, 68, -149, -22, 40], ![-47, -17, 46, 1, -16], ![208, 81, -178, -30, 49]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P1 : CertificateIrreducibleZModOfList' 47 2 2 5 [6, 32, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 46], [0, 1]]
 g := ![![[21, 8], [12, 18], [29, 28], [46, 37], [1]], ![[0, 39], [0, 29], [26, 19], [37, 10], [1]]]
 h' := ![![[15, 46], [22, 33], [14, 21], [6, 34], [41, 15], [0, 1]], ![[0, 1], [0, 14], [0, 26], [46, 13], [31, 32], [15, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [12, 36]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N1 : CertifiedPrimeIdeal' SI47N1 47 where
  n := 2
  hpos := by decide
  P := [6, 32, 1]
  hirr := P47P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2517, -5768, -13234, 4858, 7811]
  a := ![13, -7, 4, 2, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![9569, 2208, -13234, 4858, 7811]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N1 B_one_repr
lemma NI47N1 : Nat.card (O ⧸ I47N1) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![335, 197, 60, -90, -72]] ![![481, 23, -118, -14, 32]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-51413, -3737, 11800, 2142, -2768]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-51413, -3737, 11800, 2142, -2768]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![33, 32, 18, 1, 0], ![21, 30, 39, 0, 1]] where
  M :=![![![-51413, -3737, 11800, 2142, -2768], ![66432, -4881, -22830, 1456, 8568], ![-102816, -23867, 10799, 11442, 2912], ![-68160, -48142, -18070, 21719, 18600], ![-196224, -71341, 484, 33158, 18891]]]
  hmulB := by decide  
  f := ![![![27359, 10423, -12382, -2602, 3752]], ![![-90048, -31499, 41058, 5252, -10408]], ![![124896, 38001, -57567, -574, 10504]], ![![3555, 209, -1734, 1013, -304]], ![![53343, 14339, -24793, 1986, 3179]]]
  g := ![![![-1207, 203, 1532, 2142, -2768], ![-3048, -5821, -7230, 1456, 8568], ![-10218, -9007, -5825, 11442, 2912], ![-22179, -24550, -21404, 21719, 18600], ![-31833, -32059, -25153, 33158, 18891]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [5, 24, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 18, 4], [38, 34, 49], [0, 1]]
 g := ![![[52, 7, 52], [38, 28], [44, 41, 7], [10, 47], [1]], ![[12, 46, 46, 13], [16, 38], [52, 34, 29, 44], [8, 38], [48, 34, 12, 11]], ![[30, 34, 34, 46], [9, 9], [32, 34, 40, 11], [19, 7], [49, 52, 46, 42]]]
 h' := ![![[5, 18, 4], [33, 8, 23], [45, 0, 9], [28, 30, 31], [48, 29, 43], [0, 1]], ![[38, 34, 49], [50, 40, 19], [36, 10, 41], [41, 15, 8], [44, 28, 41], [5, 18, 4]], ![[0, 1], [19, 5, 11], [45, 43, 3], [2, 8, 14], [37, 49, 22], [38, 34, 49]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38, 23], []]
 b := ![[], [47, 27, 34], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [5, 24, 10, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![549926, 164123, -275197, -2068, 62279]
  a := ![-1, -1, -1, -4, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-13013, -30907, -50318, -2068, 62279]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 148877 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-27359, -10423, 12382, 2602, -3752]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-27359, -10423, 12382, 2602, -3752]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![40, 35, 1, 0, 0], ![31, 41, 0, 1, 0], ![48, 37, 0, 0, 1]] where
  M :=![![![-27359, -10423, 12382, 2602, -3752], ![90048, 31499, -41058, -5252, 10408], ![-124896, -38001, 57567, 574, -10504], ![81024, 8932, -39054, 18177, -4056], ![-83136, -4015, 40634, -24726, 7721]]]
  hmulB := by decide  
  f := ![![![51413, 3737, -11800, -2142, 2768]], ![![-66432, 4881, 22830, -1456, -8568]], ![![-3128, 6494, 5967, -2794, -3624]], ![![-20033, 6870, 11100, -2789, -5360]], ![![3888, 8138, 5242, -3582, -3831]]]
  g := ![![![-7985, -7767, 12382, 2602, -3752], ![26332, 24505, -41058, -5252, 10408], ![-36626, -31844, 57567, 574, -10504], ![24045, 14729, -39054, 18177, -4056], ![-24766, -13172, 40634, -24726, 7721]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P1 : CertificateIrreducibleZModOfList' 53 2 2 5 [43, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [30, 52], [0, 1]]
 g := ![![[3, 37], [38], [45, 37], [28], [30, 1]], ![[0, 16], [38], [42, 16], [28], [7, 52]]]
 h' := ![![[30, 52], [49, 39], [26, 41], [21, 39], [35, 9], [0, 1]], ![[0, 1], [0, 14], [37, 12], [25, 14], [40, 44], [30, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [13, 38]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N1 : CertifiedPrimeIdeal' SI53N1 53 where
  n := 2
  hpos := by decide
  P := [43, 23, 1]
  hirr := P53P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-131, -925, -3506, 1017, 2494]
  a := ![3, 3, 0, -1, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-210, -230, -3506, 1017, 2494]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N1 B_one_repr
lemma NI53N1 : Nat.card (O ⧸ I53N1) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-51413, -3737, 11800, 2142, -2768]] ![![-27359, -10423, 12382, 2602, -3752]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-353, -996, 66, 1050, -644]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-353, -996, 66, 1050, -644]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![18, 50, 45, 1, 0], ![8, 27, 15, 0, 1]] where
  M :=![![![-353, -996, 66, 1050, -644], ![15456, 8897, -6668, -5020, 4200], ![-50400, -23726, 22317, 10132, -10040], ![112752, 46862, -50604, -15333, 18164], ![-141912, -58392, 63754, 18602, -22453]]]
  hmulB := by decide  
  f := ![![![1445, 140, -306, -86, 52]], ![![-1248, 395, 660, -196, -344]], ![![4128, 1402, -97, -716, -392]], ![![2622, 1502, 409, -765, -596]], ![![848, 637, 249, -322, -277]]]
  g := ![![![-239, -612, -636, 1050, -644], ![1224, 2483, 2648, -5020, 4200], ![-2584, -4394, -4797, 10132, -10040], ![4126, 5476, 6219, -15333, 18164], ![-5036, -6479, -7399, 18602, -22453]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [24, 8, 11, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [47, 53, 44], [1, 5, 15], [0, 1]]
 g := ![![[30, 1, 57], [7, 54, 22], [55, 20], [57, 25, 3], [1]], ![[30, 8], [13, 29, 48, 38], [38, 57], [57, 34, 55, 50], [43, 21, 35, 47]], ![[58, 12, 1, 29], [0, 15, 32, 4], [13, 46], [41, 19, 18, 21], [20, 15, 57, 12]]]
 h' := ![![[47, 53, 44], [9, 12, 36], [40, 23, 9], [48, 51, 16], [35, 51, 48], [0, 1]], ![[1, 5, 15], [42, 26], [0, 34, 54], [26, 26, 23], [13, 41, 6], [47, 53, 44]], ![[0, 1], [25, 21, 23], [5, 2, 55], [9, 41, 20], [52, 26, 5], [1, 5, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31, 37], []]
 b := ![[], [57, 27, 30], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [24, 8, 11, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4794208, -3032409, -1185522, 1557942, 1142136]
  a := ![1, 5, -3, -2, 11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-711428, -1894359, -1498728, 1557942, 1142136]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 205379 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-173, -8, 44, 5, -12]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![-173, -8, 44, 5, -12]] 
 ![![59, 0, 0, 0, 0], ![31, 1, 0, 0, 0], ![21, 0, 1, 0, 0], ![13, 0, 0, 1, 0], ![27, 0, 0, 0, 1]] where
  M :=![![![-173, -8, 44, 5, -12], ![288, 13, -74, -8, 20], ![-240, -11, 61, 6, -16], ![48, -2, -12, 1, 2], ![-276, -8, 68, 5, -17]]]
  hmulB := by decide  
  f := ![![![17, 6, 4, -11, -10]], ![![13, 5, 2, -7, -6]], ![![15, 7, 3, -7, -6]], ![![31, 16, 4, -10, -8]], ![![45, 24, 8, -16, -13]]]
  g := ![![![-10, -8, 44, 5, -12], ![17, 13, -74, -8, 20], ![-14, -11, 61, 6, -16], ![5, -2, -12, 1, 2], ![-18, -8, 68, 5, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1127, 52, -282, -34, 76]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![1127, 52, -282, -34, 76]] 
 ![![59, 0, 0, 0, 0], ![56, 1, 0, 0, 0], ![25, 0, 1, 0, 0], ![39, 0, 0, 1, 0], ![58, 0, 0, 0, 1]] where
  M :=![![![1127, 52, -282, -34, 76], ![-1824, -59, 476, 44, -136], ![1632, 118, -375, -68, 88], ![-144, 106, 124, -45, -68], ![2136, 248, -418, -130, 67]]]
  hmulB := by decide  
  f := ![![![-563, -332, 18, 62, 4]], ![![-536, -323, 4, 60, 8]], ![![-289, -170, 7, 30, 4]], ![![-399, -250, -10, 49, 8]], ![![-610, -360, 10, 62, 11]]]
  g := ![![![37, 52, -282, -34, 76], ![-72, -59, 476, 44, -136], ![33, 118, -375, -68, 88], ![-59, 106, 124, -45, -68], ![-2, 248, -418, -130, 67]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-353, -996, 66, 1050, -644]] ![![-173, -8, 44, 5, -12]]
  ![![-13475, -7798, 5806, 4429, -3692]] where
 M := ![![![-13475, -7798, 5806, 4429, -3692]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![-13475, -7798, 5806, 4429, -3692]] ![![1127, 52, -282, -34, 76]]
  ![![59, 0, 0, 0, 0]] where
 M := ![![![-11269, -1652, 3304, 885, -1180]]]
 hmul := by decide  
 g := ![![![![-191, -28, 56, 15, -20]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9175, 397, -2316, -265, 632]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![9175, 397, -2316, -265, 632]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![15, 43, 50, 24, 1]] where
  M :=![![![9175, 397, -2316, -265, 632], ![-15168, -623, 3852, 424, -1060], ![12720, 596, -3167, -388, 848], ![-2592, 36, 754, 13, -246], ![15420, 833, -3744, -521, 967]]]
  hmulB := by decide  
  f := ![![![19, 15, 6, -3, -2]], ![![48, 41, 28, -4, -12]], ![![144, 100, 21, -20, -8]], ![![72, 86, 90, -9, -34]], ![![189, 151, 74, -24, -29]]]
  g := ![![![-5, -439, -556, -253, 632], ![12, 737, 932, 424, -1060], ![0, -588, -747, -340, 848], ![18, 174, 214, 97, -246], ![15, -668, -854, -389, 967]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 4 2 5 [37, 28, 8, 6, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [23, 0, 47, 9], [24, 7, 40, 54], [8, 53, 35, 59], [0, 1]]
 g := ![![[34, 42, 9, 5], [33, 26, 46], [15, 17, 24, 4], [35, 28, 55, 1], []], ![[14, 55, 16, 7, 48, 1], [57, 43, 36], [36, 32, 4, 30, 21, 9], [48, 2, 40, 58, 3, 25], [46, 10, 50, 0, 32, 58]], ![[16, 16, 6, 17, 53, 7], [35, 1, 58], [2, 32, 36, 35, 47, 23], [42, 52, 51, 60, 58, 23], [23, 30, 9, 15, 8, 23]], ![[41, 28, 41, 29, 39, 51], [29, 31, 39], [59, 21, 55, 12, 13, 44], [60, 44, 19, 26, 41, 37], [58, 24, 7, 58, 41, 53]]]
 h' := ![![[23, 0, 47, 9], [35, 54, 16, 26], [55, 1, 3, 30], [47, 58, 12, 2], [0, 0, 0, 1], [0, 1]], ![[24, 7, 40, 54], [26, 46, 54, 20], [0, 22, 14, 55], [46, 44, 49, 1], [34, 50, 50, 22], [23, 0, 47, 9]], ![[8, 53, 35, 59], [56, 16, 29, 50], [58, 21, 46, 27], [55, 45, 15, 7], [41, 33, 43, 54], [24, 7, 40, 54]], ![[0, 1], [50, 6, 23, 26], [56, 17, 59, 10], [47, 36, 46, 51], [13, 39, 29, 45], [8, 53, 35, 59]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [1, 12, 58], []]
 b := ![[], [], [29, 29, 44, 17], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 4
  hpos := by decide
  P := [37, 28, 8, 6, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-173887, -70740, 78404, 21852, -26997]
  a := ![4, 0, 0, 1, -1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3788, 17871, 23414, 10980, -26997]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 13845841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19, -15, -6, 3, 2]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![-19, -15, -6, 3, 2]] 
 ![![61, 0, 0, 0, 0], ![26, 1, 0, 0, 0], ![28, 0, 1, 0, 0], ![50, 0, 0, 1, 0], ![42, 0, 0, 0, 1]] where
  M :=![![![-19, -15, -6, 3, 2], ![-48, -41, -28, 4, 12], ![-144, -100, -21, 20, 8], ![-72, -86, -90, 9, 34], ![-252, -159, -10, 31, 7]]]
  hmulB := by decide  
  f := ![![![-9175, -397, 2316, 265, -632]], ![![-3662, -159, 924, 106, -252]], ![![-4420, -192, 1115, 128, -304]], ![![-7478, -326, 1886, 217, -514]], ![![-6570, -287, 1656, 191, -451]]]
  g := ![![![5, -15, -6, 3, 2], ![18, -41, -28, 4, 12], ![28, -100, -21, 20, 8], ![46, -86, -90, 9, 34], ![38, -159, -10, 31, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![9175, 397, -2316, -265, 632]] ![![-19, -15, -6, 3, 2]]
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


lemma PB934I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB934I1 : PrimesBelowBoundCertificateInterval O 23 61 934 where
  m := 9
  g := ![4, 2, 2, 3, 3, 2, 2, 3, 2]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB934I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0, I29N1, I29N2, I29N3]
    · exact ![I31N0, I31N1]
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0, I43N1, I43N2]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
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
    · exact ![841, 29, 29, 29]
    · exact ![923521, 31]
    · exact ![1874161, 37]
    · exact ![68921, 41, 41]
    · exact ![79507, 43, 43]
    · exact ![103823, 2209]
    · exact ![148877, 2809]
    · exact ![205379, 59, 59]
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
      exact NI29N2
      exact NI29N3
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
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
      exact NI59N2
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
  β := ![I29N0, I29N1, I29N2, I29N3, I31N1, I37N1, I41N1, I41N2, I43N1, I43N2, I59N1, I59N2, I61N1]
  Il := ![[I29N0, I29N1, I29N2, I29N3], [I31N1], [I37N1], [I41N1, I41N2], [I43N1, I43N2], [], [], [I59N1, I59N2], [I61N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
