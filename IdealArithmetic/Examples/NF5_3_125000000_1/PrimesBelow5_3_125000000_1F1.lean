
import IdealArithmetic.Examples.NF5_3_125000000_1.RI5_3_125000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![599, 170, -140, 87, -72]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![599, 170, -140, 87, -72]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![27, 23, 19, 1, 0], ![9, 21, 10, 0, 1]] where
  M :=![![![599, 170, -140, 87, -72], ![-1440, -405, 340, -208, 174], ![1740, 494, -405, 253, -208], ![-1360, -378, 324, -197, 166], ![1660, 478, -378, 241, -197]]]
  hmulB := by decide  
  f := ![![![-29, -4, 4, -1, 2]], ![![40, -1, -8, 6, -2]], ![![-20, 4, -1, -7, 6]], ![![-7, -1, -3, -1, 4]], ![![11, -1, -4, 2, 1]]]
  g := ![![![-38, -11, -37, 87, -72], ![90, 25, 88, -208, 174], ![-111, -33, -108, 253, -208], ![85, 23, 83, -197, 166], ![-106, -32, -103, 241, -197]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 3 2 4 [19, 19, 25, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 21, 22], [24, 7, 7], [0, 1]]
 g := ![![[27, 9, 22], [1, 28], [17, 28, 16], [1]], ![[24, 28, 2, 13], [19, 16], [9, 17, 16, 6], [27, 16, 4, 5]], ![[8, 20, 1, 20], [0, 24], [8, 12, 11, 16], [20, 17, 23, 24]]]
 h' := ![![[9, 21, 22], [26, 8, 15], [25, 28, 12], [10, 10, 4], [0, 1]], ![[24, 7, 7], [11, 25, 20], [16, 27, 4], [13, 23, 16], [9, 21, 22]], ![[0, 1], [4, 25, 23], [27, 3, 13], [17, 25, 9], [24, 7, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13, 27], []]
 b := ![[], [21, 1, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 3
  hpos := by decide
  P := [19, 19, 25, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-57961, -103297, -92199, -52640, -15399]
  a := ![0, -2, -3, -3, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![51790, 49338, 36619, -52640, -15399]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 24389 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -4, -4, 1, 2]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![-1, -4, -4, 1, 2]] 
 ![![29, 0, 0, 0, 0], ![24, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![22, 0, 0, 1, 0], ![26, 0, 0, 0, 1]] where
  M :=![![![-1, -4, -4, 1, 2], ![40, 19, -8, -10, 2], ![20, 28, 19, -9, -10], ![-120, -50, 32, 29, -10], ![-100, -104, -50, 37, 29]]]
  hmulB := by decide  
  f := ![![![171, 10, 4, 9, -8]], ![![136, 11, 4, 8, -6]], ![![18, 2, 3, 1, 0]], ![![138, 14, 4, 9, -6]], ![![154, 14, 10, 9, -5]]]
  g := ![![![1, -4, -4, 1, 2], ![-8, 19, -8, -10, 2], ![-8, 28, 19, -9, -10], ![22, -50, 32, 29, -10], ![32, -104, -50, 37, 29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1

def I29N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 12, -16, 10, -12]] i)))

def SI29N2: IdealEqSpanCertificate' Table ![![131, 12, -16, 10, -12]] 
 ![![29, 0, 0, 0, 0], ![25, 1, 0, 0, 0], ![21, 0, 1, 0, 0], ![15, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![131, 12, -16, 10, -12], ![-240, -29, 24, -20, 20], ![200, 12, -29, 14, -20], ![-80, -20, 0, -9, 4], ![40, -16, -20, -2, -9]]]
  hmulB := by decide  
  f := ![![![-161, -52, 32, -18, 20]], ![![-125, -41, 24, -14, 16]], ![![-129, -40, 27, -16, 16]], ![![-75, -24, 16, -7, 8]], ![![-29, -12, 4, 0, 3]]]
  g := ![![![1, 12, -16, 10, -12], ![9, -29, 24, -20, 20], ![11, 12, -29, 14, -20], ![19, -20, 0, -9, 4], ![31, -16, -20, -2, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N2 : Nat.card (O ⧸ I29N2) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N2)

lemma isPrimeI29N2 : Ideal.IsPrime I29N2 := prime_ideal_of_norm_prime hp29.out _ NI29N2
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![599, 170, -140, 87, -72]] ![![-1, -4, -4, 1, 2]]
  ![![161, 52, -32, 18, -20]] where
 M := ![![![161, 52, -32, 18, -20]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI29N1 : IdealMulLeCertificate' Table 
  ![![161, 52, -32, 18, -20]] ![![131, 12, -16, 10, -12]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-451, -194, 36, -79, 30]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![-451, -194, 36, -79, 30]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![17, 8, 26, 17, 1]] where
  M :=![![![-451, -194, 36, -79, 30], ![600, -55, -388, 42, -158], ![-1580, -842, -55, -309, 42], ![120, -538, -648, -97, -230], ![-2300, -1644, -538, -533, -97]]]
  hmulB := by decide  
  f := ![![![19, 4, -4, -1, 0]], ![![0, 15, 8, -8, -2]], ![![-20, -8, 15, 9, -8]], ![![-80, -58, -12, 23, 10]], ![![-47, -32, 4, 17, -1]]]
  g := ![![![-31, -14, -24, -19, 30], ![106, 39, 120, 88, -158], ![-74, -38, -37, -33, 42], ![130, 42, 172, 123, -230], ![-21, -28, 64, 36, -97]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 4 2 4 [27, 14, 2, 15, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 30, 8, 15], [25, 19, 14, 1], [0, 12, 9, 15], [0, 1]]
 g := ![![[21, 10, 22, 7], [17, 1, 6, 7], [19, 6, 16, 1], []], ![[1, 24, 3, 29, 4, 11], [12, 4, 3, 24, 30, 12], [7, 0, 19, 29, 2, 13], [29, 17, 3, 14, 4, 27]], ![[12, 18, 15, 12, 9, 5], [0, 28, 6, 2, 5, 9], [2, 18, 15, 2, 30, 2], [29, 21, 2, 21, 27, 1]], ![[0, 2, 29, 19, 9, 24], [29, 5, 11, 10, 12, 11], [10, 13, 8, 20, 2, 11], [13, 14, 11, 18, 28, 27]]]
 h' := ![![[22, 30, 8, 15], [6, 24, 20, 21], [14, 6, 4, 10], [0, 0, 0, 1], [0, 1]], ![[25, 19, 14, 1], [16, 13, 9, 3], [21, 23, 3, 21], [7, 8, 21, 25], [22, 30, 8, 15]], ![[0, 12, 9, 15], [16, 28, 4, 25], [24, 6, 23, 3], [24, 25, 2, 8], [25, 19, 14, 1]], ![[0, 1], [23, 28, 29, 13], [9, 27, 1, 28], [21, 29, 8, 28], [0, 12, 9, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [14, 2, 7], []]
 b := ![[], [], [6, 8, 22, 24], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 4
  hpos := by decide
  P := [27, 14, 2, 15, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1535297653, 13889249526, 16095117422, 7948415058, 5437076024]
  a := ![3, -65, 2, -66, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2932096605, -955076086, -4040930942, -2725221850, 5437076024]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 923521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 4, -4, -1, 0]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![19, 4, -4, -1, 0]] 
 ![![31, 0, 0, 0, 0], ![28, 1, 0, 0, 0], ![11, 0, 1, 0, 0], ![18, 0, 0, 1, 0], ![27, 0, 0, 0, 1]] where
  M :=![![![19, 4, -4, -1, 0], ![0, 15, 8, -8, -2], ![-20, -8, 15, 9, -8], ![-80, -58, -12, 23, 10], ![100, 14, -58, -17, 23]]]
  hmulB := by decide  
  f := ![![![-451, -194, 36, -79, 30]], ![![-388, -177, 20, -70, 22]], ![![-211, -96, 11, -38, 12]], ![![-258, -130, 0, -49, 10]], ![![-467, -222, 14, -86, 23]]]
  g := ![![![-1, 4, -4, -1, 0], ![-10, 15, 8, -8, -2], ![3, -8, 15, 9, -8], ![32, -58, -12, 23, 10], ![1, 14, -58, -17, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![-451, -194, 36, -79, 30]] ![![19, 4, -4, -1, 0]]
  ![![31, 0, 0, 0, 0]] where
 M := ![![![31, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-39, -79, -68, -19, -22]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![-39, -79, -68, -19, -22]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![20, 36, 1, 0, 0], ![20, 28, 0, 1, 0], ![32, 1, 0, 0, 1]] where
  M :=![![![-39, -79, -68, -19, -22], ![-440, -371, -158, -114, -38], ![-380, -527, -371, -139, -114], ![-920, -874, -448, -257, -120], ![-1200, -1404, -874, -388, -257]]]
  hmulB := by decide  
  f := ![![![117, 51, -34, -31, 12]], ![![240, 227, 102, -80, -62]], ![![280, 243, 87, -91, -56]], ![![220, 178, 52, -69, -36]], ![![152, 61, -48, -38, 17]]]
  g := ![![![65, 79, -68, -19, -22], ![168, 231, -158, -114, -38], ![364, 455, -371, -139, -114], ![460, 610, -448, -257, -120], ![872, 1113, -874, -388, -257]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [30, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 36], [0, 1]]
 g := ![![[18, 21], [26], [13, 16], [3], [1]], ![[0, 16], [26], [31, 21], [3], [1]]]
 h' := ![![[15, 36], [27, 13], [17, 27], [33, 33], [7, 15], [0, 1]], ![[0, 1], [0, 24], [15, 10], [10, 4], [10, 22], [15, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [16, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [30, 22, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![173, 374, 533, 170, 32]
  a := ![1, -4, -1, -5, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-403, -638, 533, 170, 32]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 8, 6, 2, 2]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![3, 8, 6, 2, 2]] 
 ![![37, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![24, 0, 1, 0, 0], ![23, 0, 0, 1, 0], ![33, 0, 0, 0, 1]] where
  M :=![![![3, 8, 6, 2, 2], ![40, 33, 16, 10, 4], ![40, 52, 33, 14, 10], ![80, 80, 44, 23, 12], ![120, 134, 80, 38, 23]]]
  hmulB := by decide  
  f := ![![![-41, 4, 14, -10, 2]], ![![-10, 1, 4, -2, 0]], ![![-32, 0, 9, -6, 2]], ![![-19, 4, 6, -7, 2]], ![![-29, 10, 14, -12, 1]]]
  g := ![![![-9, 8, 6, 2, 2], ![-28, 33, 16, 10, 4], ![-52, 52, 33, 14, 10], ![-73, 80, 44, 23, 12], ![-129, 134, 80, 38, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 3, -2, 2, -2]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![23, 3, -2, 2, -2]] 
 ![![37, 0, 0, 0, 0], ![30, 1, 0, 0, 0], ![31, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![22, 0, 0, 0, 1]] where
  M :=![![![23, 3, -2, 2, -2], ![-40, -3, 6, -2, 4], ![40, 7, -3, 4, -2], ![0, 8, 4, -1, 2], ![20, 14, 8, 3, -1]]]
  hmulB := by decide  
  f := ![![![979, 275, -228, 142, -118]], ![![730, 205, -170, 106, -88]], ![![897, 252, -209, 130, -108]], ![![-33, -9, 8, -5, 4]], ![![654, 184, -152, 95, -79]]]
  g := ![![![1, 3, -2, 2, -2], ![-6, -3, 6, -2, 4], ![-1, 7, -3, 4, -2], ![-11, 8, 4, -1, 2], ![-17, 14, 8, 3, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2

def I37N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-133, -15, 16, -11, 12]] i)))

def SI37N3: IdealEqSpanCertificate' Table ![![-133, -15, 16, -11, 12]] 
 ![![37, 0, 0, 0, 0], ![36, 1, 0, 0, 0], ![18, 0, 1, 0, 0], ![28, 0, 0, 1, 0], ![14, 0, 0, 0, 1]] where
  M :=![![![-133, -15, 16, -11, 12], ![240, 27, -30, 20, -22], ![-220, -27, 27, -19, 20], ![80, 10, -12, 7, -8], ![-80, -14, 10, -8, 7]]]
  hmulB := by decide  
  f := ![![![-9, 7, 14, -3, -6]], ![![-12, 5, 14, -2, -6]], ![![-6, 1, 5, -1, -2]], ![![4, 10, 8, -5, -4]], ![![2, 10, 10, -4, -5]]]
  g := ![![![7, -15, 16, -11, 12], ![-12, 27, -30, 20, -22], ![14, -27, 27, -19, 20], ![-4, 10, -12, 7, -8], ![10, -14, 10, -8, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N3 : Nat.card (O ⧸ I37N3) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N3)

lemma isPrimeI37N3 : Ideal.IsPrime I37N3 := prime_ideal_of_norm_prime hp37.out _ NI37N3
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![-39, -79, -68, -19, -22]] ![![3, 8, 6, 2, 2]]
  ![![-10157, -10923, -6338, -3093, -1808]] where
 M := ![![![-10157, -10923, -6338, -3093, -1808]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![-10157, -10923, -6338, -3093, -1808]] ![![23, 3, -2, 2, -2]]
  ![![-86371, -92124, -53046, -26151, -15080]] where
 M := ![![![-86371, -92124, -53046, -26151, -15080]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI37N2 : IdealMulLeCertificate' Table 
  ![![-86371, -92124, -53046, -26151, -15080]] ![![-133, -15, 16, -11, 12]]
  ![![37, 0, 0, 0, 0]] where
 M := ![![![162023, 190069, 112554, 53058, 33004]]]
 hmul := by decide  
 g := ![![![![4379, 5137, 3042, 1434, 892]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1, I37N2, I37N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
    exact isPrimeI37N2
    exact isPrimeI37N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0 ⊙ MulI37N1 ⊙ MulI37N2)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 6, 2, 1, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![11, 6, 2, 1, 0]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![8, 16, 1, 0, 0], ![36, 15, 0, 1, 0], ![3, 24, 0, 0, 1]] where
  M :=![![![11, 6, 2, 1, 0], ![0, 13, 12, 4, 2], ![20, 18, 13, 11, 4], ![40, 34, 12, 9, 10], ![100, 86, 34, 7, 9]]]
  hmulB := by decide  
  f := ![![![-509, -148, 122, -75, 62]], ![![1240, 357, -296, 182, -150]], ![![348, 100, -83, 51, -42]], ![![36, 9, -8, 5, -4]], ![![653, 188, -156, 96, -79]]]
  g := ![![![-1, -1, 2, 1, 0], ![-6, -7, 12, 4, 2], ![-12, -11, 13, 11, 4], ![-10, -13, 12, 9, 10], ![-11, -19, 34, 7, 9]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [25, 14, 1] where
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
 g := ![![[35, 23], [2], [5], [6, 32], [1]], ![[0, 18], [2], [5], [9, 9], [1]]]
 h' := ![![[27, 40], [30, 8], [30, 17], [14, 28], [16, 27], [0, 1]], ![[0, 1], [0, 33], [38, 24], [32, 13], [7, 14], [27, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [40, 35]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [25, 14, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3040, 6865, 6954, 3756, 1371]
  a := ![1, 18, 4, 17, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4681, -4723, 6954, 3756, 1371]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![51, 14, -12, 7, -6]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![51, 14, -12, 7, -6]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![23, 26, 1, 0, 0], ![17, 33, 0, 1, 0], ![20, 32, 0, 0, 1]] where
  M :=![![![51, 14, -12, 7, -6], ![-120, -33, 28, -18, 14], ![140, 38, -33, 21, -18], ![-120, -38, 24, -15, 14], ![140, 36, -38, 17, -15]]]
  hmulB := by decide  
  f := ![![![91, 8, -12, 7, -8]], ![![-160, -17, 16, -16, 14]], ![![-47, -6, 3, -6, 4]], ![![-93, -11, 8, -10, 8]], ![![-80, -10, 6, -9, 7]]]
  g := ![![![8, 7, -12, 7, -6], ![-18, -15, 28, -18, 14], ![22, 19, -33, 21, -18], ![-17, -15, 24, -15, 14], ![25, 23, -38, 17, -15]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P1 : CertificateIrreducibleZModOfList' 41 2 2 5 [37, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 40], [0, 1]]
 g := ![![[37, 10], [9], [18], [40, 10], [1]], ![[0, 31], [9], [18], [3, 31], [1]]]
 h' := ![![[25, 40], [31, 25], [6, 38], [37, 31], [4, 25], [0, 1]], ![[0, 1], [0, 16], [13, 3], [33, 10], [14, 16], [25, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [12, 22]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N1 : CertifiedPrimeIdeal' SI41N1 41 where
  n := 2
  hpos := by decide
  P := [37, 16, 1]
  hirr := P41P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![102, 103, -182, -34, 887]
  a := ![-1, 2, -4, 4, -9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-314, -547, -182, -34, 887]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N1 B_one_repr
lemma NI41N1 : Nat.card (O ⧸ I41N1) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 6, -6, 4, -4]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![41, 6, -6, 4, -4]] 
 ![![41, 0, 0, 0, 0], ![39, 1, 0, 0, 0], ![39, 0, 1, 0, 0], ![40, 0, 0, 1, 0], ![40, 0, 0, 0, 1]] where
  M :=![![![41, 6, -6, 4, -4], ![-80, -13, 12, -8, 8], ![80, 14, -13, 8, -8], ![-40, -8, 8, -5, 4], ![40, 8, -8, 6, -5]]]
  hmulB := by decide  
  f := ![![![1, -6, -6, -4, -4]], ![![-1, -7, -6, -4, -4]], ![![-1, -8, -7, -4, -4]], ![![0, -8, -8, -5, -4]], ![![0, -8, -8, -6, -5]]]
  g := ![![![1, 6, -6, 4, -4], ![-1, -13, 12, -8, 8], ![1, 14, -13, 8, -8], ![0, -8, 8, -5, 4], ![0, 8, -8, 6, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![11, 6, 2, 1, 0]] ![![51, 14, -12, 7, -6]]
  ![![1, -6, -6, -4, -4]] where
 M := ![![![1, -6, -6, -4, -4]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![1, -6, -6, -4, -4]] ![![41, 6, -6, 4, -4]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1041, -109, 118, -83, 92]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![-1041, -109, 118, -83, 92]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![33, 15, 1, 0, 0], ![21, 7, 0, 1, 0], ![27, 13, 0, 0, 1]] where
  M :=![![![-1041, -109, 118, -83, 92], ![1840, 181, -218, 144, -166], ![-1660, -185, 181, -135, 144], ![520, 34, -76, 37, -52], ![-520, -90, 34, -50, 37]]]
  hmulB := by decide  
  f := ![![![-3, -13, -16, -1, 10]], ![![200, 101, -26, -42, -2]], ![![67, 27, -19, -16, 6]], ![![19, 4, -10, -4, 4]], ![![53, 14, -24, -11, 9]]]
  g := ![![![-132, -58, 118, -83, 92], ![244, 107, -218, 144, -166], ![-202, -89, 181, -135, 144], ![85, 37, -76, 37, -52], ![-37, -17, 34, -50, 37]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [30, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 42], [0, 1]]
 g := ![![[18, 10], [0, 1], [9], [0, 17], [1]], ![[36, 33], [19, 42], [9], [22, 26], [1]]]
 h' := ![![[19, 42], [0, 28], [31, 42], [0, 3], [13, 19], [0, 1]], ![[0, 1], [16, 15], [12, 1], [14, 40], [30, 24], [19, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [9, 33]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [30, 24, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-770, 2060, 3072, -3120, 596]
  a := ![0, -10, 4, -20, 6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1226, -696, 3072, -3120, 596]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![589, 113, -104, 66, -62]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![589, 113, -104, 66, -62]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![11, 20, 1, 0, 0], ![38, 36, 0, 1, 0], ![34, 30, 0, 0, 1]] where
  M :=![![![589, 113, -104, 66, -62], ![-1240, -259, 226, -146, 132], ![1320, 285, -259, 160, -146], ![-840, -216, 172, -113, 94], ![940, 230, -216, 125, -113]]]
  hmulB := by decide  
  f := ![![![-153, -89, 10, 42, 2]], ![![40, -119, -178, 18, 84]], ![![-1, -68, -83, 14, 40]], ![![-98, -166, -128, 49, 66]], ![![-154, -182, -104, 61, 57]]]
  g := ![![![31, 39, -104, 66, -62], ![-62, -81, 226, -146, 132], ![71, 95, -259, 160, -146], ![-38, -56, 172, -113, 94], ![56, 80, -216, 125, -113]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P1 : CertificateIrreducibleZModOfList' 43 2 2 5 [6, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 42], [0, 1]]
 g := ![![[16, 36], [33, 10], [13], [23, 14], [1]], ![[0, 7], [19, 33], [13], [12, 29], [1]]]
 h' := ![![[33, 42], [17, 6], [3, 15], [34, 23], [37, 33], [0, 1]], ![[0, 1], [0, 37], [25, 28], [19, 20], [8, 10], [33, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [1, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N1 : CertifiedPrimeIdeal' SI43N1 43 where
  n := 2
  hpos := by decide
  P := [6, 10, 1]
  hirr := P43P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![465, 197, -17, 350, 359]
  a := ![13, 0, -3, 1, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-578, -531, -17, 350, 359]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N1 B_one_repr
lemma NI43N1 : Nat.card (O ⧸ I43N1) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N1

def I43N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![33, 10, -8, 5, -4]] i)))

def SI43N2: IdealEqSpanCertificate' Table ![![33, 10, -8, 5, -4]] 
 ![![43, 0, 0, 0, 0], ![16, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![27, 0, 0, 1, 0], ![42, 0, 0, 0, 1]] where
  M :=![![![33, 10, -8, 5, -4], ![-80, -23, 20, -12, 10], ![100, 30, -23, 15, -12], ![-80, -22, 20, -11, 10], ![100, 30, -22, 15, -11]]]
  hmulB := by decide  
  f := ![![![-29, 0, 0, -5, 6]], ![![-8, 1, 0, -2, 2]], ![![-3, 0, 1, 0, 0]], ![![-21, -2, 0, -2, 4]], ![![-26, 0, -2, -5, 7]]]
  g := ![![![-2, 10, -8, 5, -4], ![4, -23, 20, -12, 10], ![-6, 30, -23, 15, -12], ![3, -22, 20, -11, 10], ![-7, 30, -22, 15, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N2 : Nat.card (O ⧸ I43N2) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N2)

lemma isPrimeI43N2 : Ideal.IsPrime I43N2 := prime_ideal_of_norm_prime hp43.out _ NI43N2
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![-1041, -109, 118, -83, 92]] ![![589, 113, -104, 66, -62]]
  ![![-166029, -16684, 18920, -13033, 14728]] where
 M := ![![![-166029, -16684, 18920, -13033, 14728]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![-166029, -16684, 18920, -13033, 14728]] ![![33, 10, -8, 5, -4]]
  ![![43, 0, 0, 0, 0]] where
 M := ![![![263203, 19608, -25284, 18146, -22102]]]
 hmul := by decide  
 g := ![![![![6121, 456, -588, 422, -514]]]]
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


def P47P0 : CertificateIrreducibleZModOfList' 47 5 2 5 [18, 29, 5, 30, 43, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 18, 31, 25, 4], [19, 5, 46, 30, 39], [15, 40, 30, 18, 46], [16, 30, 34, 21, 5], [0, 1]]
 g := ![![[13, 44, 11, 23, 4], [17, 6, 20, 20, 14], [9, 24, 5, 12, 16], [1], []], ![[14, 27, 33, 10, 8, 37, 42, 36], [40, 12, 40, 43, 21, 21, 27, 24], [36, 39, 18, 42, 12, 3, 20, 25], [29, 36, 44, 42, 45, 36, 7, 1], [7, 39, 29, 16]], ![[1, 35, 37, 31, 22, 37, 11, 46], [38, 16, 30, 39, 21, 6, 36, 39], [32, 41, 26, 22, 46, 27, 0, 43], [46, 39, 32, 27, 16, 10], [23, 27, 11, 17]], ![[31, 10, 44, 44, 37, 15, 9, 41], [23, 39, 46, 21, 13, 18, 30, 35], [19, 4, 34, 3, 33, 16, 30, 33], [15, 20, 25, 41, 39, 34, 45, 44], [29, 12, 15, 1]], ![[42, 32, 8, 17, 45, 34, 28, 31], [4, 31, 3, 4, 11, 42, 22, 29], [2, 43, 43, 18, 8, 1, 43, 35], [21, 3, 1, 21, 23, 27, 16, 15], [19, 2, 28, 25]]]
 h' := ![![[1, 18, 31, 25, 4], [23, 28, 27, 10, 45], [26, 7, 25, 35, 25], [29, 18, 42, 17, 4], [0, 0, 1], [0, 1]], ![[19, 5, 46, 30, 39], [6, 9, 35, 43, 44], [31, 17, 19, 28, 37], [16, 33, 29, 3, 21], [16, 24, 14, 8, 24], [1, 18, 31, 25, 4]], ![[15, 40, 30, 18, 46], [20, 43, 21, 21, 37], [18, 38, 37, 20, 46], [44, 4, 3, 26, 27], [41, 24, 19, 9], [19, 5, 46, 30, 39]], ![[16, 30, 34, 21, 5], [19, 42, 34, 39, 10], [28, 33, 7, 44, 24], [3, 20, 22, 24, 25], [32, 2, 45, 6, 35], [15, 40, 30, 18, 46]], ![[0, 1], [23, 19, 24, 28, 5], [12, 46, 6, 14, 9], [35, 19, 45, 24, 17], [8, 44, 15, 24, 35], [16, 30, 34, 21, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19, 40, 32, 44], [], [], []]
 b := ![[], [35, 14, 42, 46, 36], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 5
  hpos := by decide
  P := [18, 29, 5, 30, 43, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9128246, 56543726, 43727578, -49087082, -2606808]
  a := ![-1, -4, 2, -5, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![194218, 1203058, 930374, -1044406, -55464]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![307, 93, -76, 47, -38]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![307, 93, -76, 47, -38]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![17, 1, 25, 1, 0], ![52, 49, 12, 0, 1]] where
  M :=![![![307, 93, -76, 47, -38], ![-760, -225, 186, -114, 94], ![940, 277, -225, 139, -114], ![-760, -214, 184, -111, 92], ![920, 264, -214, 138, -111]]]
  hmulB := by decide  
  f := ![![![-1, 3, 2, -1, 0]], ![![0, 1, 6, 4, -2]], ![![-20, -9, 1, 7, 4]], ![![-9, -3, 1, 3, 2]], ![![-4, 3, 8, 4, -1]]]
  g := ![![![28, 36, -15, 47, -38], ![-70, -89, 36, -114, 94], ![85, 108, -44, 139, -114], ![-69, -87, 35, -111, 92], ![82, 105, -44, 138, -111]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [47, 34, 33, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 25, 45], [19, 27, 8], [0, 1]]
 g := ![![[9, 7, 6], [32, 43], [33, 44, 17], [15, 29], [1]], ![[25, 40, 42, 26], [15, 46], [9, 31], [44, 24], [29, 12, 19, 18]], ![[33, 16, 4, 41], [9, 25], [4, 28, 50, 30], [37, 44], [35, 46, 1, 35]]]
 h' := ![![[1, 25, 45], [17, 16, 18], [39, 19, 34], [20, 51, 21], [6, 19, 20], [0, 1]], ![[19, 27, 8], [9, 23, 40], [48, 22, 24], [43, 49], [16, 9, 17], [1, 25, 45]], ![[0, 1], [14, 14, 48], [38, 12, 48], [39, 6, 32], [20, 25, 16], [19, 27, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 42], []]
 b := ![[], [7, 50, 45], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [47, 34, 33, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-96867, 38664, 74890, -127057, 71632]
  a := ![3, -4, 7, -8, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-31354, -63099, 45127, -127057, 71632]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 148877 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, -3, -2, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![1, -3, -2, 1, 0]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![30, 28, 1, 0, 0], ![8, 0, 0, 1, 0], ![0, 4, 0, 0, 1]] where
  M :=![![![1, -3, -2, 1, 0], ![0, -1, -6, -4, 2], ![20, 9, -1, -7, -4], ![-40, -14, 12, 3, -8], ![-80, -62, -14, 16, 3]]]
  hmulB := by decide  
  f := ![![![-307, -93, 76, -47, 38]], ![![760, 225, -186, 114, -94]], ![![210, 61, -51, 31, -26]], ![![-32, -10, 8, -5, 4]], ![![40, 12, -10, 6, -5]]]
  g := ![![![1, 1, -2, 1, 0], ![4, 3, -6, -4, 2], ![2, 1, -1, -7, -4], ![-8, -6, 12, 3, -8], ![4, 6, -14, 16, 3]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P1 : CertificateIrreducibleZModOfList' 53 2 2 5 [29, 33, 1] where
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
 g := ![![[45, 11], [42], [], [], [20, 1]], ![[0, 42], [42], [], [], [40, 52]]]
 h' := ![![[20, 52], [1, 45], [0, 28], [9], [3], [0, 1]], ![[0, 1], [0, 8], [30, 25], [9], [3], [20, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50]]
 b := ![[], [15, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N1 : CertifiedPrimeIdeal' SI53N1 53 where
  n := 2
  hpos := by decide
  P := [29, 33, 1]
  hirr := P53P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![183, 97, 76, 89, 486]
  a := ![1, 0, 2, -1, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-53, -75, 76, 89, 486]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N1 B_one_repr
lemma NI53N1 : Nat.card (O ⧸ I53N1) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![307, 93, -76, 47, -38]] ![![1, -3, -2, 1, 0]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-201, -57, 46, -30, 24]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-201, -57, 46, -30, 24]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![58, 14, 42, 1, 0], ![42, 52, 20, 0, 1]] where
  M :=![![![-201, -57, 46, -30, 24], ![480, 133, -114, 68, -60], ![-600, -177, 133, -84, 68], ![440, 108, -120, 65, -54], ![-540, -164, 108, -93, 65]]]
  hmulB := by decide  
  f := ![![![-179, -19, 20, -14, 16]], ![![320, 33, -38, 24, -28]], ![![-280, -27, 33, -24, 24]], ![![-298, -30, 34, -25, 26]], ![![58, 6, -8, 3, -5]]]
  g := ![![![9, -15, 14, -30, 24], ![-16, 39, -30, 68, -60], ![24, -43, 39, -84, 68], ![-18, 34, -30, 65, -54], ![36, -38, 46, -93, 65]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [20, 15, 26, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [27, 30, 51], [6, 28, 8], [0, 1]]
 g := ![![[37, 50, 22], [39, 22, 16], [40, 36], [12, 19, 27], [1]], ![[35, 36, 19, 41], [37, 32, 4, 41], [14, 22], [45, 9, 36, 4], [1, 19, 15, 19]], ![[23, 52, 4, 37], [33, 46, 12, 50], [25, 48], [57, 32, 53, 30], [2, 29, 29, 40]]]
 h' := ![![[27, 30, 51], [46, 31, 50], [42, 19, 55], [55, 17, 53], [39, 44, 33], [0, 1]], ![[6, 28, 8], [44, 8, 31], [51, 16, 31], [53, 33, 50], [16, 20, 41], [27, 30, 51]], ![[0, 1], [36, 20, 37], [23, 24, 32], [46, 9, 15], [58, 54, 44], [6, 28, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26, 43], []]
 b := ![[], [7, 3, 57], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [20, 15, 26, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-160, 166, 126, -388, 178]
  a := ![4, 1, -1, 2, -1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![252, -62, 218, -388, 178]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 205379 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-179, -19, 20, -14, 16]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![-179, -19, 20, -14, 16]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![20, 17, 1, 0, 0], ![14, 46, 0, 1, 0], ![24, 51, 0, 0, 1]] where
  M :=![![![-179, -19, 20, -14, 16], ![320, 33, -38, 24, -28], ![-280, -27, 33, -24, 24], ![80, 4, -8, 9, -10], ![-100, -24, 4, -3, 9]]]
  hmulB := by decide  
  f := ![![![-201, -57, 46, -30, 24]], ![![480, 133, -114, 68, -60]], ![![60, 16, -15, 8, -8]], ![![334, 92, -80, 47, -42]], ![![324, 89, -78, 45, -41]]]
  g := ![![![-13, -9, 20, -14, 16], ![24, 17, -38, 24, -28], ![-20, -12, 33, -24, 24], ![6, 4, -8, 9, -10], ![-6, -7, 4, -3, 9]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P1 : CertificateIrreducibleZModOfList' 59 2 2 5 [52, 56, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 58], [0, 1]]
 g := ![![[51, 15], [16, 45], [16], [24, 20], [3, 1]], ![[37, 44], [33, 14], [16], [25, 39], [6, 58]]]
 h' := ![![[3, 58], [53, 29], [16, 35], [50, 4], [21, 16], [0, 1]], ![[0, 1], [22, 30], [3, 24], [3, 55], [10, 43], [3, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [24, 43]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N1 : CertifiedPrimeIdeal' SI59N1 59 where
  n := 2
  hpos := by decide
  P := [52, 56, 1]
  hirr := P59P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1427, 6775, 8106, 4230, 5323]
  a := ![7, 2, -24, 2, -23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5941, -10120, 8106, 4230, 5323]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N1 B_one_repr
lemma NI59N1 : Nat.card (O ⧸ I59N1) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-201, -57, 46, -30, 24]] ![![-179, -19, 20, -14, 16]]
  ![![59, 0, 0, 0, 0]] where
 M := ![![![59, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 35, 8, 11, 2]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![31, 35, 8, 11, 2]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![12, 53, 1, 0, 0], ![35, 34, 0, 1, 0], ![19, 15, 0, 0, 1]] where
  M :=![![![31, 35, 8, 11, 2], ![40, 63, 70, 14, 22], ![220, 187, 63, 59, 14], ![120, 194, 152, 49, 48], ![480, 424, 194, 128, 49]]]
  hmulB := by decide  
  f := ![![![-69, -63, -26, 23, 16]], ![![320, 97, -126, -68, 46]], ![![272, 78, -113, -57, 42]], ![![125, 15, -78, -22, 32]], ![![29, -16, -42, -1, 19]]]
  g := ![![![-8, -13, 8, 11, 2], ![-28, -73, 70, 14, 22], ![-47, -88, 63, 59, 14], ![-71, -168, 152, 49, 48], ![-119, -245, 194, 128, 49]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [17, 60, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 60], [0, 1]]
 g := ![![[43, 58], [3], [49, 46], [7, 12], [1, 1]], ![[40, 3], [3], [34, 15], [19, 49], [2, 60]]]
 h' := ![![[1, 60], [24, 34], [21, 8], [3, 31], [44, 45], [0, 1]], ![[0, 1], [58, 27], [29, 53], [34, 30], [28, 16], [1, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [10, 41]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [17, 60, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-522, 450, 435, 484, 328]
  a := ![1, 2, -7, 1, -8]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-474, -721, 435, 484, 328]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 16, -6, -9, 2]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![29, 16, -6, -9, 2]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![17, 38, 1, 0, 0], ![25, 29, 0, 1, 0], ![56, 39, 0, 0, 1]] where
  M :=![![![29, 16, -6, -9, 2], ![40, 47, 32, -14, -18], ![-180, -72, 47, 41, -14], ![-160, -174, -88, 61, 50], ![500, 176, -174, -113, 61]]]
  hmulB := by decide  
  f := ![![![-71, -98, -78, -25, -24]], ![![-480, -437, -196, -132, -50]], ![![-327, -310, -151, -92, -40]], ![![-275, -265, -134, -78, -36]], ![![-396, -397, -214, -115, -59]]]
  g := ![![![4, 7, -6, -9, 2], ![14, -1, 32, -14, -18], ![-20, -41, 47, 41, -14], ![-49, -9, -88, 61, 50], ![47, 126, -174, -113, 61]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P1 : CertificateIrreducibleZModOfList' 61 2 2 5 [47, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [50, 60], [0, 1]]
 g := ![![[21, 13], [56], [6, 39], [54, 47], [50, 1]], ![[0, 48], [56], [4, 22], [25, 14], [39, 60]]]
 h' := ![![[50, 60], [32, 14], [23, 19], [24, 51], [29, 13], [0, 1]], ![[0, 1], [0, 47], [58, 42], [12, 10], [8, 48], [50, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [12, 41]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N1 : CertifiedPrimeIdeal' SI61N1 61 where
  n := 2
  hpos := by decide
  P := [47, 11, 1]
  hirr := P61P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![289, 1660, 1978, 1010, 164]
  a := ![3, 5, 2, 10, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1111, -1790, 1978, 1010, 164]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N1 B_one_repr
lemma NI61N1 : Nat.card (O ⧸ I61N1) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 1, 0, 0, 0]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![1, 1, 0, 0, 0]] 
 ![![61, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![30, 0, 1, 0, 0], ![15, 0, 0, 1, 0], ![23, 0, 0, 0, 1]] where
  M :=![![![1, 1, 0, 0, 0], ![0, 1, 2, 0, 0], ![0, 1, 1, 2, 0], ![0, 0, 0, 1, 2], ![20, 12, 0, -1, 1]]]
  hmulB := by decide  
  f := ![![![-99, -3, 6, -4, 8]], ![![1, 0, 0, 0, 0]], ![![-50, -1, 3, -2, 4]], ![![-25, -1, 2, -1, 2]], ![![-37, -1, 2, -1, 3]]]
  g := ![![![0, 1, 0, 0, 0], ![-1, 1, 2, 0, 0], ![-1, 1, 1, 2, 0], ![-1, 0, 0, 1, 2], ![0, 12, 0, -1, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![31, 35, 8, 11, 2]] ![![29, 16, -6, -9, 2]]
  ![![99, 3, -6, 4, -8]] where
 M := ![![![99, 3, -6, 4, -8]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![99, 3, -6, 4, -8]] ![![1, 1, 0, 0, 0]]
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


lemma PB547I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB547I1 : PrimesBelowBoundCertificateInterval O 23 61 547 where
  m := 9
  g := ![3, 2, 4, 3, 3, 1, 2, 2, 3]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB547I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0, I29N1, I29N2]
    · exact ![I31N0, I31N1]
    · exact ![I37N0, I37N1, I37N2, I37N3]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0, I43N1, I43N2]
    · exact ![I47N0]
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
    · exact ![24389, 29, 29]
    · exact ![923521, 31]
    · exact ![1369, 37, 37, 37]
    · exact ![1681, 1681, 41]
    · exact ![1849, 1849, 43]
    · exact ![229345007]
    · exact ![148877, 2809]
    · exact ![205379, 3481]
    · exact ![3721, 3721, 61]
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
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
      exact NI37N2
      exact NI37N3
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
  β := ![I29N1, I29N2, I31N1, I37N1, I37N2, I37N3, I41N2, I43N2, I61N2]
  Il := ![[I29N1, I29N2], [I31N1], [I37N1, I37N2, I37N3], [I41N2], [I43N2], [], [], [], [I61N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
