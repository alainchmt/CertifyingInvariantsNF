
import IdealArithmetic.Examples.NF5_3_729000000_3.RI5_3_729000000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-311, -355, 60, -7, 120]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![-311, -355, 60, -7, 120]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![3, 14, 1, 1, 0], ![0, 1, 24, 0, 1]] where
  M :=![![![-311, -355, 60, -7, 120], ![-480, -505, 10, 14, 198], ![-396, -419, 89, -103, 240], ![-240, -244, 296, 65, -168], ![192, 174, -154, 122, -113]]]
  hmulB := by decide  
  f := ![![![-57667, -14293, 79122, 17435, 55842]], ![![-223368, -55359, 306466, 67532, 216294]], ![![-432588, -107213, 593523, 130787, 418890]], ![![-153753, -38106, 210953, 46485, 148884]], ![![-387648, -96075, 531864, 117200, 375373]]]
  g := ![![![-10, -13, -97, -7, 120], ![-18, -31, -164, 14, 198], ![-3, 27, -192, -103, 240], ![-15, -34, 147, 65, -168], ![-6, -49, 84, 122, -113]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 3 2 4 [25, 12, 27, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 14, 10], [2, 14, 19], [0, 1]]
 g := ![![[0, 25, 20], [], [3, 18, 4], [1]], ![[15, 23, 20, 2], [25, 4], [3, 20, 4, 18], [4, 16, 23, 14]], ![[19, 7, 8, 19], [20, 4], [18, 16, 12, 26], [9, 13, 25, 15]]]
 h' := ![![[0, 14, 10], [28, 1, 7], [12, 23], [4, 17, 2], [0, 1]], ![[2, 14, 19], [12, 20, 21], [12, 3, 27], [16, 16, 24], [0, 14, 10]], ![[0, 1], [22, 8, 1], [0, 3, 2], [15, 25, 3], [2, 14, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 12], []]
 b := ![[], [24, 5, 22], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 3
  hpos := by decide
  P := [25, 12, 27, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![402453, 188243, -382656, -716825, 177468]
  a := ![0, -8, -3, 2, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![88032, 346425, -135347, -716825, 177468]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 24389 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-155, 36, 0, 10, -10]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![-155, 36, 0, 10, -10]] 
 ![![29, 0, 0, 0, 0], ![13, 1, 0, 0, 0], ![17, 0, 1, 0, 0], ![28, 0, 0, 1, 0], ![12, 0, 0, 0, 1]] where
  M :=![![![-155, 36, 0, 10, -10], ![40, -115, 12, -10, 40], ![-80, -24, 5, 2, 10], ![-40, 12, 0, 3, -4], ![-24, 38, -4, 4, -13]]]
  hmulB := by decide  
  f := ![![![-135, -32, 184, 42, 134]], ![![-79, -19, 108, 24, 78]], ![![-115, -28, 157, 36, 112]], ![![-188, -44, 256, 59, 188]], ![![-108, -26, 148, 32, 107]]]
  g := ![![![-27, 36, 0, 10, -10], ![39, -115, 12, -10, 40], ![-1, -24, 5, 2, 10], ![-8, 12, 0, 3, -4], ![-14, 38, -4, 4, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1

def I29N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![331, -356, 32, -41, 120]] i)))

def SI29N2: IdealEqSpanCertificate' Table ![![331, -356, 32, -41, 120]] 
 ![![29, 0, 0, 0, 0], ![14, 1, 0, 0, 0], ![18, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![10, 0, 0, 0, 1]] where
  M :=![![![331, -356, 32, -41, 120], ![-480, 41, 8, 26, -6], ![12, -204, 23, -15, 72], ![96, -90, 8, -11, 30], ![172, -40, 0, -11, 11]]]
  hmulB := by decide  
  f := ![![![239, 62, -328, -75, -222]], ![![146, 37, -200, -46, -138]], ![![210, 54, -289, -63, -198]], ![![204, 54, -280, -65, -186]], ![![170, 42, -232, -55, -163]]]
  g := ![![![139, -356, 32, -41, 120], ![-50, 41, 8, 26, -6], ![66, -204, 23, -15, 72], ![36, -90, 8, -11, 30], ![26, -40, 0, -11, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N2 : Nat.card (O ⧸ I29N2) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N2)

lemma isPrimeI29N2 : Ideal.IsPrime I29N2 := prime_ideal_of_norm_prime hp29.out _ NI29N2
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![-311, -355, 60, -7, 120]] ![![-155, 36, 0, 10, -10]]
  ![![26605, 32665, -4440, 1019, -12022]] where
 M := ![![![26605, 32665, -4440, 1019, -12022]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI29N1 : IdealMulLeCertificate' Table 
  ![![26605, 32665, -4440, 1019, -12022]] ![![331, -356, 32, -41, 120]]
  ![![29, 0, 0, 0, 0]] where
 M := ![![![-8896185, -6837185, 1018712, -53882, 2575258]]]
 hmul := by decide  
 g := ![![![![-306765, -235765, 35128, -1858, 88802]]]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29197, 7237, -40058, -8827, -28272]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![29197, 7237, -40058, -8827, -28272]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![11, 25, 7, 1, 0], ![9, 5, 15, 0, 1]] where
  M :=![![![29197, 7237, -40058, -8827, -28272], ![113088, 28029, -155158, -34190, -109506], ![219012, 54281, -300489, -66215, -212076], ![367608, 91108, -504368, -111141, -355968], ![322152, 79842, -442002, -97398, -311951]]]
  hmulB := by decide  
  f := ![![![-269, 173, -16, 25, -54]], ![![216, -127, 22, -28, 42]], ![![-84, 49, -1, 29, -42]], ![![59, -27, 9, -7, 6]], ![![-87, 55, -1, 16, -29]]]
  g := ![![![12282, 11912, 14381, -8827, -28272], ![47572, 46139, 55702, -34190, -109506], ![92131, 89356, 107876, -66215, -212076], ![154641, 149983, 181069, -111141, -355968], ![135519, 131437, 158679, -97398, -311951]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 3 2 4 [5, 16, 15, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [13, 15, 20], [3, 15, 11], [0, 1]]
 g := ![![[16, 28, 16], [28, 3, 10], [24, 19, 8], [1]], ![[24, 8, 11, 14], [29, 26, 0, 10], [24, 13, 13, 1], [25, 16, 21, 2]], ![[6, 7, 10, 15], [2, 16, 29, 15], [0, 17, 14, 13], [29, 15, 19, 29]]]
 h' := ![![[13, 15, 20], [15, 18, 4], [4, 11, 14], [26, 15, 16], [0, 1]], ![[3, 15, 11], [22, 11, 17], [19, 18, 27], [26, 26, 13], [13, 15, 20]], ![[0, 1], [14, 2, 10], [15, 2, 21], [6, 21, 2], [3, 15, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 1], []]
 b := ![[], [13, 16, 17], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 3
  hpos := by decide
  P := [5, 16, 15, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-22140777, -31958916, 82618622, -123247636, 17349944]
  a := ![3, -61, 2, -69, 11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![37981733, 95563944, 22100094, -123247636, 17349944]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 29791 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-269, 173, -16, 25, -54]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![-269, 173, -16, 25, -54]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![18, 24, 1, 0, 0], ![2, 7, 0, 1, 0], ![0, 9, 0, 0, 1]] where
  M :=![![![-269, 173, -16, 25, -54], ![216, -127, 22, -28, 42], ![-84, 49, -1, 29, -42], ![-24, 92, -88, 5, 24], ![-96, 48, 18, -24, 7]]]
  hmulB := by decide  
  f := ![![![29197, 7237, -40058, -8827, -28272]], ![![113088, 28029, -155158, -34190, -109506]], ![![111570, 27653, -153075, -33731, -108036]], ![![39278, 9735, -53890, -11875, -38034]], ![![43224, 10713, -59304, -13068, -41855]]]
  g := ![![![-1, 28, -16, 25, -54], ![-4, -27, 22, -28, 42], ![-4, 8, -1, 29, -42], ![50, 63, -88, 5, 24], ![-12, -9, 18, -24, 7]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P1 : CertificateIrreducibleZModOfList' 31 2 2 4 [16, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [13, 30], [0, 1]]
 g := ![![[5, 2], [22, 2], [16, 4], [13, 1]], ![[0, 29], [17, 29], [6, 27], [26, 30]]]
 h' := ![![[13, 30], [20, 8], [23, 8], [9, 29], [0, 1]], ![[0, 1], [0, 23], [3, 23], [14, 2], [13, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [14, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N1 : CertifiedPrimeIdeal' SI31N1 31 where
  n := 2
  hpos := by decide
  P := [16, 18, 1]
  hirr := P31P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8837, 693, 13886, -1533, 17405]
  a := ![1, 26, 4, 10, 23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-8249, -15435, 13886, -1533, 17405]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N1 B_one_repr
lemma NI31N1 : Nat.card (O ⧸ I31N1) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![29197, 7237, -40058, -8827, -28272]] ![![-269, 173, -16, 25, -54]]
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

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0, 0, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0, 0, 0]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![0, 0, 0, 0, 37]] where
  M :=![![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![0, 0, 0, 0, 37]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 5 2 5 [29, 14, 36, 9, 30, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 0, 10, 1, 3], [14, 25, 5, 28, 15], [28, 6, 22, 13, 2], [9, 5, 0, 32, 17], [0, 1]]
 g := ![![[13, 8, 18, 12, 36], [17, 11, 8, 16], [12, 33, 3, 7, 1], [], []], ![[30, 9, 31, 8, 36, 1, 25, 30], [14, 32, 2, 11], [25, 11, 36, 30, 27, 17, 16, 26], [16, 19, 20, 34], [22, 19, 32, 9]], ![[11, 27, 10, 7, 0, 18, 8, 5], [31, 5, 14, 16], [17, 17, 20, 21, 16, 22, 35, 19], [25, 10, 28, 11], [12, 15, 10, 3]], ![[2, 2, 22, 24, 1, 24, 30, 31], [23, 9, 25, 12], [29, 29, 8, 4, 36, 32, 21, 23], [0, 13, 30, 3], [19, 4, 6, 4]], ![[22, 15, 21, 23, 10, 20, 30, 22], [33, 2, 1, 1], [2, 13, 1, 30, 4, 29, 7, 19], [19, 28, 5, 27], [11, 35, 3, 30]]]
 h' := ![![[30, 0, 10, 1, 3], [28, 4, 19, 17, 6], [22, 22, 18, 13, 33], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[14, 25, 5, 28, 15], [29, 3, 16, 8, 26], [19, 17, 34, 33, 14], [26, 28, 20, 18, 13], [3, 29, 20, 23, 21], [30, 0, 10, 1, 3]], ![[28, 6, 22, 13, 2], [36, 28, 14, 12, 32], [11, 36, 4, 3, 33], [31, 27, 13, 36, 13], [33, 23, 18, 11, 23], [14, 25, 5, 28, 15]], ![[9, 5, 0, 32, 17], [3, 0, 27, 0, 21], [35, 30, 2, 28, 30], [10, 17, 9, 2, 17], [11, 28, 21, 33, 22], [28, 6, 22, 13, 2]], ![[0, 1], [1, 2, 35, 0, 26], [25, 6, 16, 34, 1], [1, 2, 32, 18, 30], [21, 31, 14, 7, 8], [9, 5, 0, 32, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13, 18, 29, 2], [], [], []]
 b := ![[], [22, 34, 17, 24, 24], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 5
  hpos := by decide
  P := [29, 14, 36, 9, 30, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![209625513799, 305136883896, -94476660102, -903702282296, 959847036896]
  a := ![-1, -6, -4, 13, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![5665554427, 8246942808, -2553423246, -24424386008, 25941811808]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2117, -3363, 7626, 1347, 5934]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![-2117, -3363, 7626, 1347, 5934]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![31, 31, 1, 0, 0], ![23, 39, 0, 1, 0], ![1, 31, 0, 0, 1]] where
  M :=![![![-2117, -3363, 7626, 1347, 5934], ![-23736, -3665, 28878, 6624, 19950], ![-39900, -10755, 56185, 12279, 39822], ![-67776, -17568, 94272, 20683, 66684], ![-59136, -15552, 82626, 18102, 58489]]]
  hmulB := by decide  
  f := ![![![515, 471, -816, 69, 264]], ![![-1056, -691, 2526, -2034, 942]], ![![-455, -221, 1345, -1386, 786]], ![![-451, -156, 1482, -1856, 1206]], ![![-797, -500, 1956, -1701, 859]]]
  g := ![![![-6718, -11616, 7626, 1347, 5934], ![-26616, -43309, 28878, 6624, 19950], ![-51314, -84533, 56185, 12279, 39822], ![-86161, -141801, 94272, 20683, 66684], ![-75497, -124295, 82626, 18102, 58489]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [1, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 40], [0, 1]]
 g := ![![[19, 1], [2], [8], [26, 33], [1]], ![[0, 40], [2], [8], [14, 8], [1]]]
 h' := ![![[22, 40], [19, 1], [12, 17], [15, 7], [40, 22], [0, 1]], ![[0, 1], [0, 40], [17, 24], [5, 34], [32, 19], [22, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [5, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [1, 19, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6303, -7578, 6636, 14182, -17218]
  a := ![0, -2, 4, -26, 22]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-12707, -5674, 6636, 14182, -17218]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1915, 189, -2730, -627, -1842]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![1915, 189, -2730, -627, -1842]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![33, 16, 1, 0, 0], ![5, 7, 0, 1, 0], ![34, 14, 0, 0, 1]] where
  M :=![![![1915, 189, -2730, -627, -1842], ![7368, 1615, -10674, -2364, -7446], ![14892, 3429, -20723, -4587, -14538], ![25392, 6228, -34848, -7685, -24576], ![22392, 5592, -30558, -6732, -21587]]]
  hmulB := by decide  
  f := ![![![1379, 1503, -1812, -1869, 2712]], ![![-10848, -9595, 19278, -2598, -5790]], ![![-2841, -2354, 5407, -1914, -408]], ![![-889, -590, 2022, -1736, 894]], ![![-3242, -2578, 6414, -3024, 289]]]
  g := ![![![3848, 1806, -2730, -627, -1842], ![15234, 7151, -10674, -2364, -7446], ![29658, 13918, -20723, -4587, -14538], ![49985, 23455, -34848, -7685, -24576], ![43864, 20582, -30558, -6732, -21587]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P1 : CertificateIrreducibleZModOfList' 41 2 2 5 [15, 27, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 40], [0, 1]]
 g := ![![[10, 5], [16], [32], [28, 32], [1]], ![[39, 36], [16], [32], [25, 9], [1]]]
 h' := ![![[14, 40], [4, 13], [30, 4], [31, 14], [26, 14], [0, 1]], ![[0, 1], [22, 28], [4, 37], [22, 27], [17, 27], [14, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [20, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N1 : CertifiedPrimeIdeal' SI41N1 41 where
  n := 2
  hpos := by decide
  P := [15, 27, 1]
  hirr := P41P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4361, -4143, 7760, 1081, -3186]
  a := ![13, -6, -3, 8, -19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3842, -2226, 7760, 1081, -3186]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N1 B_one_repr
lemma NI41N1 : Nat.card (O ⧸ I41N1) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, -3, 2, 0, 2]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![3, -3, 2, 0, 2]] 
 ![![41, 0, 0, 0, 0], ![29, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![25, 0, 0, 1, 0], ![35, 0, 0, 0, 1]] where
  M :=![![![3, -3, 2, 0, 2], ![-8, 1, 6, 2, 4], ![-8, -3, 13, 2, 10], ![-16, -6, 24, 5, 14], ![-12, -4, 18, 5, 13]]]
  hmulB := by decide  
  f := ![![![-269, -295, 40, -8, 110]], ![![-201, -220, 30, -6, 82]], ![![-74, -81, 11, -2, 30]], ![![-165, -181, 24, -5, 68]], ![![-227, -249, 34, -7, 93]]]
  g := ![![![0, -3, 2, 0, 2], ![-7, 1, 6, 2, 4], ![-11, -3, 13, 2, 10], ![-17, -6, 24, 5, 14], ![-16, -4, 18, 5, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![-2117, -3363, 7626, 1347, 5934]] ![![1915, 189, -2730, -627, -1842]]
  ![![251810905, 61890240, -344628954, -76002354, -243127506]] where
 M := ![![![251810905, 61890240, -344628954, -76002354, -243127506]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![251810905, 61890240, -344628954, -76002354, -243127506]] ![![3, -3, 2, 0, 2]]
  ![![41, 0, 0, 0, 0]] where
 M := ![![![7150910163, 1768868535, -9805564756, -2161126728, -6919797304]]]
 hmul := by decide  
 g := ![![![![174412443, 43143135, -239160116, -52710408, -168775544]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3497, 1820, -116, 297, -582]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![-3497, 1820, -116, 297, -582]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![38, 5, 20, 17, 1]] where
  M :=![![![-3497, 1820, -116, 297, -582], ![2328, -1855, 148, -244, 618], ![-1236, 376, -1, 83, -114], ![-936, 506, -40, 95, -174], ![-972, 714, -68, 97, -227]]]
  hmulB := by decide  
  f := ![![![-347, -86, 476, 105, 336]], ![![-1344, -333, 1844, 406, 1302]], ![![-2604, -646, 3573, 787, 2520]], ![![-4368, -1082, 5992, 1323, 4230]], ![![-3490, -865, 4788, 1056, 3379]]]
  g := ![![![433, 110, 268, 237, -582], ![-492, -115, -284, -250, 618], ![72, 22, 53, 47, -114], ![132, 32, 80, 71, -174], ![178, 43, 104, 92, -227]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 4 2 5 [18, 13, 33, 30, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 15, 13, 37], [39, 5, 20, 1], [26, 22, 10, 5], [0, 1]]
 g := ![![[22, 30, 10, 36], [4, 6, 20, 16], [28, 39, 6], [13, 1], []], ![[29, 31, 18, 20, 21, 33], [3, 12, 10, 36, 31, 19], [25, 11, 38], [11, 39, 42, 3], [19, 11, 36]], ![[4, 0, 32, 30, 27, 23], [22, 6, 18, 11, 0, 36], [22, 19, 21], [0, 28, 21, 6, 10, 14], [34, 10, 1]], ![[4, 35, 2, 27, 41, 33], [6, 27, 21, 2, 20, 32], [0, 4, 36], [37, 16, 18, 31, 6, 27], [32, 38, 25]]]
 h' := ![![[34, 15, 13, 37], [14, 36, 31, 37], [29, 20, 2, 39], [24, 28, 31, 7], [0, 0, 1], [0, 1]], ![[39, 5, 20, 1], [34, 6, 20, 4], [34, 18, 39, 41], [22, 25, 34, 34], [40, 16, 35], [34, 15, 13, 37]], ![[26, 22, 10, 5], [30, 36, 37, 18], [1, 6, 13, 37], [28, 19, 11, 8], [6, 26, 14, 33], [39, 5, 20, 1]], ![[0, 1], [4, 8, 41, 27], [1, 42, 32, 12], [1, 14, 10, 37], [14, 1, 36, 10], [26, 22, 10, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [7, 17, 15], []]
 b := ![[], [], [42, 23, 5, 28], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 4
  hpos := by decide
  P := [18, 13, 33, 30, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-96868535, -80019318, 184678228, -66469162, -12587075]
  a := ![-1, 0, 2, -8, 11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![8870705, -397301, 10149296, 3430491, -12587075]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 3418801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![347, 86, -476, -105, -336]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![347, 86, -476, -105, -336]] 
 ![![43, 0, 0, 0, 0], ![25, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![13, 0, 0, 1, 0], ![35, 0, 0, 0, 1]] where
  M :=![![![347, 86, -476, -105, -336], ![1344, 333, -1844, -406, -1302], ![2604, 646, -3573, -787, -2520], ![4368, 1082, -5992, -1323, -4230], ![3828, 948, -5252, -1157, -3709]]]
  hmulB := by decide  
  f := ![![![3497, -1820, 116, -297, 582]], ![![1979, -1015, 64, -167, 324]], ![![842, -432, 27, -71, 138]], ![![1079, -562, 36, -92, 180]], ![![2869, -1498, 96, -244, 479]]]
  g := ![![![374, 86, -476, -105, -336], ![1449, 333, -1844, -406, -1302], ![2805, 646, -3573, -787, -2520], ![4709, 1082, -5992, -1323, -4230], ![4128, 948, -5252, -1157, -3709]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![-3497, 1820, -116, 297, -582]] ![![347, 86, -476, -105, -336]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4451, -2699, 192, -404, 876]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![4451, -2699, 192, -404, 876]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![45, 6, 1, 0, 0], ![12, 34, 0, 1, 0], ![11, 24, 0, 0, 1]] where
  M :=![![![4451, -2699, 192, -404, 876], ![-3504, 2083, -142, 316, -672], ![1344, -835, 67, -122, 276], ![1200, -734, 64, -107, 246], ![1404, -846, 70, -125, 281]]]
  hmulB := by decide  
  f := ![![![-59, -53, 102, -8, -36]], ![![144, 99, -322, 256, -120]], ![![-33, -32, 51, 14, -36]], ![![60, 32, -156, 179, -114]], ![![61, 37, -148, 147, -85]]]
  g := ![![![-191, -237, 192, -404, 876], ![138, 177, -142, 316, -672], ![-69, -79, 67, -122, 276], ![-66, -72, 64, -107, 246], ![-71, -80, 70, -125, 281]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [15, 27, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 46], [0, 1]]
 g := ![![[30, 1], [31, 7], [29, 9], [21, 24], [1]], ![[3, 46], [30, 40], [21, 38], [31, 23], [1]]]
 h' := ![![[20, 46], [5, 1], [35, 30], [14, 3], [32, 20], [0, 1]], ![[0, 1], [25, 46], [24, 17], [27, 44], [9, 27], [20, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [36, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [15, 27, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-16135, -12357, 26190, 2612, -6566]
  a := ![3, 10, 7, -15, 35]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-24549, -2143, 26190, 2612, -6566]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 3, -6, 2, 2]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![3, 3, -6, 2, 2]] 
 ![![47, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![45, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![15, 0, 0, 0, 1]] where
  M :=![![![3, 3, -6, 2, 2], ![-8, -3, 18, -18, 16], ![-32, -29, 45, 28, -38], ![80, 74, -152, 45, 38], ![4, 16, 6, -51, 65]]]
  hmulB := by decide  
  f := ![![![-28283, 16889, -1184, 2550, -5470]], ![![-738, 433, -30, 66, -140]], ![![-27265, 16278, -1141, 2458, -5272]], ![![-765, 457, -32, 69, -148]], ![![-9215, 5505, -386, 831, -1783]]]
  g := ![![![5, 3, -6, 2, 2], ![-22, -3, 18, -18, 16], ![-31, -29, 45, 28, -38], ![131, 74, -152, 45, 38], ![-26, 16, 6, -51, 65]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1

def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7685, 4621, -326, 695, -1498]] i)))

def SI47N2: IdealEqSpanCertificate' Table ![![-7685, 4621, -326, 695, -1498]] 
 ![![47, 0, 0, 0, 0], ![15, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![22, 0, 0, 0, 1]] where
  M :=![![![-7685, 4621, -326, 695, -1498], ![5992, -3625, 254, -544, 1174], ![-2348, 1405, -103, 211, -458], ![-2080, 1256, -96, 187, -412], ![-2416, 1464, -110, 218, -479]]]
  hmulB := by decide  
  f := ![![![-315, -271, 576, -137, -112]], ![![-91, -82, 158, -11, -58]], ![![11, 18, -1, -62, 64]], ![![-170, -146, 312, -75, -60]], ![![-166, -156, 274, 30, -151]]]
  g := ![![![-932, 4621, -326, 695, -1498], ![731, -3625, 254, -544, 1174], ![-282, 1405, -103, 211, -458], ![-250, 1256, -96, 187, -412], ![-292, 1464, -110, 218, -479]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N2 : Nat.card (O ⧸ I47N2) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N2)

lemma isPrimeI47N2 : Ideal.IsPrime I47N2 := prime_ideal_of_norm_prime hp47.out _ NI47N2

def I47N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 91, -176, 11, 66]] i)))

def SI47N3: IdealEqSpanCertificate' Table ![![101, 91, -176, 11, 66]] 
 ![![47, 0, 0, 0, 0], ![18, 1, 0, 0, 0], ![26, 0, 1, 0, 0], ![39, 0, 0, 1, 0], ![31, 0, 0, 0, 1]] where
  M :=![![![101, 91, -176, 11, 66], ![-264, -185, 578, -440, 198], ![-396, -481, 409, 919, -1122], ![2376, 2140, -4136, 271, 1536], ![-144, 60, 678, -1488, 1229]]]
  hmulB := by decide  
  f := ![![![57211, -34421, 2266, -5209, 11052]], ![![20970, -12609, 814, -1912, 4038]], ![![32038, -19261, 1243, -2921, 6168]], ![![47835, -28753, 1850, -4362, 9204]], ![![38147, -22927, 1472, -3479, 7337]]]
  g := ![![![12, 91, -176, 11, 66], ![-20, -185, 578, -440, 198], ![-73, -481, 409, 919, -1122], ![281, 2140, -4136, 271, 1536], ![23, 60, 678, -1488, 1229]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N3 : Nat.card (O ⧸ I47N3) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N3)

lemma isPrimeI47N3 : Ideal.IsPrime I47N3 := prime_ideal_of_norm_prime hp47.out _ NI47N3
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![4451, -2699, 192, -404, 876]] ![![3, 3, -6, 2, 2]]
  ![![-15, 2, 16, 4, 10]] where
 M := ![![![-15, 2, 16, 4, 10]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![-15, 2, 16, 4, 10]] ![![-7685, 4621, -326, 695, -1498]]
  ![![57211, -34421, 2266, -5209, 11052]] where
 M := ![![![57211, -34421, 2266, -5209, 11052]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI47N2 : IdealMulLeCertificate' Table 
  ![![57211, -34421, 2266, -5209, 11052]] ![![101, 91, -176, 11, 66]]
  ![![47, 0, 0, 0, 0]] where
 M := ![![![47, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![475, 368, -60, 2, -142]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![475, 368, -60, 2, -142]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![51, 29, 23, 1, 0], ![50, 12, 0, 0, 1]] where
  M :=![![![475, 368, -60, 2, -142], ![568, 703, -116, 18, -272], ![544, 516, -113, 2, -218], ![152, 84, -80, -15, -76], ![-88, -174, -36, -20, 25]]]
  hmulB := by decide  
  f := ![![![15, 12, -28, 10, 2]], ![![-8, 3, 36, -78, 64]], ![![-128, -128, 195, 82, -170]], ![![-39, -37, 65, 7, -36]], ![![14, 14, -20, -12, 21]]]
  g := ![![![141, 38, -2, 2, -142], ![250, 65, -10, 18, -272], ![214, 58, -3, 2, -218], ![89, 27, 5, -15, -76], ![-6, 2, 8, -20, 25]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [14, 52, 49, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [51, 31, 29], [6, 21, 24], [0, 1]]
 g := ![![[38, 5, 42], [23, 42], [28, 16, 43], [19, 16], [1]], ![[36, 45, 22, 4], [30, 1], [46, 29, 12, 29], [32, 49], [38, 2, 21, 9]], ![[5, 8, 36, 11], [28, 40], [16, 16, 18, 7], [6, 15], [34, 29, 0, 44]]]
 h' := ![![[51, 31, 29], [13, 34, 28], [32, 40, 28], [36, 32, 34], [39, 1, 4], [0, 1]], ![[6, 21, 24], [40, 13, 37], [47, 40, 52], [23, 27, 52], [43, 11, 7], [51, 31, 29]], ![[0, 1], [43, 6, 41], [45, 26, 26], [47, 47, 20], [5, 41, 42], [6, 21, 24]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43, 3], []]
 b := ![[], [9, 2, 20], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [14, 52, 49, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![261860, 239605, -565182, 353545, 6288]
  a := ![1, 4, 2, -6, 13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-341195, -190352, -164089, 353545, 6288]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 148877 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, -5, 0, -1, 2]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![9, -5, 0, -1, 2]] 
 ![![53, 0, 0, 0, 0], ![22, 1, 0, 0, 0], ![23, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  M :=![![![9, -5, 0, -1, 2], ![-8, 3, 2, 0, -2], ![4, -1, -3, 3, -2], ![8, 4, -8, -5, 8], ![0, -4, 6, -4, 1]]]
  hmulB := by decide  
  f := ![![![373, 393, -58, 9, -148]], ![![166, 175, -26, 4, -66]], ![![171, 180, -27, 4, -68]], ![![9, 9, -2, 0, -4]], ![![47, 49, -8, 1, -19]]]
  g := ![![![2, -5, 0, -1, 2], ![-2, 3, 2, 0, -2], ![2, -1, -3, 3, -2], ![1, 4, -8, -5, 8], ![-1, -4, 6, -4, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1

def I53N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -1, 2, 1, -2]] i)))

def SI53N2: IdealEqSpanCertificate' Table ![![-1, -1, 2, 1, -2]] 
 ![![53, 0, 0, 0, 0], ![38, 1, 0, 0, 0], ![20, 0, 1, 0, 0], ![25, 0, 0, 1, 0], ![14, 0, 0, 0, 1]] where
  M :=![![![-1, -1, 2, 1, -2], ![8, 7, -14, 4, 2], ![-4, -1, 13, -19, 14], ![-32, -32, 48, 23, -44], ![16, 12, -34, 22, -7]]]
  hmulB := by decide  
  f := ![![![1107, -635, 48, -97, 208]], ![![778, -445, 34, -68, 146]], ![![424, -243, 19, -37, 80]], ![![527, -303, 24, -46, 100]], ![![298, -172, 14, -26, 57]]]
  g := ![![![0, -1, 2, 1, -2], ![-2, 7, -14, 4, 2], ![1, -1, 13, -19, 14], ![5, -32, 48, 23, -44], ![-4, 12, -34, 22, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N2 : Nat.card (O ⧸ I53N2) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N2)

lemma isPrimeI53N2 : Ideal.IsPrime I53N2 := prime_ideal_of_norm_prime hp53.out _ NI53N2
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![475, 368, -60, 2, -142]] ![![9, -5, 0, -1, 2]]
  ![![1107, -635, 48, -97, 208]] where
 M := ![![![1107, -635, 48, -97, 208]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI53N1 : IdealMulLeCertificate' Table 
  ![![1107, -635, 48, -97, 208]] ![![-1, -1, 2, 1, -2]]
  ![![53, 0, 0, 0, 0]] where
 M := ![![![53, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-165, 318, -32, 36, -116]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-165, 318, -32, 36, -116]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![47, 22, 27, 1, 0], ![45, 58, 29, 0, 1]] where
  M :=![![![-165, 318, -32, 36, -116], ![464, 107, -60, -20, -16], ![32, 198, 59, -32, -76], ![-80, 36, 0, 139, -164], ![-72, 64, -132, 34, 35]]]
  hmulB := by decide  
  f := ![![![52961, 13126, -72664, -16012, -51284]], ![![205136, 50841, -281452, -62020, -198640]], ![![397280, 98462, -545079, -120112, -384700]], ![![311789, 77274, -427783, -94265, -301916]], ![![447231, 110842, -613613, -135214, -433069]]]
  g := ![![![57, 106, 40, 36, -116], ![36, 25, 16, -20, -16], ![84, 90, 53, -32, -76], ![13, 110, 17, 139, -164], ![-55, -46, -35, 34, 35]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [47, 2, 36, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 18, 16], [23, 40, 43], [0, 1]]
 g := ![![[0, 11, 20], [49, 48, 21], [38, 27], [41, 39, 57], [1]], ![[56, 10, 50, 41], [46, 54, 58, 45], [34, 28], [14, 50, 2, 26], [52, 54, 3, 25]], ![[15, 7, 25, 11], [3, 45, 31, 24], [35, 26], [40, 21, 46, 40], [27, 58, 55, 34]]]
 h' := ![![[0, 18, 16], [57, 21, 16], [30, 31, 32], [20, 58, 26], [12, 57, 23], [0, 1]], ![[23, 40, 43], [21, 35, 32], [17, 49, 6], [50, 22, 21], [34, 13, 3], [0, 18, 16]], ![[0, 1], [8, 3, 11], [33, 38, 21], [47, 38, 12], [42, 48, 33], [23, 40, 43]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54, 31], []]
 b := ![[], [19, 55, 46], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [47, 2, 36, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-50129, -46229, 86605, -99, -37369]
  a := ![4, -1, -1, 3, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![27731, 35989, 19881, -99, -37369]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 205379 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-52961, -13126, 72664, 16012, 51284]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![-52961, -13126, 72664, 16012, 51284]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![58, 32, 1, 0, 0], ![32, 38, 0, 1, 0], ![43, 26, 0, 0, 1]] where
  M :=![![![-52961, -13126, 72664, 16012, 51284], ![-205136, -50841, 281452, 62020, 198640], ![-397280, -98462, 545079, 120112, 384700], ![-666832, -165268, 914912, 201607, 645716], ![-584376, -144832, 801780, 176678, 565871]]]
  hmulB := by decide  
  f := ![![![165, -318, 32, -36, 116]], ![![-464, -107, 60, 20, 16]], ![![-90, -374, 63, -24, 124]], ![![-208, -242, 56, -9, 76]], ![![-83, -280, 52, -18, 91]]]
  g := ![![![-118391, -72546, 72664, 16012, 51284], ![-458568, -280995, 281452, 62020, 198640], ![-888094, -544194, 545079, 120112, 384700], ![-1490660, -913426, 914912, 201607, 645716], ![-1306335, -800478, 801780, 176678, 565871]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P1 : CertificateIrreducibleZModOfList' 59 2 2 5 [48, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [52, 58], [0, 1]]
 g := ![![[53, 16], [24, 57], [51], [16, 1], [52, 1]], ![[0, 43], [38, 2], [51], [9, 58], [45, 58]]]
 h' := ![![[52, 58], [28, 4], [31, 23], [58, 46], [41, 1], [0, 1]], ![[0, 1], [0, 55], [47, 36], [31, 13], [34, 58], [52, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45]]
 b := ![[], [5, 52]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N1 : CertifiedPrimeIdeal' SI59N1 59 where
  n := 2
  hpos := by decide
  P := [48, 7, 1]
  hirr := P59P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-189182, -114759, 309694, -18192, 31840]
  a := ![7, -46, -24, 25, -119]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-320990, -172229, 309694, -18192, 31840]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N1 B_one_repr
lemma NI59N1 : Nat.card (O ⧸ I59N1) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-165, 318, -32, 36, -116]] ![![-52961, -13126, 72664, 16012, 51284]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0, 0, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0, 0, 0]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![0, 0, 0, 0, 61]] where
  M :=![![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![0, 0, 0, 0, 61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 5 2 5 [24, 1, 3, 26, 59, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [15, 19, 31, 60], [30, 19, 17, 40, 29], [12, 11, 5, 36, 29], [6, 11, 8, 47, 3], [0, 1]]
 g := ![![[7, 27, 17, 44, 58], [12, 52, 55, 42], [46, 7, 43, 25, 41], [39, 2, 1], []], ![[52, 58, 47, 11, 55, 11, 57], [7, 51, 19, 58], [59, 0, 35, 47, 39, 32, 14], [22, 51, 24, 41, 4, 0, 34], [7, 37, 5, 30, 60]], ![[29, 23, 13, 0, 16, 3, 14, 54], [8, 5, 27, 9], [46, 21, 11, 7, 31, 45, 26, 6], [49, 32, 39, 29, 3, 5, 55, 17], [8, 30, 30, 27, 23, 56, 4, 50]], ![[38, 15, 34, 42, 25, 21, 29, 8], [15, 32, 32, 52], [16, 20, 56, 29, 53, 50, 3, 6], [16, 58, 35, 45, 45, 35, 41, 24], [3, 43, 1, 54, 53, 8, 38, 50]], ![[56, 40, 17, 7, 24, 30, 53, 14], [4, 50, 6, 27], [38, 47, 30, 3, 41, 54, 13, 56], [44, 55, 25, 58, 59, 36, 47, 1], [44, 44, 34, 16, 16, 20, 42, 27]]]
 h' := ![![[15, 19, 31, 60], [53, 42, 23, 42, 34], [55, 44, 37, 3, 46], [40, 35, 40, 16, 23], [0, 0, 0, 1], [0, 1]], ![[30, 19, 17, 40, 29], [16, 21, 12, 11, 2], [1, 16, 20, 40, 27], [35, 36, 4, 45, 48], [35, 35, 26, 43, 24], [15, 19, 31, 60]], ![[12, 11, 5, 36, 29], [32, 10, 57, 45, 56], [38, 58, 28, 29, 58], [20, 8, 19, 14, 22], [29, 3, 24, 3, 58], [30, 19, 17, 40, 29]], ![[6, 11, 8, 47, 3], [31, 58, 54, 42, 25], [56, 44, 0, 51, 28], [39, 22, 14, 27, 39], [9, 57, 35, 2, 17], [12, 11, 5, 36, 29]], ![[0, 1], [23, 52, 37, 43, 5], [27, 21, 37, 60, 24], [59, 21, 45, 20, 51], [14, 27, 37, 12, 23], [6, 11, 8, 47, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58, 56], [], [], []]
 b := ![[], [13, 17, 35, 56], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 5
  hpos := by decide
  P := [24, 1, 3, 26, 59, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2236153738854, 1815485795664, -3786188207296, 145770315117, 945096451572]
  a := ![1, -12, -7, 9, -36]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![36658258014, 29762062224, -62068659136, 2389677297, 15493384452]
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



lemma PB1321I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB1321I1 : PrimesBelowBoundCertificateInterval O 23 61 1321 where
  m := 9
  g := ![3, 2, 1, 3, 2, 4, 3, 2, 1]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB1321I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0, I29N1, I29N2]
    · exact ![I31N0, I31N1]
    · exact ![I37N0]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1, I47N2, I47N3]
    · exact ![I53N0, I53N1, I53N2]
    · exact ![I59N0, I59N1]
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
    · exact ![24389, 29, 29]
    · exact ![29791, 961]
    · exact ![69343957]
    · exact ![1681, 1681, 41]
    · exact ![3418801, 43]
    · exact ![2209, 47, 47, 47]
    · exact ![148877, 53, 53]
    · exact ![205379, 3481]
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
      exact NI29N2
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
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
      exact NI53N2
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
  β := ![I29N1, I29N2, I31N1, I41N2, I43N1, I47N1, I47N2, I47N3, I53N1, I53N2]
  Il := ![[I29N1, I29N2], [I31N1], [], [I41N2], [I43N1], [I47N1, I47N2, I47N3], [I53N1, I53N2], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
