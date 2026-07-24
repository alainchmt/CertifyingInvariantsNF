
import IdealArithmetic.Examples.NF5_3_8100000_3.RI5_3_8100000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4, 65, -21, 31, -23]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![4, 65, -21, 31, -23]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![0, 0, 0, 29, 0], ![20, 6, 11, 10, 1]] where
  M :=![![![4, 65, -21, 31, -23], ![-69, -128, 65, -49, 85], ![255, 381, -128, 171, -183], ![-57, -49, 31, -14, 45], ![96, 110, -40, 48, -59]]]
  hmulB := by decide  
  f := ![![![2, 1, -1, -1, 3]], ![![9, 8, 1, -13, -5]], ![![-15, -3, 8, 3, -21]], ![![-15, -13, -1, 22, 7]], ![![-7, -3, 2, 5, -4]]]
  g := ![![![16, 7, 8, 9, -23], ![-61, -22, -30, -31, 85], ![135, 51, 65, 69, -183], ![-33, -11, -16, -16, 45], ![44, 16, 21, 22, -59]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 4 2 4 [3, 21, 2, 8, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 4, 7, 17], [19, 21, 24, 16], [0, 3, 27, 25], [0, 1]]
 g := ![![[9, 27, 4, 20], [2, 0, 5], [21, 4, 21, 1], []], ![[8, 6, 6, 21, 10, 12], [21, 3, 28], [26, 5, 23, 20, 24, 26], [4, 3, 24, 6, 28, 12]], ![[24, 28, 28, 21, 16, 9], [0, 5, 25], [18, 16, 11, 5, 21, 24], [27, 8, 16, 23, 19, 7]], ![[0, 6, 16, 18, 21, 13], [7, 1, 5], [21, 5, 21, 28, 8, 24], [17, 0, 18, 28, 10, 23]]]
 h' := ![![[2, 4, 7, 17], [19, 22, 20, 7], [24, 11, 14, 18], [0, 0, 0, 1], [0, 1]], ![[19, 21, 24, 16], [23, 1, 13, 12], [12, 20, 28, 17], [25, 13, 8, 15], [2, 4, 7, 17]], ![[0, 3, 27, 25], [4, 24, 17, 8], [2, 17, 6, 5], [21, 25, 22, 4], [19, 21, 24, 16]], ![[0, 1], [4, 11, 8, 2], [24, 10, 10, 18], [7, 20, 28, 9], [0, 3, 27, 25]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [4, 16, 2], []]
 b := ![[], [], [4, 27, 0, 18], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 4
  hpos := by decide
  P := [3, 21, 2, 8, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1392558, 4242821, 1851577, 4316407, 1882589]
  a := ![0, -2, -4, -10, -13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1250318, -243197, -650238, -500327, 1882589]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 707281 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2, -1, 1, 1, -3]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![-2, -1, 1, 1, -3]] 
 ![![29, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![16, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![-2, -1, 1, 1, -3], ![-9, -8, -1, 13, 5], ![15, 3, -8, -3, 21], ![15, 13, 1, -22, -7], ![-18, -8, 6, 10, -15]]]
  hmulB := by decide  
  f := ![![![-4, -65, 21, -31, 23]], ![![1, -18, 5, -9, 5]], ![![-11, -49, 16, -23, 19]], ![![1, -14, 4, -7, 4]], ![![-4, -15, 5, -7, 6]]]
  g := ![![![0, -1, 1, 1, -3], ![-1, -8, -1, 13, 5], ![1, 3, -8, -3, 21], ![2, 13, 1, -22, -7], ![-1, -8, 6, 10, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![4, 65, -21, 31, -23]] ![![-2, -1, 1, 1, -3]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-34, -16, 10, 33, -17]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![-34, -16, 10, 33, -17]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![2, 21, 14, 9, 1]] where
  M :=![![![-34, -16, 10, 33, -17], ![-51, -55, -16, 127, 83], ![249, 150, -55, -135, 171], ![111, 127, 33, -198, -115], ![-228, -131, 47, 214, -83]]]
  hmulB := by decide  
  f := ![![![56, 18, -10, 5, -21]], ![![-63, -37, 18, -13, 31]], ![![93, 84, -37, 33, -57]], ![![3, -13, 5, -6, 5]], ![![4, 11, -4, 5, -5]]]
  g := ![![![0, 11, 8, 6, -17], ![-7, -58, -38, -20, 83], ![-3, -111, -79, -54, 171], ![11, 82, 53, 27, -115], ![-2, 52, 39, 31, -83]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 4 2 4 [21, 12, 20, 29, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 9, 28, 2], [1, 30], [20, 22, 3, 29], [0, 1]]
 g := ![![[26, 15, 30, 16], [12, 19, 17, 10], [9, 15, 2, 1], []], ![[4, 8, 6, 7, 8, 19], [30, 30, 11, 17, 21, 8], [11, 23, 26, 21, 11, 10], [0, 24, 21, 24, 11, 8]], ![[25, 1, 16, 15], [27, 10, 16, 21], [27, 9, 5, 30], []], ![[21, 18, 17, 19, 10, 12], [24, 21, 20, 5, 30, 23], [9, 16, 7, 21, 30, 21], [26, 26, 22, 7, 20, 23]]]
 h' := ![![[12, 9, 28, 2], [27, 24, 8, 27], [28, 11, 1, 14], [0, 0, 0, 1], [0, 1]], ![[1, 30], [12, 28, 21, 26], [10, 24, 6, 2], [23, 5, 23, 25], [12, 9, 28, 2]], ![[20, 22, 3, 29], [24, 3, 27, 4], [23, 7, 12, 17], [1, 28, 3, 30], [1, 30]], ![[0, 1], [25, 7, 6, 5], [11, 20, 12, 29], [14, 29, 5, 6], [20, 22, 3, 29]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [6], []]
 b := ![[], [], [30, 19, 11, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 4
  hpos := by decide
  P := [21, 12, 20, 29, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![177215201469, 441792895502, 173046014394, 359984671762, 164702090324]
  a := ![3, -65, -62, -191, -186]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4909321909, -97321000042, -68799459682, -36204327134, 164702090324]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 923521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![56, 18, -10, 5, -21]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![56, 18, -10, 5, -21]] 
 ![![31, 0, 0, 0, 0], ![14, 1, 0, 0, 0], ![21, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![17, 0, 0, 0, 1]] where
  M :=![![![56, 18, -10, 5, -21], ![-63, -37, 18, -13, 31], ![93, 84, -37, 33, -57], ![3, -13, 5, -6, 5], ![6, 23, -9, 10, -11]]]
  hmulB := by decide  
  f := ![![![-34, -16, 10, 33, -17]], ![![-17, -9, 4, 19, -5]], ![![-15, -6, 5, 18, -6]], ![![-3, 1, 3, 0, -7]], ![![-26, -13, 7, 25, -12]]]
  g := ![![![11, 18, -10, 5, -21], ![-12, -37, 18, -13, 31], ![15, 84, -37, 33, -57], ![1, -13, 5, -6, 5], ![0, 23, -9, 10, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![-34, -16, 10, 33, -17]] ![![56, 18, -10, 5, -21]]
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

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4, -4, -10, -7, -13]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![4, -4, -10, -7, -13]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![12, 25, 1, 0, 0], ![24, 34, 0, 1, 0], ![6, 14, 0, 0, 1]] where
  M :=![![![4, -4, -10, -7, -13], ![-39, -65, -4, -41, -1], ![-3, -54, -65, -63, -81], ![-21, -41, -7, -28, -7], ![0, -11, -17, -14, -21]]]
  hmulB := by decide  
  f := ![![![34, 14, -2, -21, -7]], ![![-21, 7, 14, -19, -35]], ![![-6, 7, 9, -16, -26]], ![![3, 15, 11, -30, -35]], ![![0, 7, 5, -14, -15]]]
  g := ![![![10, 18, -10, -7, -13], ![27, 39, -4, -41, -1], ![75, 131, -65, -63, -81], ![21, 32, -7, -28, -7], ![18, 32, -17, -14, -21]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [31, 28, 1] where
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
 g := ![![[20, 30], [4], [24, 11], [7], [1]], ![[31, 7], [4], [12, 26], [7], [1]]]
 h' := ![![[9, 36], [3, 20], [33, 2], [4, 23], [6, 9], [0, 1]], ![[0, 1], [35, 17], [14, 35], [26, 14], [13, 28], [9, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [17, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [31, 28, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![177, 574, 256, 834, 270]
  a := ![1, -4, -4, -13, -13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-663, -1026, 256, 834, 270]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![352, 23, -29, -9, -95]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![352, 23, -29, -9, -95]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![25, 21, 1, 0, 0], ![5, 36, 0, 1, 0], ![10, 32, 0, 0, 1]] where
  M :=![![![352, 23, -29, -9, -95], ![-285, -20, 23, 7, 77], ![231, 15, -20, -9, -63], ![111, 7, -9, -4, -31], ![-102, -8, 8, 4, 27]]]
  hmulB := by decide  
  f := ![![![10, 11, -5, -1, -9]], ![![-27, -32, 11, -13, 7]], ![![-8, -10, 2, -7, -3]], ![![-25, -30, 10, -13, 6]], ![![-20, -24, 8, -12, 3]]]
  g := ![![![56, 108, -29, -9, -95], ![-45, -87, 23, 7, 77], ![38, 75, -20, -9, -63], ![18, 36, -9, -4, -31], ![-16, -32, 8, 4, 27]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P1 : CertificateIrreducibleZModOfList' 37 2 2 5 [10, 34, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 36], [0, 1]]
 g := ![![[33, 26], [7], [17, 16], [9], [1]], ![[0, 11], [7], [28, 21], [9], [1]]]
 h' := ![![[3, 36], [7, 10], [15, 28], [10, 4], [27, 3], [0, 1]], ![[0, 1], [0, 27], [25, 9], [22, 33], [36, 34], [3, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [19, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N1 : CertifiedPrimeIdeal' SI37N1 37 where
  n := 2
  hpos := by decide
  P := [10, 34, 1]
  hirr := P37P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3738, 19189, 11340, 34073, 22294]
  a := ![1, 18, 23, 62, 71]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-18191, -58351, 11340, 34073, 22294]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N1 B_one_repr
lemma NI37N1 : Nat.card (O ⧸ I37N1) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 7, -5, 0, -18]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![71, 7, -5, 0, -18]] 
 ![![37, 0, 0, 0, 0], ![28, 1, 0, 0, 0], ![30, 0, 1, 0, 0], ![31, 0, 0, 1, 0], ![13, 0, 0, 0, 1]] where
  M :=![![![71, 7, -5, 0, -18], ![-54, 2, 7, 6, 18], ![54, 21, 2, 12, -6], ![24, 6, 0, 3, -4], ![-18, 3, 3, 4, 7]]]
  hmulB := by decide  
  f := ![![![35, 29, -5, -30, -6]], ![![26, 22, -3, -24, -6]], ![![24, 21, -4, -18, -6]], ![![29, 23, -5, -23, -2]], ![![17, 14, -2, -16, -3]]]
  g := ![![![7, 7, -5, 0, -18], ![-20, 2, 7, 6, 18], ![-24, 21, 2, 12, -6], ![-5, 6, 0, 3, -4], ![-11, 3, 3, 4, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![4, -4, -10, -7, -13]] ![![352, 23, -29, -9, -95]]
  ![![787, 77, -49, 2, -192]] where
 M := ![![![787, 77, -49, 2, -192]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![787, 77, -49, 2, -192]] ![![71, 7, -5, 0, -18]]
  ![![37, 0, 0, 0, 0]] where
 M := ![![![52577, 4070, -4070, -888, -13838]]]
 hmul := by decide  
 g := ![![![![1421, 110, -110, -24, -374]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 2, -2, -2, 6]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![5, 2, -2, -2, 6]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![6, 24, 1, 0, 0], ![17, 8, 0, 1, 0], ![29, 11, 0, 0, 1]] where
  M :=![![![5, 2, -2, -2, 6], ![18, 17, 2, -26, -10], ![-30, -6, 17, 6, -42], ![-30, -26, -2, 45, 14], ![36, 16, -12, -20, 31]]]
  hmulB := by decide  
  f := ![![![-167, -18, 18, 2, 50]], ![![150, 37, -18, 10, -46]], ![![60, 18, -7, 6, -18]], ![![-41, 0, 4, 3, 12]], ![![-77, -3, 8, 4, 23]]]
  g := ![![![-3, 0, -2, -2, 6], ![18, 7, 2, -26, -10], ![24, 0, 17, 6, -42], ![-29, -12, -2, 45, 14], ![-11, 3, -12, -20, 31]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [25, 39, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 40], [0, 1]]
 g := ![![[36, 23], [40], [5], [31, 4], [1]], ![[0, 18], [40], [5], [39, 37], [1]]]
 h' := ![![[2, 40], [16, 33], [14, 32], [4, 13], [16, 2], [0, 1]], ![[0, 1], [0, 8], [37, 9], [30, 28], [20, 39], [2, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [35, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [25, 39, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11, 39, 37, 370, 552]
  a := ![-1, 2, -4, -5, -18]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-549, -241, 37, 370, 552]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 5, -3, -8, 6]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![11, 5, -3, -8, 6]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![25, 32, 1, 0, 0], ![17, 39, 0, 1, 0], ![37, 21, 0, 0, 1]] where
  M :=![![![11, 5, -3, -8, 6], ![18, 20, 5, -38, -22], ![-66, -33, 20, 36, -54], ![-36, -38, -8, 63, 32], ![66, 37, -15, -56, 31]]]
  hmulB := by decide  
  f := ![![![-29, -105, 41, -46, 50]], ![![150, 244, -105, 100, -142]], ![![89, 112, -51, 44, -72]], ![![133, 191, -84, 77, -116]], ![![47, 26, -15, 8, -25]]]
  g := ![![![0, 7, -3, -8, 6], ![33, 44, 5, -38, -22], ![20, -23, 20, 36, -54], ![-51, -71, -8, 63, 32], ![6, 50, -15, -56, 31]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P1 : CertificateIrreducibleZModOfList' 41 2 2 5 [8, 28, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 40], [0, 1]]
 g := ![![[24, 36], [18], [18], [21, 5], [1]], ![[0, 5], [18], [18], [4, 36], [1]]]
 h' := ![![[13, 40], [4, 6], [36, 31], [37, 10], [33, 13], [0, 1]], ![[0, 1], [0, 35], [29, 10], [3, 31], [38, 28], [13, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [39, 35]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N1 : CertifiedPrimeIdeal' SI41N1 41 where
  n := 2
  hpos := by decide
  P := [8, 28, 1]
  hirr := P41P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-232, -900, 600, -1700, 888]
  a := ![0, -10, 4, -14, 12]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-468, 672, 600, -1700, 888]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N1 B_one_repr
lemma NI41N1 : Nat.card (O ⧸ I41N1) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 2, 0, -1, 1]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![2, 2, 0, -1, 1]] 
 ![![41, 0, 0, 0, 0], ![26, 1, 0, 0, 0], ![21, 0, 1, 0, 0], ![19, 0, 0, 1, 0], ![10, 0, 0, 0, 1]] where
  M :=![![![2, 2, 0, -1, 1], ![3, 5, 2, -3, -3], ![-9, 0, 5, 15, -3], ![-3, -3, -1, 10, 7], ![12, 9, -1, -10, 3]]]
  hmulB := by decide  
  f := ![![![-152, 44, -8, 29, 19]], ![![-95, 25, -4, 17, 13]], ![![-75, 30, -7, 18, 6]], ![![-73, 19, -3, 13, 10]], ![![-34, 13, -3, 8, 3]]]
  g := ![![![-1, 2, 0, -1, 1], ![-2, 5, 2, -3, -3], ![-9, 0, 5, 15, -3], ![-4, -3, -1, 10, 7], ![-1, 9, -1, -10, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![5, 2, -2, -2, 6]] ![![11, 5, -3, -8, 6]]
  ![![691, 429, -119, -650, 216]] where
 M := ![![![691, 429, -119, -650, 216]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![691, 429, -119, -650, 216]] ![![2, 2, 0, -1, 1]]
  ![![41, 0, 0, 0, 0]] where
 M := ![![![8282, 7421, 697, -12423, -4141]]]
 hmul := by decide  
 g := ![![![![202, 181, 17, -303, -101]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, -2, -2, -10, -2]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![1, -2, -2, -10, -2]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![41, 21, 5, 1, 0], ![31, 25, 19, 0, 1]] where
  M :=![![![1, -2, -2, -10, -2], ![-6, -11, -2, -18, -18], ![-54, -66, -11, 6, -18], ![-6, -18, -10, 5, 14], ![24, 12, -4, -44, -9]]]
  hmulB := by decide  
  f := ![![![-41, -10, 6, -2, 14]], ![![42, 19, -10, 6, -18]], ![![-54, -42, 19, -18, 30]], ![![-25, -5, 3, -1, 8]], ![![-29, -15, 7, -6, 13]]]
  g := ![![![11, 6, 2, -10, -2], ![30, 19, 10, -18, -18], ![6, 6, 7, 6, -18], ![-15, -11, -7, 5, 14], ![49, 27, 9, -44, -9]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [20, 25, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 40, 16], [40, 2, 27], [0, 1]]
 g := ![![[30, 21, 10], [19, 26, 40], [31, 24], [19, 42, 1], []], ![[15, 30, 31, 31], [26, 2, 30, 23], [41, 4], [18, 32, 25, 21], [35, 41]], ![[12, 5, 17, 5], [18, 6, 26, 5], [14, 15], [1, 24, 32, 28], [24, 41]]]
 h' := ![![[2, 40, 16], [7, 9, 28], [31, 29, 13], [7, 18, 29], [0, 0, 1], [0, 1]], ![[40, 2, 27], [16, 36, 28], [28, 39, 17], [26, 22, 2], [35, 13, 2], [2, 40, 16]], ![[0, 1], [36, 41, 30], [13, 18, 13], [11, 3, 12], [2, 30, 40], [40, 2, 27]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17, 14], []]
 b := ![[], [24, 18, 26], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [20, 25, 1, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2978, -14789, -9521, -52001, -35986]
  a := ![13, 0, -4, -8, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![75595, 45974, 21726, -52001, -35986]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 79507 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-41, -10, 6, -2, 14]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-41, -10, 6, -2, 14]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![3, 13, 1, 0, 0], ![15, 23, 0, 1, 0], ![1, 40, 0, 0, 1]] where
  M :=![![![-41, -10, 6, -2, 14], ![42, 19, -10, 6, -18], ![-54, -42, 19, -18, 30], ![-6, 6, -2, 3, -2], ![0, -12, 4, -4, 5]]]
  hmulB := by decide  
  f := ![![![1, -2, -2, -10, -2]], ![![-6, -11, -2, -18, -18]], ![![-3, -5, -1, -6, -6]], ![![-3, -7, -2, -13, -10]], ![![-5, -10, -2, -18, -17]]]
  g := ![![![-1, -14, 6, -2, 14], ![0, 17, -10, 6, -18], ![3, -25, 19, -18, 30], ![-1, 1, -2, 3, -2], ![1, -4, 4, -4, 5]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P1 : CertificateIrreducibleZModOfList' 43 2 2 5 [40, 35, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 42], [0, 1]]
 g := ![![[17, 14], [2, 36], [36], [1, 21], [1]], ![[0, 29], [32, 7], [36], [40, 22], [1]]]
 h' := ![![[8, 42], [6, 10], [31, 37], [3, 37], [3, 8], [0, 1]], ![[0, 1], [0, 33], [26, 6], [41, 6], [24, 35], [8, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [25, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N1 : CertifiedPrimeIdeal' SI43N1 43 where
  n := 2
  hpos := by decide
  P := [40, 35, 1]
  hirr := P43P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![39, 37, 59, -75, -45]
  a := ![-1, -4, -1, -8, -3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![24, 65, 59, -75, -45]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N1 B_one_repr
lemma NI43N1 : Nat.card (O ⧸ I43N1) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![1, -2, -2, -10, -2]] ![![-41, -10, 6, -2, 14]]
  ![![43, 0, 0, 0, 0]] where
 M := ![![![43, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-35, -24, -14, -20, -12]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-35, -24, -14, -20, -12]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![32, 5, 27, 1, 0], ![24, 25, 11, 0, 1]] where
  M :=![![![-35, -24, -14, -20, -12], ![-36, -113, -24, -80, -28], ![-84, -192, -113, -168, -132], ![-48, -80, -20, -57, -20], ![-6, -44, -30, -40, -37]]]
  hmulB := by decide  
  f := ![![![11, 8, -2, -12, 4]], ![![12, 17, 8, -32, -28]], ![![-84, -48, 17, 72, -36]], ![![-40, -21, 9, 31, -20]], ![![-6, 3, 7, -8, -21]]]
  g := ![![![19, 8, 14, -20, -12], ![68, 21, 52, -80, -28], ![180, 84, 125, -168, -132], ![48, 15, 37, -57, -20], ![46, 23, 31, -40, -37]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [10, 43, 17, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 34, 46], [26, 12, 1], [0, 1]]
 g := ![![[9, 1, 18], [8, 31, 1], [33, 13, 7], [11, 30, 1], []], ![[28, 33, 37, 33], [34, 39, 5, 44], [17, 5, 20, 41], [42, 32, 4, 44], [9, 1]], ![[2, 14, 42, 16], [40, 38, 21, 27], [10, 11, 41, 2], [31, 22, 41, 28], [7, 1]]]
 h' := ![![[4, 34, 46], [14, 5, 26], [46, 23, 46], [31, 26, 17], [0, 0, 1], [0, 1]], ![[26, 12, 1], [37, 22, 25], [24, 14, 12], [5, 28, 37], [20, 16, 12], [4, 34, 46]], ![[0, 1], [14, 20, 43], [38, 10, 36], [11, 40, 40], [42, 31, 34], [26, 12, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42, 22], []]
 b := ![[], [1, 14, 22], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [10, 43, 17, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-38591, -37004, 55955, -9777, 82024]
  a := ![3, -4, 7, -1, 14]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-36049, -43377, -12390, -9777, 82024]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 103823 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 1, 1, 1, 1]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![2, 1, 1, 1, 1]] 
 ![![47, 0, 0, 0, 0], ![28, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![10, 0, 0, 1, 0], ![43, 0, 0, 0, 1]] where
  M :=![![![2, 1, 1, 1, 1], ![3, 8, 1, 5, 1], ![3, 9, 8, 9, 9], ![3, 5, 1, 4, 1], ![0, 2, 2, 2, 3]]]
  hmulB := by decide  
  f := ![![![28, -1, -5, 3, 5]], ![![17, 0, -3, 1, 3]], ![![9, 0, -1, 0, 0]], ![![5, -1, -1, 2, 1]], ![![26, -1, -5, 3, 6]]]
  g := ![![![-2, 1, 1, 1, 1], ![-7, 8, 1, 5, 1], ![-18, 9, 8, 9, 9], ![-5, 5, 1, 4, 1], ![-5, 2, 2, 2, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1

def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 5, 1, -8, -4]] i)))

def SI47N2: IdealEqSpanCertificate' Table ![![5, 5, 1, -8, -4]] 
 ![![47, 0, 0, 0, 0], ![45, 1, 0, 0, 0], ![43, 0, 1, 0, 0], ![31, 0, 0, 1, 0], ![39, 0, 0, 0, 1]] where
  M :=![![![5, 5, 1, -8, -4], ![-12, -4, 5, 6, -12], ![-36, -33, -4, 60, 24], ![18, 6, -8, -5, 22], ![24, 27, 7, -46, -27]]]
  hmulB := by decide  
  f := ![![![55, -187, 71, -86, 68]], ![![57, -169, 64, -78, 60]], ![![35, -194, 75, -88, 76]], ![![41, -119, 45, -55, 42]], ![![39, -162, 62, -74, 61]]]
  g := ![![![3, 5, 1, -8, -4], ![5, -4, 5, 6, -12], ![-25, -33, -4, 60, 24], ![-13, 6, -8, -5, 22], ![21, 27, 7, -46, -27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N2 : Nat.card (O ⧸ I47N2) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N2)

lemma isPrimeI47N2 : Ideal.IsPrime I47N2 := prime_ideal_of_norm_prime hp47.out _ NI47N2
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-35, -24, -14, -20, -12]] ![![2, 1, 1, 1, 1]]
  ![![-244, -477, -215, -385, -241]] where
 M := ![![![-244, -477, -215, -385, -241]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![-244, -477, -215, -385, -241]] ![![5, 5, 1, -8, -4]]
  ![![47, 0, 0, 0, 0]] where
 M := ![![![-470, -1034, -376, -799, -423]]]
 hmul := by decide  
 g := ![![![![-10, -22, -8, -17, -9]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-22, -19, -3, -13, -1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-22, -19, -3, -13, -1]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![45, 45, 36, 1, 0], ![20, 17, 12, 0, 1]] where
  M :=![![![-22, -19, -3, -13, -1], ![-3, -34, -19, -29, -25], ![-75, -135, -34, -93, -33], ![-15, -29, -13, -24, -13], ![-12, -32, -8, -26, -11]]]
  hmulB := by decide  
  f := ![![![-8, -3, 1, 3, 1]], ![![3, -2, -3, 7, 5]], ![![15, 9, -2, -21, 9]], ![![6, 2, -3, -6, 11]], ![![1, 0, -1, -1, 4]]]
  g := ![![![11, 11, 9, -13, -1], ![34, 32, 25, -29, -25], ![90, 87, 70, -93, -33], ![25, 24, 19, -24, -13], ![26, 25, 20, -26, -11]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [19, 3, 23, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [15, 19, 23], [15, 33, 30], [0, 1]]
 g := ![![[2, 41, 13], [9, 49], [42, 47, 11], [2, 52], [1]], ![[16, 20, 41, 50], [], [4, 41, 39, 14], [50, 29], [7, 32, 48, 30]], ![[3, 2, 51, 26], [37, 49], [11, 32, 8, 30], [40, 9], [9, 33, 8, 23]]]
 h' := ![![[15, 19, 23], [50, 24, 38], [50, 13, 7], [5, 21, 45], [34, 50, 30], [0, 1]], ![[15, 33, 30], [29, 27, 4], [20, 2], [32, 43, 7], [9, 6, 20], [15, 19, 23]], ![[0, 1], [48, 2, 11], [50, 38, 46], [28, 42, 1], [24, 50, 3], [15, 33, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22, 43], []]
 b := ![[], [4, 7, 35], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [19, 3, 23, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1126, 12266, 10281, 50594, 48527]
  a := ![1, 0, 3, 6, 13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-61248, -58291, -45159, 50594, 48527]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 148877 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -1, 1, -2, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-1, -1, 1, -2, 0]] 
 ![![53, 0, 0, 0, 0], ![17, 1, 0, 0, 0], ![29, 0, 1, 0, 0], ![33, 0, 0, 1, 0], ![21, 0, 0, 0, 1]] where
  M :=![![![-1, -1, 1, -2, 0], ![0, 2, -1, 4, -4], ![-12, -15, 2, 6, 12], ![6, 4, -2, -3, 2], ![0, 1, 3, -8, -5]]]
  hmulB := by decide  
  f := ![![![-329, -39, 21, -4, 80]], ![![-101, -13, 6, -2, 24]], ![![-185, -24, 11, -4, 44]], ![![-207, -25, 13, -3, 50]], ![![-129, -16, 8, -2, 31]]]
  g := ![![![1, -1, 1, -2, 0], ![-1, 2, -1, 4, -4], ![-5, -15, 2, 6, 12], ![1, 4, -2, -3, 2], ![5, 1, 3, -8, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1

def I53N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![26, 2, -2, -1, -7]] i)))

def SI53N2: IdealEqSpanCertificate' Table ![![26, 2, -2, -1, -7]] 
 ![![53, 0, 0, 0, 0], ![32, 1, 0, 0, 0], ![36, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![40, 0, 0, 0, 1]] where
  M :=![![![26, 2, -2, -1, -7], ![-21, -1, 2, 1, 5], ![15, 0, -1, 3, -3], ![9, 1, -1, 0, -1], ![-6, 1, 1, -2, 1]]]
  hmulB := by decide  
  f := ![![![-20, -24, 14, -3, 19]], ![![-11, -13, 8, -1, 11]], ![![-15, -18, 11, -3, 15]], ![![-1, -1, 1, 0, 1]], ![![-16, -19, 11, -2, 15]]]
  g := ![![![6, 2, -2, -1, -7], ![-5, -1, 2, 1, 5], ![3, 0, -1, 3, -3], ![1, 1, -1, 0, -1], ![-2, 1, 1, -2, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N2 : Nat.card (O ⧸ I53N2) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N2)

lemma isPrimeI53N2 : Ideal.IsPrime I53N2 := prime_ideal_of_norm_prime hp53.out _ NI53N2
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-22, -19, -3, -13, -1]] ![![-1, -1, 1, -2, 0]]
  ![![-20, -24, 14, -3, 19]] where
 M := ![![![-20, -24, 14, -3, 19]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI53N1 : IdealMulLeCertificate' Table 
  ![![-20, -24, 14, -3, 19]] ![![26, 2, -2, -1, -7]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0, 0, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0, 0, 0]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![0, 0, 0, 0, 59]] where
  M :=![![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![0, 0, 0, 0, 59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 5 2 5 [45, 11, 20, 25, 10, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [48, 18, 13, 48, 40], [23, 32, 42, 9, 41], [9, 45, 10, 7, 18], [28, 22, 53, 54, 19], [0, 1]]
 g := ![![[54, 11, 3, 50, 22], [27, 26, 52, 15, 17], [41, 6, 48, 3], [16, 49, 1], []], ![[16, 24, 9, 47, 16, 44, 10, 32], [55, 27, 36, 31, 33, 47, 42, 2], [40, 43, 36, 51], [43, 53, 46, 25, 50, 9, 53, 52], [20, 35, 27, 3, 25, 48, 37, 44]], ![[46, 45, 6, 24, 35, 45, 46, 16], [31, 4, 37, 52, 8, 55, 55, 16], [5, 7, 4, 51], [20, 28, 21, 22, 26, 37, 29, 4], [31, 2, 11, 51, 39, 31, 44, 9]], ![[17, 5, 22, 31, 52, 46, 31, 55], [56, 25, 41, 30, 58, 31, 23, 37], [25, 14, 19, 15], [27, 43, 58, 13, 48, 49, 47, 38], [13, 6, 45, 16, 50, 55, 50, 50]], ![[53, 13, 7, 19, 30, 26, 48, 21], [27, 40, 56, 9, 1, 41, 34, 17], [46, 44, 18, 7], [58, 19, 49, 51, 38, 4, 40, 57], [2, 39, 9, 52, 49, 52, 40, 15]]]
 h' := ![![[48, 18, 13, 48, 40], [24, 49, 46, 15, 9], [10, 19, 34, 42, 31], [47, 38, 40, 25, 11], [0, 0, 0, 1], [0, 1]], ![[23, 32, 42, 9, 41], [18, 52, 42, 37, 15], [57, 57, 54, 40, 11], [38, 32, 9, 21, 13], [11, 19, 51, 44, 14], [48, 18, 13, 48, 40]], ![[9, 45, 10, 7, 18], [55, 17, 30, 13, 24], [9, 11, 45, 5, 24], [23, 7, 50, 12, 46], [34, 26, 1, 18, 12], [23, 32, 42, 9, 41]], ![[28, 22, 53, 54, 19], [4, 37, 23, 38, 47], [13, 52, 0, 6, 54], [31, 24, 16, 8, 29], [26, 20, 2, 3, 44], [9, 45, 10, 7, 18]], ![[0, 1], [11, 22, 36, 15, 23], [15, 38, 44, 25, 57], [43, 17, 3, 52, 19], [32, 53, 5, 52, 48], [28, 22, 53, 54, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 58, 7, 57], [], [], []]
 b := ![[], [39, 27, 19, 10, 3], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 5
  hpos := by decide
  P := [45, 11, 20, 25, 10, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3481, 531, -531, 531, -1062]
  a := ![4, 1, -1, 1, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![59, 9, -9, 9, -18]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 60, -8, 32, -14]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![41, 60, -8, 32, -14]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![22, 58, 38, 1, 0], ![43, 15, 9, 0, 1]] where
  M :=![![![41, 60, -8, 32, -14], ![-42, -25, 60, 12, 78], ![234, 372, -25, 216, -54], ![-6, 12, 32, 23, 42], ![66, 102, -10, 54, -19]]]
  hmulB := by decide  
  f := ![![![41, 0, -4, 4, -10]], ![![-30, -1, 0, 0, 18]], ![![54, 24, -1, -36, -18]], ![![20, 14, -2, -21, 2]], ![![29, 3, -3, -2, -5]]]
  g := ![![![-1, -26, -18, 32, -14], ![-60, -31, -18, 12, 78], ![-36, -186, -127, 216, -54], ![-38, -32, -20, 23, 42], ![-5, -45, -31, 54, -19]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [9, 24, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [37, 13, 42], [20, 47, 19], [0, 1]]
 g := ![![[23, 2, 3], [57, 45], [31, 34, 41], [57, 6, 16], [1]], ![[35, 10, 38, 42], [33, 45], [6, 21, 2, 46], [27, 31, 3, 36], [4, 19, 35, 34]], ![[12, 28, 41, 14], [], [8, 6, 51, 41], [56, 58, 37, 36], [58, 56, 41, 27]]]
 h' := ![![[37, 13, 42], [41, 39, 8], [26, 2, 44], [36, 1, 38], [52, 37, 57], [0, 1]], ![[20, 47, 19], [21, 19, 1], [14, 26, 17], [32, 13, 59], [48, 54, 24], [37, 13, 42]], ![[0, 1], [15, 3, 52], [25, 33], [40, 47, 25], [36, 31, 41], [20, 47, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 53], []]
 b := ![[], [60, 38, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [9, 24, 4, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-305332, -1355798, -1151548, -1425313, -1441904]
  a := ![7, 2, -22, -17, -40]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1525466, 1687556, 1081762, -1425313, -1441904]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 226981 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-41, 0, 4, -4, 10]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![-41, 0, 4, -4, 10]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![33, 16, 1, 0, 0], ![34, 4, 0, 1, 0], ![39, 44, 0, 0, 1]] where
  M :=![![![-41, 0, 4, -4, 10], ![30, 1, 0, 0, -18], ![-54, -24, 1, 36, 18], ![-6, 0, -4, 1, 18], ![30, 18, 2, -30, -17]]]
  hmulB := by decide  
  f := ![![![-41, -60, 8, -32, 14]], ![![42, 25, -60, -12, -78]], ![![-15, -32, -11, -24, -12]], ![![-20, -32, 0, -19, 2]], ![![3, -22, -38, -30, -47]]]
  g := ![![![-7, -8, 4, -4, 10], ![12, 13, 0, 0, -18], ![-33, -16, 1, 36, 18], ![-10, -12, -4, 1, 18], ![27, 14, 2, -30, -17]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P1 : CertificateIrreducibleZModOfList' 61 2 2 5 [46, 44, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [17, 60], [0, 1]]
 g := ![![[54, 4], [27], [28, 39], [56, 1], [17, 1]], ![[0, 57], [27], [20, 22], [12, 60], [34, 60]]]
 h' := ![![[17, 60], [27, 2], [54, 37], [47, 51], [11, 60], [0, 1]], ![[0, 1], [0, 59], [12, 24], [60, 10], [55, 1], [17, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [60, 36]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N1 : CertifiedPrimeIdeal' SI61N1 61 where
  n := 2
  hpos := by decide
  P := [46, 44, 1]
  hirr := P61P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8, 30, -12, 2, -70]
  a := ![1, 2, -4, -1, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![50, 54, -12, 2, -70]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N1 B_one_repr
lemma NI61N1 : Nat.card (O ⧸ I61N1) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![41, 60, -8, 32, -14]] ![![-41, 0, 4, -4, 10]]
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


lemma PB140I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB140I1 : PrimesBelowBoundCertificateInterval O 23 61 140 where
  m := 9
  g := ![2, 2, 3, 3, 2, 3, 3, 1, 2]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB140I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0, I29N1]
    · exact ![I31N0, I31N1]
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1, I47N2]
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
    · exact ![707281, 29]
    · exact ![923521, 31]
    · exact ![1369, 1369, 37]
    · exact ![1681, 1681, 41]
    · exact ![79507, 1849]
    · exact ![103823, 47, 47]
    · exact ![148877, 53, 53]
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
  β := ![I29N1, I31N1, I37N2, I41N2, I47N1, I47N2, I53N1, I53N2]
  Il := ![[I29N1], [I31N1], [I37N2], [I41N2], [], [I47N1, I47N2], [I53N1, I53N2], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
