
import IdealArithmetic.Examples.NF5_1_1000000_1.RI5_1_1000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![22, 5, 6, 5, 1]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![22, 5, 6, 5, 1]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![25, 12, 1, 0, 0], ![24, 28, 0, 1, 0], ![13, 25, 0, 0, 1]] where
  M :=![![![22, 5, 6, 5, 1], ![3, 34, 0, 17, 9], ![27, 29, 17, 17, 25], ![36, 26, 6, 17, 0], ![-6, 14, 10, 6, 25]]]
  hmulB := by decide  
  f := ![![![50, 25, 8, -41, -19]], ![![-57, -2, 66, -25, -63]], ![![13, 18, 35, -42, -42]], ![![-12, 18, 66, -55, -72]], ![![-23, 11, 60, -42, -63]]]
  g := ![![![-9, -8, 6, 5, 1], ![-18, -23, 0, 17, 9], ![-39, -44, 17, 17, 25], ![-18, -18, 6, 17, 0], ![-25, -31, 10, 6, 25]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [27, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 28], [0, 1]]
 g := ![![[], [6], [0, 4], [0, 1]], ![[], [6], [0, 25], [0, 28]]]
 h' := ![![[0, 28], [12], [0, 8], [0, 2], [0, 1]], ![[0, 1], [12], [0, 21], [0, 27], [0, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [0, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [27, 0, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![66, 288, 72, 329, 156]
  a := ![0, -7, 2, -8, -11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-402, -472, 72, 329, 156]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, -3, 2, -1, 1]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![2, -3, 2, -1, 1]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![24, 6, 1, 0, 0], ![15, 9, 0, 1, 0], ![27, 23, 0, 0, 1]] where
  M :=![![![2, -3, 2, -1, 1], ![3, 4, -2, 3, -3], ![-9, 1, 1, -1, 9], ![12, -2, 2, -1, -4], ![-18, 4, 0, 0, 9]]]
  hmulB := by decide  
  f := ![![![-2, 1, 4, 1, -3]], ![![-9, 0, 0, 9, 5]], ![![-3, 1, 3, 3, -1]], ![![-3, 1, 2, 3, 0]], ![![-9, 1, 4, 8, 1]]]
  g := ![![![-2, -1, 2, -1, 1], ![3, 2, -2, 3, -3], ![-9, -7, 1, -1, 9], ![3, 3, 2, -1, -4], ![-9, -7, 0, 0, 9]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P1 : CertificateIrreducibleZModOfList' 29 2 2 4 [1, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 28], [0, 1]]
 g := ![![[20, 1], [4], [16, 20], [9, 1]], ![[0, 28], [4], [22, 9], [18, 28]]]
 h' := ![![[9, 28], [20, 1], [13, 2], [20, 22], [0, 1]], ![[0, 1], [0, 28], [2, 27], [15, 7], [9, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [2, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N1 : CertifiedPrimeIdeal' SI29N1 29 where
  n := 2
  hpos := by decide
  P := [1, 20, 1]
  hirr := P29P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11962, 21360, 8003, 13001, 5834]
  a := ![3, -62, -1, -63, -58]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-18367, -9581, 8003, 13001, 5834]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N1 B_one_repr
lemma NI29N1 : Nat.card (O ⧸ I29N1) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N1

def I29N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4, 2, -1, 1, 1]] i)))

def SI29N2: IdealEqSpanCertificate' Table ![![-4, 2, -1, 1, 1]] 
 ![![29, 0, 0, 0, 0], ![11, 1, 0, 0, 0], ![24, 0, 1, 0, 0], ![22, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![-4, 2, -1, 1, 1], ![3, -3, 1, -1, 1], ![3, 4, -2, 1, -3], ![-6, 1, 1, -1, 2], ![6, 1, -1, 2, -5]]]
  hmulB := by decide  
  f := ![![![16, 30, 9, 13, 9]], ![![7, 13, 4, 6, 4]], ![![15, 28, 8, 13, 9]], ![![14, 25, 7, 11, 8]], ![![4, 7, 2, 3, 2]]]
  g := ![![![-1, 2, -1, 1, 1], ![1, -3, 1, -1, 1], ![0, 4, -2, 1, -3], ![-1, 1, 1, -1, 2], ![0, 1, -1, 2, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N2 : Nat.card (O ⧸ I29N2) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N2)

lemma isPrimeI29N2 : Ideal.IsPrime I29N2 := prime_ideal_of_norm_prime hp29.out _ NI29N2
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![22, 5, 6, 5, 1]] ![![2, -3, 2, -1, 1]]
  ![![47, -46, 50, -18, 50]] where
 M := ![![![47, -46, 50, -18, 50]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI29N1 : IdealMulLeCertificate' Table 
  ![![47, -46, 50, -18, 50]] ![![-4, 2, -1, 1, 1]]
  ![![29, 0, 0, 0, 0]] where
 M := ![![![232, 464, -261, 261, -435]]]
 hmul := by decide  
 g := ![![![![8, 16, -9, 9, -15]]]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10, 0, -15, 7, 15]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![10, 0, -15, 7, 15]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![2, 12, 1, 0, 0], ![19, 7, 0, 1, 0], ![0, 17, 0, 0, 1]] where
  M :=![![![10, 0, -15, 7, 15], ![45, 17, -7, -23, -1], ![-3, 14, 40, -37, -45], ![-90, -31, 29, 33, -14], ![0, -7, -23, 22, 25]]]
  hmulB := by decide  
  f := ![![![34, 76, 13, 41, 29]], ![![87, 117, 35, 67, 53]], ![![41, 58, 16, 33, 25]], ![![43, 78, 17, 43, 32]], ![![51, 68, 20, 39, 30]]]
  g := ![![![-3, -4, -15, 7, 15], ![16, 9, -7, -23, -1], ![20, 18, 40, -37, -45], ![-25, -12, 29, 33, -14], ![-12, -10, -23, 22, 25]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [5, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [14, 30], [0, 1]]
 g := ![![[22, 25], [17, 1], [22, 25], [14, 1]], ![[0, 6], [0, 30], [0, 6], [28, 30]]]
 h' := ![![[14, 30], [8, 26], [14, 30], [23, 5], [0, 1]], ![[0, 1], [0, 5], [0, 1], [0, 26], [14, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [11, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [5, 17, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![86, 86, 103, 41, -59]
  a := ![1, -6, 1, -7, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-29, -14, 103, 41, -59]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2, -5, 0, -3, -1]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![-2, -5, 0, -3, -1]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![17, 23, 1, 0, 0], ![6, 8, 0, 1, 0], ![15, 12, 0, 0, 1]] where
  M :=![![![-2, -5, 0, -3, -1], ![-3, -6, -2, -3, -5], ![-15, -13, -3, -7, -1], ![0, -10, -2, -5, -4], ![-12, -4, -2, -4, 1]]]
  hmulB := by decide  
  f := ![![![-2, -3, -2, 5, 1]], ![![3, 2, -8, 1, 9]], ![![2, 0, -7, 3, 7]], ![![0, 0, -2, 1, 2]], ![![0, -1, -4, 3, 4]]]
  g := ![![![1, 1, 0, -3, -1], ![4, 4, -2, -3, -5], ![3, 4, -3, -7, -1], ![4, 4, -2, -5, -4], ![1, 2, -2, -4, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P1 : CertificateIrreducibleZModOfList' 31 2 2 4 [11, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [20, 30], [0, 1]]
 g := ![![[1, 9], [6, 1], [5, 10], [20, 1]], ![[26, 22], [26, 30], [19, 21], [9, 30]]]
 h' := ![![[20, 30], [27, 3], [7, 30], [28, 17], [0, 1]], ![[0, 1], [25, 28], [18, 1], [27, 14], [20, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [22, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N1 : CertifiedPrimeIdeal' SI31N1 31 where
  n := 2
  hpos := by decide
  P := [11, 11, 1]
  hirr := P31P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1436, 4105, 826, 3471, 2043]
  a := ![1, 25, -3, 24, 33]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2067, -2167, 826, 3471, 2043]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N1 B_one_repr
lemma NI31N1 : Nat.card (O ⧸ I31N1) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N1

def I31N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, -3, -1, -2, 0]] i)))

def SI31N2: IdealEqSpanCertificate' Table ![![-5, -3, -1, -2, 0]] 
 ![![31, 0, 0, 0, 0], ![27, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![11, 0, 0, 0, 1]] where
  M :=![![![-5, -3, -1, -2, 0], ![0, -8, -1, -4, -4], ![-12, -9, -4, -6, -4], ![-6, -9, -1, -5, -2], ![-6, -3, -3, -2, -3]]]
  hmulB := by decide  
  f := ![![![25, 15, 1, -20, -8]], ![![21, 13, 2, -18, -8]], ![![9, 6, 1, -8, -4]], ![![1, 0, -2, 1, 2]], ![![11, 6, 0, -8, -3]]]
  g := ![![![3, -3, -1, -2, 0], ![9, -8, -1, -4, -4], ![11, -9, -4, -6, -4], ![9, -9, -1, -5, -2], ![5, -3, -3, -2, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N2 : Nat.card (O ⧸ I31N2) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N2)

lemma isPrimeI31N2 : Ideal.IsPrime I31N2 := prime_ideal_of_norm_prime hp31.out _ NI31N2
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![10, 0, -15, 7, 15]] ![![-2, -5, 0, -3, -1]]
  ![![25, 15, 1, -20, -8]] where
 M := ![![![25, 15, 1, -20, -8]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI31N1 : IdealMulLeCertificate' Table 
  ![![25, 15, 1, -20, -8]] ![![-5, -3, -1, -2, 0]]
  ![![31, 0, 0, 0, 0]] where
 M := ![![![31, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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


def P37P0 : CertificateIrreducibleZModOfList' 37 5 2 5 [24, 20, 29, 15, 21, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 21, 1, 18, 17], [29, 36, 20, 24, 30], [32, 29, 10, 34, 34], [6, 24, 6, 35, 30], [0, 1]]
 g := ![![[16, 18, 22, 32, 36], [4, 7, 26, 7], [13, 35, 19, 16, 1], [], []], ![[16, 9, 21, 9, 32, 1, 5, 22], [1, 7, 21, 9], [17, 29, 3, 30, 24, 4, 12, 13], [1, 1, 18, 27], [27, 27, 19, 30]], ![[18, 15, 31, 24, 16, 8, 18, 12], [8, 9, 23, 11], [31, 8, 20, 11, 26, 25, 1, 33], [2, 29, 30, 16], [5, 32, 4, 12]], ![[35, 4, 16, 20, 1, 25, 9, 3], [5, 30, 6, 11], [9, 28, 36, 0, 33, 14, 17, 21], [5, 13, 13, 11], [14, 1, 14, 9]], ![[25, 26, 22, 31, 4, 21, 20, 21], [10, 21, 7, 9], [0, 25, 6, 30, 3, 18, 25, 12], [21, 7, 22, 4], [15, 4, 35, 12]]]
 h' := ![![[23, 21, 1, 18, 17], [12, 24, 28, 33, 31], [21, 10, 21, 24, 9], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[29, 36, 20, 24, 30], [10, 34, 10, 7, 11], [21, 0, 33, 2, 34], [3, 30, 26, 28, 4], [29, 0, 3, 25, 8], [23, 21, 1, 18, 17]], ![[32, 29, 10, 34, 34], [33, 16, 8, 5, 17], [15, 18, 29, 17, 14], [17, 5, 28, 9, 29], [18, 36, 21, 18, 4], [29, 36, 20, 24, 30]], ![[6, 24, 6, 35, 30], [1, 6, 21, 5, 31], [11, 14, 19, 23, 14], [31, 18, 28, 9, 20], [22, 35, 16, 23, 23], [32, 29, 10, 34, 34]], ![[0, 1], [10, 31, 7, 24, 21], [19, 32, 9, 8, 3], [21, 21, 29, 28, 20], [9, 3, 33, 8, 2], [6, 24, 6, 35, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 25, 35, 20], [], [], []]
 b := ![[], [4, 11, 2, 7, 1], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 5
  hpos := by decide
  P := [24, 20, 29, 15, 21, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![26881610, -4090942, -13873742, -11755788, 8011092]
  a := ![-1, -7, 5, -5, -18]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![726530, -110566, -374966, -317724, 216516]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0, 0, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0, 0, 0]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![0, 0, 0, 0, 41]] where
  M :=![![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![0, 0, 0, 0, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 5 2 5 [18, 7, 10, 13, 22, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 38, 6, 3, 34], [12, 33, 35, 17, 17], [12, 14, 27, 39, 34], [32, 37, 14, 23, 38], [0, 1]]
 g := ![![[18, 16, 32, 1, 36], [18, 2, 17, 32], [4, 1, 10, 33], [1], []], ![[11, 14, 33, 40, 3, 14, 15, 26], [26, 20, 5, 4], [35, 18, 24, 25], [35, 1, 19, 10, 37, 39, 10, 15], [27, 25, 28, 8]], ![[19, 14, 18, 1, 25, 37, 6, 26], [1, 25, 30, 10], [29, 25, 27, 32], [39, 21, 11, 27, 10, 15, 11, 24], [30, 37, 1, 2]], ![[15, 0, 23, 0, 37, 19, 23, 14], [20, 33, 23, 31], [23, 13, 10, 1], [0, 12, 22, 37, 22, 35, 12, 26], [38, 31, 16, 8]], ![[36, 36, 32, 4, 32, 36, 18, 15], [1, 35, 10, 31], [6, 33, 17, 40], [19, 19, 25, 10, 17, 20, 30, 14], [8, 12, 33, 9]]]
 h' := ![![[4, 38, 6, 3, 34], [40, 14, 4, 8, 6], [6, 1, 18, 5, 27], [23, 34, 31, 28, 19], [0, 0, 1], [0, 1]], ![[12, 33, 35, 17, 17], [14, 18, 0, 7, 34], [21, 27, 7, 28, 39], [35, 5, 1, 0, 5], [22, 34, 10, 31, 19], [4, 38, 6, 3, 34]], ![[12, 14, 27, 39, 34], [3, 39, 23, 8, 37], [29, 34, 17, 36, 16], [10, 20, 12, 31, 27], [14, 39, 40, 29, 32], [12, 33, 35, 17, 17]], ![[32, 37, 14, 23, 38], [14, 13, 27, 4, 11], [28, 17, 17, 8, 21], [14, 3, 5, 25, 40], [34, 4, 0, 17, 34], [12, 14, 27, 39, 34]], ![[0, 1], [25, 39, 28, 14, 35], [17, 3, 23, 5, 20], [17, 20, 33, 39, 32], [19, 5, 31, 5, 38], [32, 37, 14, 23, 38]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 20, 21, 1], [], [], []]
 b := ![[], [32, 13, 16, 38, 6], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 5
  hpos := by decide
  P := [18, 7, 10, 13, 22, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-96492270, -12689500, 120448898, -89486354, -54420940]
  a := ![0, -4, -2, -14, 12]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2353470, -309500, 2937778, -2182594, -1327340]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -3, 1, -2, 2]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![-1, -3, 1, -2, 2]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![25, 16, 1, 0, 0], ![15, 14, 0, 1, 0], ![2, 26, 0, 0, 1]] where
  M :=![![![-1, -3, 1, -2, 2], ![6, 0, -1, 0, -6], ![-18, -1, 0, -2, 6], ![6, -7, 1, -1, -2], ![-18, 5, -3, 0, 7]]]
  hmulB := by decide  
  f := ![![![5, -1, -5, 0, 2]], ![![6, 2, -1, -10, -2]], ![![5, 0, -3, -4, 0]], ![![3, 0, -2, -3, 0]], ![![4, 1, -1, -6, -1]]]
  g := ![![![0, -1, 1, -2, 2], ![1, 4, -1, 0, -6], ![0, -3, 0, -2, 6], ![0, 1, 1, -1, -2], ![1, -3, -3, 0, 7]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [30, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 42], [0, 1]]
 g := ![![[35, 17], [37, 16], [16], [21, 23], [1]], ![[30, 26], [7, 27], [16], [37, 20], [1]]]
 h' := ![![[25, 42], [8, 24], [3, 4], [15, 4], [13, 25], [0, 1]], ![[0, 1], [6, 19], [17, 39], [29, 39], [36, 18], [25, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [29, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [30, 18, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![460, -32, 32, 157, -380]
  a := ![13, -7, 4, -6, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-45, 166, 32, 157, -380]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8, 3, 0, -5, -1]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![8, 3, 0, -5, -1]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![10, 4, 1, 0, 0], ![23, 19, 0, 1, 0], ![6, 31, 0, 0, 1]] where
  M :=![![![8, 3, 0, -5, -1], ![-3, 2, 8, -5, -9], ![-27, -9, 7, 11, -1], ![0, -6, -14, 15, 16], ![12, 6, -4, -6, 3]]]
  hmulB := by decide  
  f := ![![![20, 9, 2, 7, -3]], ![![-9, 26, 2, 11, 17]], ![![5, 5, 1, 3, 1]], ![![7, 17, 2, 9, 6]], ![![-3, 20, 2, 9, 12]]]
  g := ![![![3, 3, 0, -5, -1], ![2, 8, 8, -5, -9], ![-8, -5, 7, 11, -1], ![-7, -17, -14, 15, 16], ![4, 1, -4, -6, 3]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P1 : CertificateIrreducibleZModOfList' 43 2 2 5 [28, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 42], [0, 1]]
 g := ![![[36, 10], [36, 38], [35], [10, 17], [1]], ![[18, 33], [2, 5], [35], [31, 26], [1]]]
 h' := ![![[24, 42], [24, 28], [20, 34], [21, 32], [15, 24], [0, 1]], ![[0, 1], [8, 15], [19, 9], [15, 11], [32, 19], [24, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [26, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N1 : CertifiedPrimeIdeal' SI43N1 43 where
  n := 2
  hpos := by decide
  P := [28, 19, 1]
  hirr := P43P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7, 19, -40, -35, 73]
  a := ![-1, -1, -1, -2, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![18, -33, -40, -35, 73]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N1 B_one_repr
lemma NI43N1 : Nat.card (O ⧸ I43N1) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N1

def I43N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2, -2, -1, -1, -1]] i)))

def SI43N2: IdealEqSpanCertificate' Table ![![-2, -2, -1, -1, -1]] 
 ![![43, 0, 0, 0, 0], ![23, 1, 0, 0, 0], ![30, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![-2, -2, -1, -1, -1], ![-3, -5, -1, -3, -1], ![-3, -8, -2, -5, -5], ![-6, -5, -1, -3, -2], ![0, -5, -1, -2, -3]]]
  hmulB := by decide  
  f := ![![![-2, 6, 3, -11, 1]], ![![-1, 3, 2, -6, 0]], ![![-3, 4, 2, -7, 1]], ![![0, 1, 0, -2, 1]], ![![0, 1, 0, -1, 0]]]
  g := ![![![2, -2, -1, -1, -1], ![4, -5, -1, -3, -1], ![7, -8, -2, -5, -5], ![4, -5, -1, -3, -2], ![4, -5, -1, -2, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N2 : Nat.card (O ⧸ I43N2) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N2)

lemma isPrimeI43N2 : Ideal.IsPrime I43N2 := prime_ideal_of_norm_prime hp43.out _ NI43N2
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![-1, -3, 1, -2, 2]] ![![8, 3, 0, -5, -1]]
  ![![-2, 6, 3, -11, 1]] where
 M := ![![![-2, 6, 3, -11, 1]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![-2, 6, 3, -11, 1]] ![![-2, -2, -1, -1, -1]]
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


def P47P0 : CertificateIrreducibleZModOfList' 47 5 2 5 [25, 34, 40, 7, 9, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 7, 19, 36, 21], [14, 33, 13, 26, 13], [5, 16, 5, 5, 26], [0, 37, 10, 27, 34], [0, 1]]
 g := ![![[3, 27, 40, 25, 8], [44, 15, 39, 13, 8], [35, 43, 36, 8, 34], [1], []], ![[18, 1, 27, 10, 13, 40, 43, 28], [4, 25, 33, 40, 19, 36, 16, 21], [3, 33, 34, 15, 17, 37, 33, 8], [22, 30, 38, 23, 15, 43, 25, 36], [34, 17, 34, 18]], ![[40, 28, 1, 8, 34, 7, 20, 30], [14, 7, 21, 41, 6, 45], [3, 15, 29, 8, 16, 5, 5, 46], [17, 6, 39, 11, 31, 10, 20, 46], [35, 10, 1, 28]], ![[20, 6, 27, 0, 45, 33, 13, 40], [29, 9, 19, 4, 2, 31, 22, 5], [12, 23, 3, 27, 34, 32, 5, 46], [17, 1, 6, 12, 27, 37, 40, 10], [14, 29, 4, 18]], ![[0, 2, 28, 20, 35, 35, 5, 6], [45, 43, 46, 19, 39, 20, 35, 14], [45, 44, 36, 42, 20, 20, 29, 17], [34, 40, 33, 27, 39, 2, 15, 34], [41, 23, 33, 28]]]
 h' := ![![[19, 7, 19, 36, 21], [28, 4, 37, 32, 14], [18, 5, 6, 2, 33], [22, 13, 7, 40, 38], [0, 0, 1], [0, 1]], ![[14, 33, 13, 26, 13], [39, 7, 37, 5, 39], [15, 30, 0, 15, 46], [11, 25, 28, 13, 5], [28, 1, 4, 3, 18], [19, 7, 19, 36, 21]], ![[5, 16, 5, 5, 26], [33, 16, 44, 14, 20], [20, 43, 35, 41], [15, 30, 26, 21, 21], [26, 1, 17, 19, 26], [14, 33, 13, 26, 13]], ![[0, 37, 10, 27, 34], [37, 36, 35, 30, 43], [40, 33, 24, 7, 7], [31, 31, 2, 3, 3], [4, 40, 23, 11, 2], [5, 16, 5, 5, 26]], ![[0, 1], [3, 31, 35, 13, 25], [3, 30, 29, 29, 8], [43, 42, 31, 17, 27], [9, 5, 2, 14, 1], [0, 37, 10, 27, 34]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39, 29, 12, 5], [], [], []]
 b := ![[], [18, 15, 13, 14, 2], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 5
  hpos := by decide
  P := [25, 34, 40, 7, 9, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4456540, -961714, 2232359, -641879, 14003274]
  a := ![3, 3, 0, -1, 14]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![94820, -20462, 47497, -13657, 297942]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0, 0, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0, 0, 0]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![0, 0, 0, 0, 53]] where
  M :=![![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![0, 0, 0, 0, 53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 5 2 5 [9, 37, 25, 43, 46, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 40, 46, 44, 6], [47, 42, 50, 32, 8], [34, 16, 40, 29, 21], [13, 7, 23, 1, 18], [0, 1]]
 g := ![![[45, 37, 43, 21, 10], [40, 32, 6, 43], [51, 0, 32, 50, 36], [7, 1], []], ![[10, 26, 51, 48, 25, 17, 19, 29], [41, 41, 26, 7], [51, 25, 42, 1, 41, 0, 21, 46], [1, 5, 11, 9], [0, 46, 11, 52, 42, 17, 10, 4]], ![[32, 30, 17, 52, 47, 35, 19, 22], [33, 16, 9, 49], [22, 37, 10, 16, 39, 52, 38, 48], [49, 11, 6, 25], [5, 47, 50, 9, 15, 14, 29, 35]], ![[30, 41, 31, 46, 25, 11, 52, 8], [12, 27, 41, 42], [24, 3, 28, 5, 28, 25, 15, 22], [38, 6, 6, 40], [35, 32, 35, 3, 50, 49, 3, 39]], ![[16, 18, 4, 52, 50, 9, 16, 18], [28, 34, 33, 6], [6, 49, 20, 39, 38, 32, 37, 22], [35, 37, 23, 42], [21, 12, 23, 31, 21, 23, 32, 2]]]
 h' := ![![[19, 40, 46, 44, 6], [17, 44, 6, 45, 13], [18, 15, 34, 51, 34], [43, 50, 0, 45, 6], [0, 0, 0, 1], [0, 1]], ![[47, 42, 50, 32, 8], [40, 51, 9, 10, 7], [41, 1, 43, 32, 22], [51, 28, 22, 41, 34], [22, 29, 39, 9, 3], [19, 40, 46, 44, 6]], ![[34, 16, 40, 29, 21], [32, 3, 2, 1, 49], [8, 6, 12, 14, 7], [52, 44, 49, 19, 35], [4, 6, 7, 1, 48], [47, 42, 50, 32, 8]], ![[13, 7, 23, 1, 18], [38, 24, 2, 16, 38], [27, 22, 20, 49, 25], [19, 31, 45, 41, 46], [34, 4, 13, 44, 27], [34, 16, 40, 29, 21]], ![[0, 1], [22, 37, 34, 34, 52], [3, 9, 50, 13, 18], [39, 6, 43, 13, 38], [47, 14, 47, 51, 28], [13, 7, 23, 1, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33, 29, 4, 27], [], [], []]
 b := ![[], [43, 29, 47, 2, 22], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 5
  hpos := by decide
  P := [9, 37, 25, 43, 46, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6104116, 4317115, 5004472, 9170643, 2646979]
  a := ![1, 5, -3, 4, 11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-115172, 81455, 94424, 173031, 49943]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0, 0, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0, 0, 0]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![0, 0, 0, 0, 59]] where
  M :=![![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![0, 0, 0, 0, 59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 5 2 5 [19, 0, 58, 6, 49, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [45, 38, 50, 25, 43], [31, 5, 52, 8, 12], [1, 0, 6, 48, 57], [51, 15, 10, 37, 6], [0, 1]]
 g := ![![[38, 33, 49, 58, 28], [53, 38, 32, 5, 22], [19, 28, 49, 16], [35, 10, 1], []], ![[15, 12, 25, 45, 24, 10, 40, 43], [39, 46, 53, 36, 20, 51, 51, 37], [22, 41, 24, 29], [46, 21, 29, 43, 20, 29, 56, 30], [11, 14, 23, 53, 49, 46, 11, 34]], ![[5, 0, 26, 5, 50, 27, 24, 51], [2, 56, 49, 27, 16, 57, 43, 15], [11, 48, 14, 28], [27, 5, 30, 19, 13, 18, 21, 7], [18, 27, 1, 49, 55, 38, 27, 17]], ![[33, 3, 46, 41, 43, 32, 8, 16], [26, 3, 2, 32, 38, 34, 56, 25], [51, 22, 53, 21], [55, 54, 19, 35, 24, 1, 35, 19], [3, 33, 13, 37, 15, 47, 24, 51]], ![[26, 51, 14, 50, 53, 41, 58, 10], [51, 50, 42, 38, 26, 40, 14, 39], [5, 31, 13, 46], [19, 8, 48, 4, 22, 8, 15, 2], [14, 28, 37, 19, 16, 23, 20, 39]]]
 h' := ![![[45, 38, 50, 25, 43], [55, 37, 28, 39, 38], [13, 2, 43, 48, 50], [43, 46, 16, 36, 55], [0, 0, 0, 1], [0, 1]], ![[31, 5, 52, 8, 12], [38, 32, 13, 11, 58], [4, 30, 30, 46, 42], [3, 7, 20, 9, 18], [56, 12, 9, 9, 34], [45, 38, 50, 25, 43]], ![[1, 0, 6, 48, 57], [51, 33, 38, 17, 45], [43, 37, 15, 8, 4], [55, 51, 48, 26, 38], [8, 37, 20, 32, 25], [31, 5, 52, 8, 12]], ![[51, 15, 10, 37, 6], [41, 57, 19, 9, 46], [2, 58, 31, 48, 28], [26, 50, 56, 55, 27], [3, 22, 10, 46, 16], [1, 0, 6, 48, 57]], ![[0, 1], [37, 18, 20, 42, 49], [40, 50, 58, 27, 53], [28, 23, 37, 51, 39], [48, 47, 20, 30, 43], [51, 15, 10, 37, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37, 48, 41, 19], [], [], []]
 b := ![[], [8, 2, 11, 55, 27], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 5
  hpos := by decide
  P := [19, 0, 58, 6, 49, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-104489, 19942, -3658, -2596, 52628]
  a := ![4, 0, 0, 1, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1771, 338, -62, -44, 892]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4, 2, -3, 1, 5]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![-4, 2, -3, 1, 5]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![33, 57, 1, 0, 0], ![5, 9, 0, 1, 0], ![18, 45, 0, 0, 1]] where
  M :=![![![-4, 2, -3, 1, 5], ![15, -1, 1, -5, -3], ![-9, 8, 4, -3, -7], ![-18, -7, 5, 5, 2], ![0, 5, -7, 6, 1]]]
  hmulB := by decide  
  f := ![![![32, 54, 11, 29, 21]], ![![63, 93, 25, 51, 37]], ![![78, 119, 30, 65, 47]], ![![13, 20, 5, 11, 8]], ![![57, 86, 22, 47, 34]]]
  g := ![![![0, -1, -3, 1, 5], ![1, 2, 1, -5, -3], ![0, 2, 4, -3, -7], ![-4, -7, 5, 5, 2], ![3, 5, -7, 6, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [45, 42, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 60], [0, 1]]
 g := ![![[5, 19], [48], [50, 1], [20, 60], [19, 1]], ![[0, 42], [48], [8, 60], [1, 1], [38, 60]]]
 h' := ![![[19, 60], [24, 18], [7, 32], [15, 60], [60, 11], [0, 1]], ![[0, 1], [0, 43], [5, 29], [57, 1], [25, 50], [19, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [21, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [45, 42, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![112, 4764, 384, 3093, 534]
  a := ![7, -21, -1, -21, -44]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-617, -1131, 384, 3093, 534]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2, 4, -1, 3, -5]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![-2, 4, -1, 3, -5]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![27, 34, 1, 0, 0], ![29, 46, 0, 1, 0], ![49, 20, 0, 0, 1]] where
  M :=![![![-2, 4, -1, 3, -5], ![-15, -5, 1, 1, 11], ![33, -2, -6, 3, -9], ![-6, 13, -3, -5, 2], ![30, -11, 7, -2, -17]]]
  hmulB := by decide  
  f := ![![![106, 168, 41, 95, 67]], ![![201, 309, 73, 177, 123]], ![![165, 256, 61, 146, 102]], ![![206, 319, 76, 182, 127]], ![![154, 241, 58, 137, 96]]]
  g := ![![![3, 0, -1, 3, -5], ![-10, -5, 1, 1, 11], ![9, 4, -6, 3, -9], ![2, 5, -3, -5, 2], ![12, 3, 7, -2, -17]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P1 : CertificateIrreducibleZModOfList' 61 2 2 5 [52, 25, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [36, 60], [0, 1]]
 g := ![![[4, 27], [13], [36, 13], [54, 27], [36, 1]], ![[0, 34], [13], [16, 48], [50, 34], [11, 60]]]
 h' := ![![[36, 60], [51, 24], [19, 14], [59, 47], [19, 24], [0, 1]], ![[0, 1], [0, 37], [35, 47], [43, 14], [29, 37], [36, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37]]
 b := ![[], [33, 49]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N1 : CertifiedPrimeIdeal' SI61N1 61 where
  n := 2
  hpos := by decide
  P := [52, 25, 1]
  hirr := P61P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![33, 242, 63, 189, -121]
  a := ![1, -6, 1, -7, -13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-20, -134, 63, 189, -121]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N1 B_one_repr
lemma NI61N1 : Nat.card (O ⧸ I61N1) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2, -3, -6, 7, 7]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![-2, -3, -6, 7, 7]] 
 ![![61, 0, 0, 0, 0], ![31, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![57, 0, 0, 1, 0], ![56, 0, 0, 0, 1]] where
  M :=![![![-2, -3, -6, 7, 7], ![21, 6, -10, -5, 7], ![21, 13, 11, -25, -17], ![-36, -8, 24, 1, -20], ![-12, -8, -6, 14, 9]]]
  hmulB := by decide  
  f := ![![![-110, -35, 8, -31, 59]], ![![-53, -19, 4, -16, 28]], ![![-33, -8, 1, -8, 16]], ![![-102, -35, 8, -30, 55]], ![![-106, -30, 6, -28, 55]]]
  g := ![![![-10, -3, -6, 7, 7], ![-2, 6, -10, -5, 7], ![30, 13, 11, -25, -17], ![15, -8, 24, 1, -20], ![-16, -8, -6, 14, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![-4, 2, -3, 1, 5]] ![![-2, 4, -1, 3, -5]]
  ![![23, -62, 56, -34, -14]] where
 M := ![![![23, -62, 56, -34, -14]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![23, -62, 56, -34, -14]] ![![-2, -3, -6, 7, 7]]
  ![![61, 0, 0, 0, 0]] where
 M := ![![![1220, 671, 366, -1159, -671]]]
 hmul := by decide  
 g := ![![![![20, 11, 6, -19, -11]]]]
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


lemma PB63I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 62 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 62 (by omega)

def PB63I1 : PrimesBelowBoundCertificateInterval O 23 62 63 where
  m := 9
  g := ![3, 3, 1, 1, 3, 1, 1, 1, 3]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB63I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0, I29N1, I29N2]
    · exact ![I31N0, I31N1, I31N2]
    · exact ![I37N0]
    · exact ![I41N0]
    · exact ![I43N0, I43N1, I43N2]
    · exact ![I47N0]
    · exact ![I53N0]
    · exact ![I59N0]
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
    · exact ![841, 841, 29]
    · exact ![961, 961, 31]
    · exact ![69343957]
    · exact ![115856201]
    · exact ![1849, 1849, 43]
    · exact ![229345007]
    · exact ![418195493]
    · exact ![714924299]
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
      exact NI31N2
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
      exact NI61N2
  β := ![I29N2, I31N2, I43N2, I61N2]
  Il := ![[I29N2], [I31N2], [], [], [I43N2], [], [], [], [I61N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
