
import IdealArithmetic.Examples.NF5_1_1012500_1.RI5_1_1012500_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 10, -10, -10, -2]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![13, 10, -10, -10, -2]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![13, 7, 25, 1, 0], ![1, 18, 25, 0, 1]] where
  M :=![![![13, 10, -10, -10, -2], ![-12, 13, -4, -18, -10], ![-60, -12, -11, -30, -18], ![-24, -24, -24, -17, -6], ![-60, -48, -84, -72, -23]]]
  hmulB := by decide  
  f := ![![![41, -26, 18, 14, -10]], ![![-60, 41, -28, -18, 14]], ![![84, -60, 41, 18, -18]], ![![73, -51, 35, 17, -16]], ![![37, -28, 19, 4, -7]]]
  g := ![![![5, 4, 10, -10, -2], ![8, 11, 24, -18, -10], ![12, 18, 41, -30, -18], ![7, 7, 19, -17, -6], ![31, 30, 79, -72, -23]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 3 2 4 [10, 18, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 26, 4], [23, 2, 25], [0, 1]]
 g := ![![[23, 4, 22], [27, 5], [28, 22, 16], [1]], ![[25, 27, 3, 24], [10, 23], [20, 26, 20, 22], [11, 14, 6, 6]], ![[10, 24, 12, 7], [27, 4], [25, 26, 0, 22], [13, 17, 4, 23]]]
 h' := ![![[2, 26, 4], [4, 5, 15], [10, 14, 11], [19, 11, 25], [0, 1]], ![[23, 2, 25], [21, 24, 21], [18, 4, 20], [14, 3, 7], [2, 26, 4]], ![[0, 1], [15, 0, 22], [16, 11, 27], [2, 15, 26], [23, 2, 25]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 2], []]
 b := ![[], [9, 3, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 3
  hpos := by decide
  P := [10, 18, 4, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-70478, -45696, -68219, -76257, -40545]
  a := ![0, -1, -4, -1, -6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![33152, 41997, 98339, -76257, -40545]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 24389 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, -2, 2, 0, -1]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![-7, -2, 2, 0, -1]] 
 ![![29, 0, 0, 0, 0], ![16, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![14, 0, 0, 0, 1]] where
  M :=![![![-7, -2, 2, 0, -1], ![-6, -7, -2, 0, 0], ![0, -6, -9, -4, 0], ![0, 3, -3, -5, -2], ![-12, 3, -7, -14, -7]]]
  hmulB := by decide  
  f := ![![![-41, 37, -23, 10, 3]], ![![-22, 19, -12, 4, 2]], ![![-5, 7, -4, 6, -1]], ![![-7, 2, -2, -7, 3]], ![![-8, 13, -7, 14, -3]]]
  g := ![![![1, -2, 2, 0, -1], ![4, -7, -2, 0, 0], ![5, -6, -9, -4, 0], ![0, 3, -3, -5, -2], ![3, 3, -7, -14, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1

def I29N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, -2, 0, 0, -1]] i)))

def SI29N2: IdealEqSpanCertificate' Table ![![1, -2, 0, 0, -1]] 
 ![![29, 0, 0, 0, 0], ![22, 1, 0, 0, 0], ![9, 0, 1, 0, 0], ![27, 0, 0, 1, 0], ![13, 0, 0, 0, 1]] where
  M :=![![![1, -2, 0, 0, -1], ![-6, 1, -4, -4, 0], ![0, -6, -3, -4, -4], ![-12, 3, -7, -7, 0], ![-12, -9, -11, -14, -7]]]
  hmulB := by decide  
  f := ![![![-25, 13, 15, -6, -5]], ![![-20, 9, 12, -4, -4]], ![![-9, 3, 4, -2, -1]], ![![-21, 12, 14, -5, -5]], ![![-11, 8, 6, -4, -2]]]
  g := ![![![2, -2, 0, 0, -1], ![4, 1, -4, -4, 0], ![11, -6, -3, -4, -4], ![6, 3, -7, -7, 0], ![26, -9, -11, -14, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N2 : Nat.card (O ⧸ I29N2) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N2)

lemma isPrimeI29N2 : Ideal.IsPrime I29N2 := prime_ideal_of_norm_prime hp29.out _ NI29N2
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![13, 10, -10, -10, -2]] ![![-7, -2, 2, 0, -1]]
  ![![-127, -72, 140, 118, 21]] where
 M := ![![![-127, -72, 140, 118, 21]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI29N1 : IdealMulLeCertificate' Table 
  ![![-127, -72, 140, 118, 21]] ![![1, -2, 0, 0, -1]]
  ![![29, 0, 0, 0, 0]] where
 M := ![![![-1363, -493, -1189, -1392, -580]]]
 hmul := by decide  
 g := ![![![![-47, -17, -41, -48, -20]]]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -20, -8, 6, 5]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![-1, -20, -8, 6, 5]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![16, 9, 1, 0, 0], ![13, 25, 0, 1, 0], ![16, 30, 0, 0, 1]] where
  M :=![![![-1, -20, -8, 6, 5], ![30, -1, -18, -2, 6], ![36, 30, -7, -10, -2], ![-24, 3, 13, -1, -4], ![-48, -21, 21, 10, -5]]]
  hmulB := by decide  
  f := ![![![-25, 11, -13, -12, 3]], ![![18, -25, 4, -2, -12]], ![![-10, -1, -7, -8, -2]], ![![5, -17, -2, -7, -9]], ![![2, -19, -5, -10, -11]]]
  g := ![![![-1, -8, -8, 6, 5], ![8, 1, -18, -2, 6], ![10, 13, -7, -10, -2], ![-5, 1, 13, -1, -4], ![-14, -10, 21, 10, -5]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [25, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 30], [0, 1]]
 g := ![![[17, 5], [22, 1], [17, 5], [9, 1]], ![[0, 26], [0, 30], [0, 26], [18, 30]]]
 h' := ![![[9, 30], [8, 6], [9, 30], [23, 25], [0, 1]], ![[0, 1], [0, 25], [0, 1], [0, 6], [9, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [24, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [25, 22, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1502, -1717, 3488, -1467, 247]
  a := ![3, -64, 1, -1, 2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1361, -124, 3488, -1467, 247]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, 1, -1, -2, 0]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![-5, 1, -1, -2, 0]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![17, 7, 1, 0, 0], ![25, 27, 0, 1, 0], ![0, 18, 0, 0, 1]] where
  M :=![![![-5, 1, -1, -2, 0], ![0, -5, 0, 0, -2], ![-12, 0, -9, -8, 0], ![6, -6, 0, -1, -4], ![-18, 0, -14, -16, -5]]]
  hmulB := by decide  
  f := ![![![1, -7, 3, 6, -2]], ![![-12, 1, -8, -8, 6]], ![![-1, -4, 0, 2, 0]], ![![-11, -4, -5, -3, 4]], ![![-6, 0, -4, -4, 3]]]
  g := ![![![2, 2, -1, -2, 0], ![0, 1, 0, 0, -2], ![11, 9, -9, -8, 0], ![1, 3, 0, -1, -4], ![20, 20, -14, -16, -5]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P1 : CertificateIrreducibleZModOfList' 31 2 2 4 [7, 28, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 30], [0, 1]]
 g := ![![[4, 9], [12, 28], [21, 4], [3, 1]], ![[0, 22], [3, 3], [2, 27], [6, 30]]]
 h' := ![![[3, 30], [9, 28], [8, 11], [10, 2], [0, 1]], ![[0, 1], [0, 3], [10, 20], [16, 29], [3, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [8, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N1 : CertifiedPrimeIdeal' SI31N1 31 where
  n := 2
  hpos := by decide
  P := [7, 28, 1]
  hirr := P31P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![234, 48, 137, 189, 31]
  a := ![1, -3, -2, -1, -3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-220, -212, 137, 189, 31]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N1 B_one_repr
lemma NI31N1 : Nat.card (O ⧸ I31N1) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N1

def I31N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 0, 0, 2, -1]] i)))

def SI31N2: IdealEqSpanCertificate' Table ![![1, 0, 0, 2, -1]] 
 ![![31, 0, 0, 0, 0], ![15, 1, 0, 0, 0], ![23, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![1, 0, 0, 2, -1], ![-6, 1, -2, -6, 2], ![12, -6, 3, 10, -6], ![-24, 9, -9, -19, 8], ![24, -15, 7, 14, -11]]]
  hmulB := by decide  
  f := ![![![-47, -63, -3, 20, 9]], ![![-21, -32, -3, 10, 5]], ![![-31, -45, -4, 14, 7]], ![![-4, -3, 1, 1, 0]], ![![-9, -6, 2, 2, 0]]]
  g := ![![![0, 0, 0, 2, -1], ![1, 1, -2, -6, 2], ![1, -6, 3, 10, -6], ![2, 9, -9, -19, 8], ![3, -15, 7, 14, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N2 : Nat.card (O ⧸ I31N2) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N2)

lemma isPrimeI31N2 : Ideal.IsPrime I31N2 := prime_ideal_of_norm_prime hp31.out _ NI31N2
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![-1, -20, -8, 6, 5]] ![![-5, 1, -1, -2, 0]]
  ![![47, 63, 3, -20, -9]] where
 M := ![![![47, 63, 3, -20, -9]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI31N1 : IdealMulLeCertificate' Table 
  ![![47, 63, 3, -20, -9]] ![![1, 0, 0, 2, -1]]
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

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 13, 25, 30, 16]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![29, 13, 25, 30, 16]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![18, 17, 27, 25, 1]] where
  M :=![![![29, 13, 25, 30, 16], ![96, 29, 70, 84, 30], ![180, 96, 159, 176, 84], ![162, 42, 132, 151, 46], ![438, 204, 398, 448, 197]]]
  hmulB := by decide  
  f := ![![![5, -1, 3, 2, -2]], ![![-12, 5, -2, -4, 2]], ![![12, -12, 7, 8, -4]], ![![-18, 12, -10, -9, 6]], ![![-6, 1, -1, -1, 1]]]
  g := ![![![-7, -7, -11, -10, 16], ![-12, -13, -20, -18, 30], ![-36, -36, -57, -52, 84], ![-18, -20, -30, -27, 46], ![-84, -85, -133, -121, 197]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 4 2 5 [5, 9, 32, 5, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 26, 21, 35], [16, 20, 6, 21], [23, 27, 10, 18], [0, 1]]
 g := ![![[31, 35, 20, 33], [13, 35, 25], [19, 5, 10, 25], [1], []], ![[1, 36, 5, 1, 35, 8], [33, 8, 10], [33, 16, 9, 29, 26, 23], [29, 22, 26], [26, 7, 4]], ![[19, 31, 34, 14, 28, 7], [29, 21, 10], [30, 18, 14, 25, 31, 27], [10, 23, 28], [7, 8, 34]], ![[36, 28, 32, 15, 13, 6], [11, 18, 26], [36, 2, 11, 21, 29, 35], [21, 20, 7], [1, 35, 28]]]
 h' := ![![[30, 26, 21, 35], [6, 8, 0, 12], [16, 14, 16, 5], [32, 28, 5, 32], [0, 0, 1], [0, 1]], ![[16, 20, 6, 21], [21, 14, 1, 25], [36, 28, 6, 11], [15, 18, 6, 28], [30, 33, 22, 27], [30, 26, 21, 35]], ![[23, 27, 10, 18], [30, 36, 2, 32], [8, 2, 15, 11], [25, 16, 34, 12], [36, 19, 15, 19], [16, 20, 6, 21]], ![[0, 1], [15, 16, 34, 5], [25, 30, 0, 10], [5, 12, 29, 2], [6, 22, 36, 28], [23, 27, 10, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [1, 28, 33], []]
 b := ![[], [], [9, 17, 27, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 4
  hpos := by decide
  P := [5, 9, 32, 5, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![27528016, 11358863, 23738965, 26908819, 11125165]
  a := ![1, 19, 3, -1, 6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4668242, -4804566, -7476770, -6789738, 11125165]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1874161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, -1, 3, 2, -2]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![5, -1, 3, 2, -2]] 
 ![![37, 0, 0, 0, 0], ![12, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![11, 0, 0, 1, 0], ![27, 0, 0, 0, 1]] where
  M :=![![![5, -1, 3, 2, -2], ![-12, 5, -2, -4, 2], ![12, -12, 7, 8, -4], ![-18, 12, -10, -9, 6], ![18, -6, 4, 4, -3]]]
  hmulB := by decide  
  f := ![![![29, 13, 25, 30, 16]], ![![12, 5, 10, 12, 6]], ![![8, 4, 7, 8, 4]], ![![13, 5, 11, 13, 6]], ![![33, 15, 29, 34, 17]]]
  g := ![![![1, -1, 3, 2, -2], ![-2, 5, -2, -4, 2], ![4, -12, 7, 8, -4], ![-5, 12, -10, -9, 6], ![3, -6, 4, 4, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![29, 13, 25, 30, 16]] ![![5, -1, 3, 2, -2]]
  ![![37, 0, 0, 0, 0]] where
 M := ![![![37, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0, 0, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0, 0, 0]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![0, 0, 0, 0, 41]] where
  M :=![![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![0, 0, 0, 0, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 5 2 5 [5, 38, 18, 5, 11, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 21, 31, 10, 27], [1, 39, 40, 8, 12], [21, 18, 0, 4, 10], [11, 3, 11, 19, 33], [0, 1]]
 g := ![![[17, 16, 38, 38, 25], [1, 14, 15, 16], [20, 4, 9, 39], [1], []], ![[38, 38, 15, 29, 26, 2, 23, 28], [34, 9, 26, 31], [1, 24, 25, 9], [24, 1, 40, 39, 8, 5, 5, 6], [25, 38, 24, 32]], ![[2, 31, 30, 12, 28, 29, 10, 17], [17, 40, 17, 31], [2, 17, 3, 31], [30, 22, 21, 12, 38, 6, 21, 38], [13, 36, 2, 21]], ![[29, 2, 10, 20, 7, 38, 27, 23], [1, 16, 7, 40], [0, 9, 8, 21], [11, 22, 8, 19, 26, 27, 7, 40], [36, 35, 5, 18]], ![[7, 25, 10, 18, 38, 27, 29, 10], [9, 4, 20, 21], [39, 15, 0, 33], [35, 32, 26, 30, 19, 9, 22, 20], [10, 6, 17, 23]]]
 h' := ![![[38, 21, 31, 10, 27], [3, 32, 22, 19, 5], [7, 10, 1, 12, 37], [36, 3, 23, 36, 30], [0, 0, 1], [0, 1]], ![[1, 39, 40, 8, 12], [14, 12, 1, 5, 30], [26, 22, 36, 39, 21], [20, 25, 26, 34, 38], [7, 5, 4, 17, 8], [38, 21, 31, 10, 27]], ![[21, 18, 0, 4, 10], [20, 17, 35, 36, 30], [8, 36, 15, 30, 21], [10, 16, 31, 16, 21], [18, 19, 30, 28, 25], [1, 39, 40, 8, 12]], ![[11, 3, 11, 19, 33], [5, 10, 16, 9, 20], [16, 4, 4, 23, 32], [37, 40, 39, 39, 12], [15, 33, 2, 21, 39], [21, 18, 0, 4, 10]], ![[0, 1], [19, 11, 8, 13, 38], [33, 10, 26, 19, 12], [8, 39, 4, 39, 22], [30, 25, 4, 16, 10], [11, 3, 11, 19, 33]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19, 2, 2, 32], [], [], []]
 b := ![[], [4, 11, 25, 6, 14], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 5
  hpos := by decide
  P := [5, 38, 18, 5, 11, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-587702692, -295672935, -525514015, -604530650, -269000918]
  a := ![-1, 0, -2, 2, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-14334212, -7211535, -12817415, -14744650, -6560998]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 29, -17, -12, 2]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![41, 29, -17, -12, 2]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![42, 36, 13, 37, 1]] where
  M :=![![![41, 29, -17, -12, 2], ![12, 41, 16, -14, -12], ![-72, 12, 33, -2, -14], ![-6, -42, -8, 7, 6], ![30, -48, -46, 8, 13]]]
  hmulB := by decide  
  f := ![![![-1, 1, -1, 0, 0]], ![![0, -1, 0, -2, 0]], ![![0, 0, -1, 2, -2]], ![![-6, 0, -2, -7, 2]], ![![-6, 0, -3, -7, 1]]]
  g := ![![![-1, -1, -1, -2, 2], ![12, 11, 4, 10, -12], ![12, 12, 5, 12, -14], ![-6, -6, -2, -5, 6], ![-12, -12, -5, -11, 13]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 4 2 5 [8, 13, 42, 33, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 0, 4, 2], [0, 39, 18, 10], [3, 3, 21, 31], [0, 1]]
 g := ![![[26, 20, 19, 9], [37, 6, 42, 13], [21, 10, 10], [10, 1], []], ![[14, 39, 20, 10, 7, 26], [0, 42, 16, 19, 42, 18], [27, 17, 31], [0, 5, 37, 31, 19, 39], [21, 13, 4]], ![[5, 37, 31, 6, 23, 21], [28, 21, 0, 7, 22, 24], [19, 26, 21], [37, 17, 39, 24, 32, 17], [12, 27, 14]], ![[25, 2, 30, 32, 8, 10], [0, 3, 13, 28, 0, 31], [3, 39, 36], [18, 2, 27, 23, 39, 16], [26, 33, 15]]]
 h' := ![![[7, 0, 4, 2], [5, 39, 24, 3], [40, 12, 28, 23], [6, 34, 40, 15], [0, 0, 1], [0, 1]], ![[0, 39, 18, 10], [39, 2, 15, 20], [14, 32, 36, 40], [12, 27, 20, 26], [10, 10, 5, 27], [7, 0, 4, 2]], ![[3, 3, 21, 31], [34, 11, 20, 31], [2, 39, 10, 22], [5, 15, 10, 8], [33, 15, 38, 36], [0, 39, 18, 10]], ![[0, 1], [34, 34, 27, 32], [30, 3, 12, 1], [22, 10, 16, 37], [16, 18, 42, 23], [3, 3, 21, 31]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [27, 22, 7], []]
 b := ![[], [], [28, 9, 31, 38], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 4
  hpos := by decide
  P := [8, 13, 42, 33, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![14144120, 5881848, 12227338, 13810574, 5712076]
  a := ![0, 0, -6, -10, -4]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5250304, -4645416, -1442550, -4593866, 5712076]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 3418801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 1, -1, 0, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-1, 1, -1, 0, 0]] 
 ![![43, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![40, 0, 0, 1, 0], ![15, 0, 0, 0, 1]] where
  M :=![![![-1, 1, -1, 0, 0], ![0, -1, 0, -2, 0], ![0, 0, -1, 2, -2], ![-6, 0, -2, -7, 2], ![6, -6, 0, 4, -5]]]
  hmulB := by decide  
  f := ![![![41, 29, -17, -12, 2]], ![![6, 5, -2, -2, 0]], ![![5, 5, -2, -2, 0]], ![![38, 26, -16, -11, 2]], ![![15, 9, -7, -4, 1]]]
  g := ![![![0, 1, -1, 0, 0], ![2, -1, 0, -2, 0], ![-1, 0, -1, 2, -2], ![6, 0, -2, -7, 2], ![-1, -6, 0, 4, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![41, 29, -17, -12, 2]] ![![-1, 1, -1, 0, 0]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-55, -26, 24, 12, -5]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-55, -26, 24, 12, -5]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![1, 32, 22, 1, 0], ![4, 35, 1, 0, 1]] where
  M :=![![![-55, -26, 24, 12, -5], ![-30, -55, -12, 16, 12], ![72, -30, -43, 8, 16], ![12, 51, 1, -19, -4], ![-12, 63, 45, -14, -23]]]
  hmulB := by decide  
  f := ![![![-11, 7, -3, -6, 5]], ![![30, -11, 14, 20, -6]], ![![-36, 30, -9, -16, 20]], ![![5, 6, 6, 7, 5]], ![![20, -6, 10, 14, -3]]]
  g := ![![![-1, -5, -5, 12, -5], ![-2, -21, -8, 16, 12], ![0, -18, -5, 8, 16], ![1, 17, 9, -19, -4], ![2, 28, 8, -14, -23]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [44, 34, 35, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [26, 37, 44], [33, 9, 3], [0, 1]]
 g := ![![[40, 9, 14], [37, 19, 21], [25, 0, 14], [16, 12, 1], []], ![[18, 18, 29, 43], [17, 23, 25, 33], [41, 43, 4, 26], [8, 4, 41, 39], [27, 9]], ![[2, 23, 39, 24], [13, 42, 40, 18], [23, 14, 9, 28], [18, 19, 22, 18], [21, 9]]]
 h' := ![![[26, 37, 44], [17, 6, 22], [28, 44, 31], [1, 9, 22], [0, 0, 1], [0, 1]], ![[33, 9, 3], [1, 12, 39], [11, 46, 6], [16, 29, 30], [5, 46, 9], [26, 37, 44]], ![[0, 1], [38, 29, 33], [15, 4, 10], [27, 9, 42], [24, 1, 37], [33, 9, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45, 5], []]
 b := ![[], [45, 15, 33], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [44, 34, 35, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-24846, 1189, -18987, -25264, -5747]
  a := ![13, -1, -2, 1, -6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![498, 21506, 11544, -25264, -5747]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 103823 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, -7, 3, 6, -5]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![11, -7, 3, 6, -5]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![41, 4, 1, 0, 0], ![15, 34, 0, 1, 0], ![31, 7, 0, 0, 1]] where
  M :=![![![11, -7, 3, 6, -5], ![-30, 11, -14, -20, 6], ![36, -30, 9, 16, -20], ![-78, 33, -35, -47, 18], ![30, -45, -1, 2, -29]]]
  hmulB := by decide  
  f := ![![![55, 26, -24, -12, 5]], ![![30, 55, 12, -16, -12]], ![![49, 28, -19, -12, 3]], ![![39, 47, 1, -15, -7]], ![![41, 24, -15, -10, 2]]]
  g := ![![![-1, -4, 3, 6, -5], ![14, 15, -14, -20, 6], ![1, -10, 9, 16, -20], ![32, 35, -35, -47, 18], ![20, 2, -1, 2, -29]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P1 : CertificateIrreducibleZModOfList' 47 2 2 5 [20, 42, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 46], [0, 1]]
 g := ![![[35, 16], [10, 3], [24, 25], [19, 25], [1]], ![[21, 31], [25, 44], [8, 22], [3, 22], [1]]]
 h' := ![![[5, 46], [35, 43], [37, 12], [43, 42], [27, 5], [0, 1]], ![[0, 1], [15, 4], [3, 35], [18, 5], [5, 42], [5, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [17, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N1 : CertifiedPrimeIdeal' SI47N1 47 where
  n := 2
  hpos := by decide
  P := [20, 42, 1]
  hirr := P47P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-159, -45, 23, -137, 149]
  a := ![-1, -3, 1, -1, 2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-78, 74, 23, -137, 149]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N1 B_one_repr
lemma NI47N1 : Nat.card (O ⧸ I47N1) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-55, -26, 24, 12, -5]] ![![11, -7, 3, 6, -5]]
  ![![47, 0, 0, 0, 0]] where
 M := ![![![-47, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-95, 58, -48, -36, 27]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-95, 58, -48, -36, 27]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![22, 10, 10, 34, 1]] where
  M :=![![![-95, 58, -48, -36, 27], ![162, -95, 64, 48, -36], ![-216, 162, -103, -64, 48], ![252, -189, 129, 57, -56], ![-84, 63, -43, 34, 1]]]
  hmulB := by decide  
  f := ![![![-1, 1, -1, -2, -1]], ![![-6, -1, -2, -4, -2]], ![![-12, -6, -7, -8, -4]], ![![-6, -3, -7, -7, -2]], ![![-8, -3, -7, -8, -3]]]
  g := ![![![-13, -4, -6, -18, 27], ![18, 5, 8, 24, -36], ![-24, -6, -11, -32, 48], ![28, 7, 13, 37, -56], ![-2, 1, -1, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 4 2 5 [34, 51, 2, 37, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [29, 24, 24, 3], [14, 42, 3, 33], [26, 39, 26, 17], [0, 1]]
 g := ![![[35, 18, 44, 24], [27, 39, 42], [6, 20, 21, 36], [42, 16, 1], []], ![[39, 19, 44, 41, 1, 39], [32, 21, 28], [16, 32, 21, 34, 19, 8], [15, 38, 24], [16, 18, 21, 3, 20, 27]], ![[37, 46, 1, 1, 15, 3], [48, 13, 6], [45, 52, 46, 31, 34, 34], [33, 38, 17], [17, 24, 24, 49, 44, 3]], ![[49, 39, 12, 14, 15, 10], [15, 22, 44], [37, 51, 30, 26, 10, 43], [43, 51, 25], [34, 13, 33, 49, 26, 37]]]
 h' := ![![[29, 24, 24, 3], [47, 3, 10, 36], [8, 30, 52, 25], [3, 17, 20, 6], [0, 0, 0, 1], [0, 1]], ![[14, 42, 3, 33], [35, 49, 31, 38], [40, 20, 44, 9], [45, 38, 16, 12], [48, 29, 32, 36], [29, 24, 24, 3]], ![[26, 39, 26, 17], [49, 25, 24, 20], [41, 0, 45, 35], [40, 51, 2, 24], [46, 11, 2, 21], [14, 42, 3, 33]], ![[0, 1], [31, 29, 41, 12], [45, 3, 18, 37], [16, 0, 15, 11], [43, 13, 19, 48], [26, 39, 26, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [21, 18, 14], []]
 b := ![[], [], [21, 0, 33, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 4
  hpos := by decide
  P := [34, 51, 2, 37, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3531917, 2265549, -1143252, -1906362, 1484070]
  a := ![3, 0, 3, -4, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-682669, -237267, -301584, -988014, 1484070]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 7890481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, -1, 1, 2, 1]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![1, -1, 1, 2, 1]] 
 ![![53, 0, 0, 0, 0], ![19, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![51, 0, 0, 0, 1]] where
  M :=![![![1, -1, 1, 2, 1], ![6, 1, 2, 4, 2], ![12, 6, 7, 8, 4], ![6, 3, 7, 7, 2], ![18, 9, 21, 22, 9]]]
  hmulB := by decide  
  f := ![![![95, -58, 48, 36, -27]], ![![31, -19, 16, 12, -9]], ![![22, -14, 11, 8, -6]], ![![6, -3, 3, 3, -2]], ![![93, -57, 47, 34, -26]]]
  g := ![![![-1, -1, 1, 2, 1], ![-3, 1, 2, 4, 2], ![-8, 6, 7, 8, 4], ![-5, 3, 7, 7, 2], ![-18, 9, 21, 22, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-95, 58, -48, -36, 27]] ![![1, -1, 1, 2, 1]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-47, 7, 21, -2, -6]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-47, 7, 21, -2, -6]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![19, 49, 9, 1, 0], ![31, 12, 23, 0, 1]] where
  M :=![![![-47, 7, 21, -2, -6], ![-36, -47, 16, 20, -2], ![-12, -36, -35, 4, 20], ![66, 12, 2, 1, -8], ![18, 78, 0, -28, -7]]]
  hmulB := by decide  
  f := ![![![-1, -5, -3, -2, -4]], ![![-24, -1, -16, -20, -2]], ![![-12, -24, -21, -20, -20]], ![![-23, -6, -18, -21, -6]], ![![-11, -13, -14, -14, -11]]]
  g := ![![![3, 3, 3, -2, -6], ![-6, -17, -2, 20, -2], ![-12, -8, -9, 4, 20], ![5, 1, 3, 1, -8], ![13, 26, 7, -28, -7]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [37, 37, 7, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [32, 32, 40], [20, 26, 19], [0, 1]]
 g := ![![[39, 13, 3], [35, 27, 17], [56, 15], [29, 57, 49], [1]], ![[6, 12, 6, 18], [35, 38, 12, 44], [32, 12], [5, 10, 45, 47], [41, 19, 10, 44]], ![[47, 32, 36, 51], [54, 17, 2, 5], [5, 49], [40, 45, 37, 4], [21, 28, 28, 15]]]
 h' := ![![[32, 32, 40], [3, 23, 11], [55, 30, 28], [48, 16, 29], [22, 22, 52], [0, 1]], ![[20, 26, 19], [47, 22, 26], [42, 49, 40], [39, 51, 37], [40, 32, 49], [32, 32, 40]], ![[0, 1], [54, 14, 22], [43, 39, 50], [46, 51, 52], [25, 5, 17], [20, 26, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49, 1], []]
 b := ![[], [54, 30, 28], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [37, 37, 7, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5410, 11826, 9478, 9471, 9645]
  a := ![1, 1, 1, -1, 4]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-8026, -9627, -5044, 9471, 9645]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 205379 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-25, 14, -10, -12, 7]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![-25, 14, -10, -12, 7]] 
 ![![59, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![19, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![-25, 14, -10, -12, 7], ![42, -25, 18, 20, -12], ![-72, 42, -31, -32, 20], ![96, -57, 41, 41, -26], ![-60, 39, -27, -22, 15]]]
  hmulB := by decide  
  f := ![![![-53, -43, -15, -10, -7]], ![![-7, -6, -3, -2, -1]], ![![-10, -8, -5, -4, -2]], ![![-19, -14, -6, -5, -3]], ![![-10, -5, -5, -6, -3]]]
  g := ![![![3, 14, -10, -12, 7], ![-5, -25, 18, 20, -12], ![8, 42, -31, -32, 20], ![-10, -57, 41, 41, -26], ![5, 39, -27, -22, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 14, -12, -6, 2]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![31, 14, -12, -6, 2]] 
 ![![59, 0, 0, 0, 0], ![35, 1, 0, 0, 0], ![14, 0, 1, 0, 0], ![43, 0, 0, 1, 0], ![13, 0, 0, 0, 1]] where
  M :=![![![31, 14, -12, -6, 2], ![12, 31, 6, -10, -6], ![-36, 12, 25, -2, -10], ![-12, -24, -4, 7, 4], ![12, -36, -24, 8, 11]]]
  hmulB := by decide  
  f := ![![![-307, 206, -144, -90, 70]], ![![-175, 117, -82, -52, 40]], ![![-82, 56, -39, -22, 18]], ![![-215, 142, -100, -67, 50]], ![![-65, 46, -32, -14, 13]]]
  g := ![![![-1, 14, -12, -6, 2], ![-11, 31, 6, -10, -6], ![-10, 12, 25, -2, -10], ![9, -24, -4, 7, 4], ![19, -36, -24, 8, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-47, 7, 21, -2, -6]] ![![-25, 14, -10, -12, 7]]
  ![![125, -71, 25, 82, -31]] where
 M := ![![![125, -71, 25, 82, -31]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![125, -71, 25, 82, -31]] ![![31, 14, -12, -6, 2]]
  ![![59, 0, 0, 0, 0]] where
 M := ![![![767, -1003, -885, 236, 413]]]
 hmul := by decide  
 g := ![![![![13, -17, -15, 4, 7]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0, 0, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0, 0, 0]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![0, 0, 0, 0, 61]] where
  M :=![![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![0, 0, 0, 0, 61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 5 2 5 [49, 28, 53, 9, 46, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [48, 20, 47, 28, 41], [9, 4, 44, 7, 2], [50, 8, 54, 41, 19], [30, 28, 38, 46, 60], [0, 1]]
 g := ![![[4, 14, 7, 55, 58], [51, 4, 0, 13], [40, 60, 1, 33, 4], [33, 15, 1], []], ![[36, 15, 22, 59, 5, 51, 51, 25], [41, 41, 23, 42], [37, 42, 5, 49, 34, 27, 25, 1], [8, 27, 42, 44, 17, 0, 25, 22], [47, 16, 13, 60, 52, 53, 37, 52]], ![[13, 43, 2, 38, 45, 36, 6, 44], [14, 52, 0, 22], [7, 41, 46, 51, 46, 7, 41, 53], [58, 60, 9, 15, 27, 37], [48, 48, 41, 14, 51, 28, 21, 8]], ![[22, 57, 23, 17, 17, 51, 38, 4], [30, 28, 21, 46], [20, 5, 7, 13, 17, 17, 44, 9], [2, 43, 47, 16, 60, 27, 28, 27], [32, 51, 17, 15, 5, 53, 34, 27]], ![[17, 50, 18, 22, 26, 37, 49, 49], [2, 46, 60, 60], [32, 58, 53, 21, 7, 6, 60, 25], [9, 8, 22, 36, 43, 46, 18, 12], [12, 41, 19, 54, 48, 12, 1, 60]]]
 h' := ![![[48, 20, 47, 28, 41], [5, 14, 39, 23, 34], [53, 12, 6, 44, 47], [30, 49, 39, 39, 2], [0, 0, 0, 1], [0, 1]], ![[9, 4, 44, 7, 2], [19, 48, 57, 36, 21], [36, 3, 15, 6, 46], [49, 31, 39, 52, 53], [14, 49, 17, 55, 35], [48, 20, 47, 28, 41]], ![[50, 8, 54, 41, 19], [42, 5, 15, 27, 49], [22, 60, 17, 29, 49], [24, 41, 56, 7, 22], [24, 21, 42, 54], [9, 4, 44, 7, 2]], ![[30, 28, 38, 46, 60], [7, 44, 7, 48, 34], [47, 24, 60, 59, 30], [45, 13, 58, 51, 51], [29, 58, 52, 5, 19], [50, 8, 54, 41, 19]], ![[0, 1], [46, 11, 4, 49, 45], [12, 23, 24, 45, 11], [16, 49, 52, 34, 55], [60, 55, 11, 7, 7], [30, 28, 38, 46, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48, 6, 41, 7], [], [], []]
 b := ![[], [26, 42, 54, 4, 40], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 5
  hpos := by decide
  P := [49, 28, 53, 9, 46, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![18849, 4575, 9821, 14579, 7015]
  a := ![4, 0, 0, 1, 0]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![309, 75, 161, 239, 115]
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



lemma PB63I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 62 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 62 (by omega)

def PB63I1 : PrimesBelowBoundCertificateInterval O 23 62 63 where
  m := 9
  g := ![3, 3, 2, 1, 2, 2, 2, 3, 1]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB63I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0, I29N1, I29N2]
    · exact ![I31N0, I31N1, I31N2]
    · exact ![I37N0, I37N1]
    · exact ![I41N0]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1, I59N2]
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
    · exact ![961, 961, 31]
    · exact ![1874161, 37]
    · exact ![115856201]
    · exact ![3418801, 43]
    · exact ![103823, 2209]
    · exact ![7890481, 53]
    · exact ![205379, 59, 59]
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
      exact NI31N2
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
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
  β := ![I29N1, I29N2, I31N2, I37N1, I43N1, I53N1, I59N1, I59N2]
  Il := ![[I29N1, I29N2], [I31N2], [I37N1], [], [I43N1], [], [I53N1], [I59N1, I59N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
