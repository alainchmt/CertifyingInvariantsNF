
import IdealArithmetic.Examples.NF5_1_2700000_1.RI5_1_2700000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![27, 65, 6, -12, -33]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![27, 65, 6, -12, -33]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![23, 23, 1, 0, 0], ![14, 11, 0, 1, 0], ![22, 7, 0, 0, 1]] where
  M :=![![![27, 65, 6, -12, -33], ![24, 54, 56, 30, 21], ![-60, -105, 209, 190, 255], ![-160, -325, 200, 239, 375], ![48, 95, -74, -82, -124]]]
  hmulB := by decide  
  f := ![![![-1, -5, 16, 28, 117]], ![![-56, -24, 6, -90, -249]], ![![-39, -18, 13, -44, -99]], ![![-30, -21, 20, -23, -24]], ![![-14, -7, 10, -4, 11]]]
  g := ![![![27, 10, 6, -12, -33], ![-74, -59, 56, 30, 21], ![-453, -303, 209, 190, 255], ![-564, -351, 200, 239, 375], ![194, 123, -74, -82, -124]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [18, 27, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 28], [0, 1]]
 g := ![![[16, 9], [28], [8, 22], [2, 1]], ![[5, 20], [28], [23, 7], [4, 28]]]
 h' := ![![[2, 28], [19, 3], [1, 17], [22, 15], [0, 1]], ![[0, 1], [25, 26], [6, 12], [23, 14], [2, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [23, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [18, 27, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3076, -5776, -324, 1358, -2226]
  a := ![15, 37, -35, -39, -90]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1184, 80, -324, 1358, -2226]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-57, 4, -6, -8, -24]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![-57, 4, -6, -8, -24]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![19, 25, 1, 0, 0], ![14, 18, 0, 1, 0], ![28, 19, 0, 0, 1]] where
  M :=![![![-57, 4, -6, -8, -24], ![16, -41, -10, 4, 24], ![-8, 20, -59, -52, -72], ![56, 80, -58, -65, -96], ![-8, -26, 22, 24, 37]]]
  hmulB := by decide  
  f := ![![![-21, 4, -14, -48, -168]], ![![96, 51, -34, 116, 264]], ![![61, 39, -31, 64, 120]], ![![58, 46, -42, 47, 48]], ![![44, 35, -32, 36, 37]]]
  g := ![![![29, 26, -6, -8, -24], ![-18, -11, -10, 4, 24], ![133, 131, -59, -52, -72], ![164, 156, -58, -65, -96], ![-62, -59, 22, 24, 37]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P1 : CertificateIrreducibleZModOfList' 29 2 2 4 [10, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [28, 28], [0, 1]]
 g := ![![[3, 20], [22], [0, 23], [28, 1]], ![[12, 9], [22], [6, 6], [27, 28]]]
 h' := ![![[28, 28], [12, 7], [0, 15], [10, 20], [0, 1]], ![[0, 1], [5, 22], [14, 14], [19, 9], [28, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [3, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N1 : CertifiedPrimeIdeal' SI29N1 29 where
  n := 2
  hpos := by decide
  P := [10, 1, 1]
  hirr := P29P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-662842, -1236334, 189275, 417588, 121179]
  a := ![188, 438, -436, -500, -1125]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-465459, -544386, 189275, 417588, 121179]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N1 B_one_repr
lemma NI29N1 : Nat.card (O ⧸ I29N1) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N1

def I29N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17, 2, -1, -2, -7]] i)))

def SI29N2: IdealEqSpanCertificate' Table ![![-17, 2, -1, -2, -7]] 
 ![![29, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![16, 0, 1, 0, 0], ![28, 0, 0, 1, 0], ![24, 0, 0, 0, 1]] where
  M :=![![![-17, 2, -1, -2, -7], ![4, -14, 0, 4, 11], ![-8, -5, -9, -6, -7], ![10, 10, -11, -11, -15], ![0, -3, 4, 4, 6]]]
  hmulB := by decide  
  f := ![![![19, 22, -23, 8, -25]], ![![6, 6, -6, 4, -1]], ![![8, 13, -15, -2, -37]], ![![26, 24, -23, 19, 7]], ![![12, 15, -16, 4, -22]]]
  g := ![![![7, 2, -1, -2, -7], ![-8, -14, 0, 4, 11], ![18, -5, -9, -6, -7], ![26, 10, -11, -11, -15], ![-10, -3, 4, 4, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N2 : Nat.card (O ⧸ I29N2) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N2)

lemma isPrimeI29N2 : Ideal.IsPrime I29N2 := prime_ideal_of_norm_prime hp29.out _ NI29N2
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![27, 65, 6, -12, -33]] ![![-57, 4, -6, -8, -24]]
  ![![-955, -2539, -1196, -280, 411]] where
 M := ![![![-955, -2539, -1196, -280, 411]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI29N1 : IdealMulLeCertificate' Table 
  ![![-955, -2539, -1196, -280, 411]] ![![-17, 2, -1, -2, -7]]
  ![![29, 0, 0, 0, 0]] where
 M := ![![![12847, 35583, 16443, 3654, -6206]]]
 hmul := by decide  
 g := ![![![![443, 1227, 567, 126, -214]]]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![39, -29, 6, 14, 37]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![39, -29, 6, 14, 37]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![29, 16, 1, 1, 0], ![6, 25, 9, 0, 1]] where
  M :=![![![39, -29, 6, 14, 37], ![-28, 6, -4, -6, -17], ![12, -15, -5, 2, 13], ![-8, 15, -10, -15, -27], ![-4, 1, 2, 2, 0]]]
  hmulB := by decide  
  f := ![![![1, -1, 0, 2, 5]], ![![-4, -4, 2, -2, -1]], ![![4, 5, -9, -2, -19]], ![![-1, -3, 1, 1, 5]], ![![-2, -2, -1, -2, -6]]]
  g := ![![![-19, -38, -11, 14, 37], ![8, 17, 5, -6, -17], ![-4, -12, -4, 2, 13], ![19, 30, 8, -15, -27], ![-2, -1, 0, 2, 0]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 3 2 4 [17, 26, 15, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [20, 11, 5], [27, 19, 26], [0, 1]]
 g := ![![[28, 22, 9], [3, 16, 7], [6, 9, 8], [1]], ![[30, 21, 8, 28], [17, 0, 30, 16], [25, 1, 9, 7], [16, 5, 4, 1]], ![[0, 20, 23, 27], [5, 0, 11, 27], [15, 9, 8, 13], [30, 22, 14, 30]]]
 h' := ![![[20, 11, 5], [11, 10, 28], [22, 11, 21], [14, 5, 16], [0, 1]], ![[27, 19, 26], [4, 10, 24], [17, 15, 20], [9, 20, 19], [20, 11, 5]], ![[0, 1], [0, 11, 10], [23, 5, 21], [15, 6, 27], [27, 19, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13, 13], []]
 b := ![[], [20, 7, 16], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 3
  hpos := by decide
  P := [17, 26, 15, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-89259, -75241, 115084, 136430, -493057]
  a := ![15, 36, -34, -39, -89]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-35077, 324784, 142457, 136430, -493057]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 29791 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, -1, 0, 2, 5]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![1, -1, 0, 2, 5]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![26, 30, 1, 0, 0], ![0, 13, 0, 1, 0], ![25, 7, 0, 0, 1]] where
  M :=![![![1, -1, 0, 2, 5], ![-4, -4, 2, -2, -1], ![4, 5, -9, -2, -19], ![0, -5, 8, 7, 45], ![-4, -1, 0, -6, -20]]]
  hmulB := by decide  
  f := ![![![39, -29, 6, 14, 37]], ![![-28, 6, -4, -6, -17]], ![![6, -19, 1, 6, 15]], ![![-12, 3, -2, -3, -8]], ![![25, -22, 4, 10, 26]]]
  g := ![![![-4, -2, 0, 2, 5], ![-1, -1, 2, -2, -1], ![23, 14, -9, -2, -19], ![-43, -21, 8, 7, 45], ![16, 7, 0, -6, -20]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P1 : CertificateIrreducibleZModOfList' 31 2 2 4 [15, 30, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 30], [0, 1]]
 g := ![![[2, 20], [14, 19], [27, 10], [1, 1]], ![[22, 11], [2, 12], [6, 21], [2, 30]]]
 h' := ![![[1, 30], [7, 12], [29, 9], [16, 17], [0, 1]], ![[0, 1], [19, 19], [7, 22], [2, 14], [1, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [21, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N1 : CertifiedPrimeIdeal' SI31N1 31 where
  n := 2
  hpos := by decide
  P := [15, 30, 1]
  hirr := P31P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-86250, -163746, 25887, 60454, 22516]
  a := ![-69, -163, 161, 182, 415]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-42652, -60770, 25887, 60454, 22516]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N1 B_one_repr
lemma NI31N1 : Nat.card (O ⧸ I31N1) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![39, -29, 6, 14, 37]] ![![1, -1, 0, 2, 5]]
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

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![369, -210, 46, 108, 294]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![369, -210, 46, 108, 294]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![17, 25, 22, 1, 0], ![12, 12, 18, 0, 1]] where
  M :=![![![369, -210, 46, 108, 294], ![-216, 123, -26, -64, -174], ![128, -70, 15, 40, 102], ![-104, 50, -6, -27, -66], ![-32, 20, -6, -12, -35]]]
  hmulB := by decide  
  f := ![![![5, 10, -2, -4, -6]], ![![8, 19, -2, -8, -18]], ![![16, 30, 3, 0, -6]], ![![17, 35, 0, -7, -18]], ![![12, 24, 0, -4, -11]]]
  g := ![![![-135, -174, -206, 108, 294], ![80, 103, 122, -64, -174], ![-48, -62, -73, 40, 102], ![31, 41, 48, -27, -66], ![16, 20, 24, -12, -35]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [32, 29, 34, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [36, 11, 30], [4, 25, 7], [0, 1]]
 g := ![![[22, 2, 10], [22, 4], [9, 3, 30], [3, 1], []], ![[31, 31, 18, 9], [17, 11], [12, 1], [13, 33], [30, 12]], ![[14, 14, 19, 12], [21, 34], [11, 9, 17, 25], [19, 10], [16, 12]]]
 h' := ![![[36, 11, 30], [26, 8, 26], [8, 16, 35], [15, 29, 17], [0, 0, 1], [0, 1]], ![[4, 25, 7], [22, 27, 2], [23, 27, 23], [0, 13], [3, 19, 25], [36, 11, 30]], ![[0, 1], [1, 2, 9], [28, 31, 16], [24, 32, 20], [22, 18, 11], [4, 25, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 27], []]
 b := ![[], [33, 20, 25], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [32, 29, 34, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![15582, -30450, -122100, 151274, -563976]
  a := ![14, 35, -31, -34, -85]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![113828, 79876, 181120, 151274, -563976]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 50653 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-49, 28, -6, -14, -38]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-49, 28, -6, -14, -38]] 
 ![![37, 0, 0, 0, 0], ![15, 1, 0, 0, 0], ![34, 0, 1, 0, 0], ![24, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![-49, 28, -6, -14, -38], ![28, -17, 4, 8, 22], ![-16, 10, -3, -4, -14], ![12, -10, 4, 5, 18], ![4, -2, 0, 0, -1]]]
  hmulB := by decide  
  f := ![![![27, 56, -30, -38, -58]], ![![13, 27, -14, -18, -28]], ![![30, 62, -31, -40, -62]], ![![20, 42, -20, -27, -42]], ![![1, 2, -2, -2, -3]]]
  g := ![![![5, 28, -6, -14, -38], ![-3, -17, 4, 8, 22], ![2, 10, -3, -4, -14], ![-4, -10, 4, 5, 18], ![1, -2, 0, 0, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, -4, 19, 16, 21]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![1, -4, 19, 16, 21]] 
 ![![37, 0, 0, 0, 0], ![16, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![30, 0, 0, 1, 0], ![11, 0, 0, 0, 1]] where
  M :=![![![1, -4, 19, 16, 21], ![-32, -58, 58, 60, 87], ![-120, -245, 153, 182, 285], ![-122, -250, 99, 141, 237], ![44, 91, -42, -56, -92]]]
  hmulB := by decide  
  f := ![![![109, 92, -95, 58, -33]], ![![44, 34, -34, 28, 9]], ![![3, 13, -18, -16, -84]], ![![112, 80, -75, 87, 93]], ![![19, 17, -19, 6, -23]]]
  g := ![![![-19, -4, 19, 16, 21], ![-55, -58, 58, 60, 87], ![-142, -245, 153, 182, 285], ![-88, -250, 99, 141, 237], ![38, 91, -42, -56, -92]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![369, -210, 46, 108, 294]] ![![-49, 28, -6, -14, -38]]
  ![![-22225, 12694, -2760, -6490, -17636]] where
 M := ![![![-22225, 12694, -2760, -6490, -17636]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![-22225, 12694, -2760, -6490, -17636]] ![![1, -4, 19, 16, 21]]
  ![![37, 0, 0, 0, 0]] where
 M := ![![![-81437, 46472, -10101, -23754, -64565]]]
 hmul := by decide  
 g := ![![![![-2201, 1256, -273, -642, -1745]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-441, 261, -59, -134, -360]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![-441, 261, -59, -134, -360]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![33, 29, 39, 17, 1]] where
  M :=![![![-441, 261, -59, -134, -360], ![268, -131, 26, 66, 192], ![-132, 130, -33, -68, -168], ![134, -45, 13, 33, 96], ![32, -34, 8, 14, 37]]]
  hmulB := by decide  
  f := ![![![-1, -1, 1, 0, 0]], ![![0, -1, 0, 2, 0]], ![![-4, -10, 7, 8, 24]], ![![-6, -5, -1, -5, -24]], ![![-7, -13, 7, 7, 13]]]
  g := ![![![279, 261, 341, 146, -360], ![-148, -139, -182, -78, 192], ![132, 122, 159, 68, -168], ![-74, -69, -91, -39, 96], ![-29, -27, -35, -15, 37]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 4 2 5 [36, 31, 37, 0, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 29, 34, 6], [23, 36, 24, 37], [8, 16, 24, 39], [0, 1]]
 g := ![![[2, 18, 39, 25], [28, 29, 36], [40, 39, 16], [0, 1], []], ![[30, 29, 37, 39, 9, 35], [16, 12, 10], [24, 36, 40], [8, 33, 5, 29, 18, 19], [8, 39, 36]], ![[2, 9, 30, 14, 29, 20], [10, 14, 21], [40, 0, 23], [35, 38, 9, 14, 28, 9], [24, 13, 16]], ![[10, 24, 28, 14, 38, 33], [17, 10, 18], [0, 7, 9], [40, 32, 19, 14, 29, 8], [36, 27, 4]]]
 h' := ![![[10, 29, 34, 6], [1, 10, 8, 5], [36, 21, 40, 6], [0, 5, 10, 4], [0, 0, 1], [0, 1]], ![[23, 36, 24, 37], [37, 35, 22, 32], [30, 14, 26, 16], [19, 26, 39, 32], [17, 35, 32, 25], [10, 29, 34, 6]], ![[8, 16, 24, 39], [14, 1, 8, 6], [13, 14, 37, 29], [31, 7, 0, 8], [34, 34, 0, 34], [23, 36, 24, 37]], ![[0, 1], [2, 36, 3, 39], [32, 33, 20, 31], [27, 3, 33, 38], [39, 13, 8, 23], [8, 16, 24, 39]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [35, 35, 40], []]
 b := ![[], [], [13, 28, 38, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 4
  hpos := by decide
  P := [36, 31, 37, 0, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![41230076, 82574960, -41058634, -51295230, -81891840]
  a := ![8, 20, -22, -30, -48]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![66918556, 59937520, 76895686, 32704050, -81891840]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 2825761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 1, -1, 0, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![1, 1, -1, 0, 0]] 
 ![![41, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![1, 1, -1, 0, 0], ![0, 1, 0, -2, 0], ![4, 10, -7, -8, -24], ![6, 5, 1, 5, 24], ![-4, -4, 2, -2, -5]]]
  hmulB := by decide  
  f := ![![![441, -261, 59, 134, 360]], ![![58, -35, 8, 18, 48]], ![![57, -35, 8, 18, 48]], ![![29, -18, 4, 9, 24]], ![![53, -31, 7, 16, 43]]]
  g := ![![![0, 1, -1, 0, 0], ![0, 1, 0, -2, 0], ![3, 10, -7, -8, -24], ![-4, 5, 1, 5, 24], ![1, -4, 2, -2, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![-441, 261, -59, -134, -360]] ![![1, 1, -1, 0, 0]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-565, 300, -64, -154, -426]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![-565, 300, -64, -154, -426]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![20, 32, 27, 26, 1]] where
  M :=![![![-565, 300, -64, -154, -426], ![308, -221, 46, 108, 282], ![-216, 50, -25, -40, -114], ![148, -90, 2, 29, 102], ![52, -20, 10, 16, 37]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 2, 6]], ![![-4, -3, 2, -4, -6]], ![![8, 10, -11, 0, -18]], ![![-4, -10, 14, 7, 54]], ![![0, -2, 3, 2, 19]]]
  g := ![![![185, 324, 266, 254, -426], ![-124, -215, -176, -168, 282], ![48, 86, 71, 68, -114], ![-44, -78, -64, -61, 102], ![-16, -28, -23, -22, 37]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 4 2 5 [3, 8, 16, 13, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 20, 17, 14], [32, 8, 42, 12], [3, 14, 27, 17], [0, 1]]
 g := ![![[16, 27, 18, 16], [32, 39, 11, 14], [6, 5, 17], [30, 1], []], ![[8, 13, 5, 9, 21, 24], [39, 28, 38, 0, 36, 10], [36, 31, 36], [13, 28, 15, 3, 17, 13], [10, 35, 24]], ![[5, 8, 42, 27, 1, 20], [33, 18, 33, 32, 28, 12], [8, 10, 4], [15, 22, 6, 24, 3, 30], [5, 39, 15]], ![[14, 12, 24, 40, 40, 4], [32, 12, 18, 21, 38, 40], [36, 27, 41], [17, 28, 27, 37, 42, 40], [34, 42, 31]]]
 h' := ![![[38, 20, 17, 14], [33, 18, 4, 39], [41, 32, 29, 10], [39, 15, 28, 24], [0, 0, 1], [0, 1]], ![[32, 8, 42, 12], [7, 29, 25, 33], [42, 19, 31, 20], [8, 25, 5, 37], [38, 2, 19, 2], [38, 20, 17, 14]], ![[3, 14, 27, 17], [33, 19, 11, 39], [17, 30, 31, 1], [27, 23, 6, 41], [20, 11, 36, 29], [32, 8, 42, 12]], ![[0, 1], [10, 20, 3, 18], [35, 5, 38, 12], [10, 23, 4, 27], [36, 30, 30, 12], [3, 14, 27, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [32, 0, 10], []]
 b := ![[], [], [36, 11, 10, 35], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 4
  hpos := by decide
  P := [3, 8, 16, 13, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![67723831, 62779411, -62165902, 39706912, -9803923]
  a := ![15, 37, -20, -24, -77]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![6134937, 8755929, 4710233, 6851370, -9803923]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 3418801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 0, 0, -2, -6]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-1, 0, 0, -2, -6]] 
 ![![43, 0, 0, 0, 0], ![37, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![39, 0, 0, 1, 0], ![23, 0, 0, 0, 1]] where
  M :=![![![-1, 0, 0, -2, -6], ![4, 3, -2, 4, 6], ![-8, -10, 11, 0, 18], ![4, 10, -14, -7, -54], ![4, 0, 2, 8, 29]]]
  hmulB := by decide  
  f := ![![![565, -300, 64, 154, 426]], ![![479, -253, 54, 130, 360]], ![![97, -50, 11, 26, 72]], ![![509, -270, 58, 139, 384]], ![![301, -160, 34, 82, 227]]]
  g := ![![![5, 0, 0, -2, -6], ![-9, 3, -2, 4, 6], ![-3, -10, 11, 0, 18], ![29, 10, -14, -7, -54], ![-23, 0, 2, 8, 29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![-565, 300, -64, -154, -426]] ![![-1, 0, 0, -2, -6]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![597, -320, 53, 152, 439]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![597, -320, 53, 152, 439]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![5, 27, 18, 33, 1]] where
  M :=![![![597, -320, 53, 152, 439], ![-304, 276, -98, -164, -371], ![328, 145, -107, -110, -113], ![-54, 310, -91, -159, -321], ![-92, -55, 26, 32, 38]]]
  hmulB := by decide  
  f := ![![![3, 0, 1, 6, 19]], ![![-12, -8, 6, -12, -23]], ![![24, 25, -27, 10, -29]], ![![-22, -40, 47, 17, 147]], ![![-13, -23, 26, 9, 79]]]
  g := ![![![-34, -259, -167, -305, 439], ![33, 219, 140, 257, -371], ![19, 68, 41, 77, -113], ![33, 191, 121, 222, -321], ![-6, -23, -14, -26, 38]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 4 2 5 [23, 10, 22, 3, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [41, 3, 26, 7], [26, 5, 8, 2], [24, 38, 13, 38], [0, 1]]
 g := ![![[35, 41, 5, 36], [22, 12, 26, 21], [13, 2, 11, 28], [44, 1], []], ![[5, 16, 39, 14, 12, 24], [14, 7, 8, 1, 32, 27], [30, 15, 43, 3, 45, 7], [36, 13, 10, 31, 36, 16], [23, 29, 2]], ![[2, 15, 44, 18, 38, 24], [27, 18, 6, 0, 41, 17], [11, 37, 39, 5, 35, 16], [30, 45, 44, 10, 7, 12], [30, 20, 4]], ![[43, 13, 46, 35, 11, 22], [34, 34, 34, 33, 0, 43], [10, 42, 16, 17, 44, 26], [11, 0, 39, 13, 42, 29], [27, 40, 34]]]
 h' := ![![[41, 3, 26, 7], [11, 28, 29, 6], [30, 26, 31, 31], [22, 7, 9, 34], [0, 0, 1], [0, 1]], ![[26, 5, 8, 2], [0, 0, 10, 32], [3, 42, 44, 20], [40, 40, 23, 1], [24, 7, 30, 3], [41, 3, 26, 7]], ![[24, 38, 13, 38], [13, 12, 40, 23], [13, 10, 17, 28], [35, 6, 24, 33], [33, 17, 6, 37], [26, 5, 8, 2]], ![[0, 1], [2, 7, 15, 33], [39, 16, 2, 15], [31, 41, 38, 26], [2, 23, 10, 7], [24, 38, 13, 38]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [25, 12, 38], []]
 b := ![[], [], [43, 31, 13, 28], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 4
  hpos := by decide
  P := [23, 10, 22, 3, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2337247, 5152956, -2547420, -3725852, -6130984]
  a := ![5, 11, -13, -16, -31]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![701961, 3631692, 2293836, 4225460, -6130984]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 4879681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, 0, -1, -6, -19]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-3, 0, -1, -6, -19]] 
 ![![47, 0, 0, 0, 0], ![32, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![23, 0, 0, 1, 0], ![27, 0, 0, 0, 1]] where
  M :=![![![-3, 0, -1, -6, -19], ![12, 8, -6, 12, 23], ![-24, -25, 27, -10, 29], ![22, 40, -47, -17, -147], ![8, -5, 10, 24, 90]]]
  hmulB := by decide  
  f := ![![![-597, 320, -53, -152, -439]], ![![-400, 212, -34, -100, -291]], ![![-134, 65, -9, -30, -91]], ![![-291, 150, -24, -71, -208]], ![![-341, 185, -31, -88, -253]]]
  g := ![![![14, 0, -1, -6, -19], ![-23, 8, -6, 12, 23], ![-1, -25, 27, -10, 29], ![76, 40, -47, -17, -147], ![-62, -5, 10, 24, 90]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![597, -320, 53, 152, 439]] ![![-3, 0, -1, -6, -19]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-23, -15, 4, -40, -111]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-23, -15, 4, -40, -111]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![47, 3, 31, 8, 1]] where
  M :=![![![-23, -15, 4, -40, -111], ![80, 66, -60, 70, 75], ![-140, -195, 211, 10, 465], ![60, 235, -310, -239, -1335], ![96, 5, 34, 190, 620]]]
  hmulB := by decide  
  f := ![![![5, -5, -2, 0, 3]], ![![0, 8, -10, -10, -15]], ![![20, 35, -27, -30, -45]], ![![20, 45, -20, -27, -45]], ![![19, 23, -21, -22, -31]]]
  g := ![![![98, 6, 65, 16, -111], ![-65, -3, -45, -10, 75], ![-415, -30, -268, -70, 465], ![1185, 80, 775, 197, -1335], ![-548, -35, -362, -90, 620]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 4 2 5 [46, 51, 38, 38, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [16, 31, 42, 8], [6, 30, 45, 47], [46, 44, 19, 51], [0, 1]]
 g := ![![[25, 19, 5, 36], [28, 40, 28], [9, 41, 50, 15], [28, 15, 1], []], ![[12, 50, 44, 33, 7, 33], [11, 39, 9], [10, 32, 10, 51, 24, 31], [9, 21, 10], [48, 23, 49, 45, 3, 35]], ![[37, 20, 50, 29, 27, 38], [37, 48, 17], [9, 3, 23, 21, 23, 42], [41, 26, 52], [25, 12, 13, 40, 30, 49]], ![[28, 10, 9, 29, 49, 12], [5, 20, 40], [1, 7, 23, 17, 52, 51], [36, 19, 44], [0, 17, 40, 21, 2, 45]]]
 h' := ![![[16, 31, 42, 8], [31, 2, 4, 6], [10, 31, 26, 9], [37, 2, 33, 11], [0, 0, 0, 1], [0, 1]], ![[6, 30, 45, 47], [11, 37, 21, 17], [26, 46, 16, 50], [39, 45, 6, 14], [33, 3, 46, 13], [16, 31, 42, 8]], ![[46, 44, 19, 51], [37, 5, 13, 20], [34, 26, 14, 21], [51, 21, 38, 29], [20, 35, 32, 23], [6, 30, 45, 47]], ![[0, 1], [44, 9, 15, 10], [3, 3, 50, 26], [29, 38, 29, 52], [28, 15, 28, 16], [46, 44, 19, 51]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [3, 43, 6], []]
 b := ![[], [], [39, 4, 35, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 4
  hpos := by decide
  P := [46, 51, 38, 38, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2341652, 496395, -513442, 2319802, 14342541]
  a := ![-6, -15, 18, 14, 39]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-12674675, -802476, -8398721, -2121142, 14342541]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 7890481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, -5, -2, 0, 3]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![5, -5, -2, 0, 3]] 
 ![![53, 0, 0, 0, 0], ![15, 1, 0, 0, 0], ![40, 0, 1, 0, 0], ![51, 0, 0, 1, 0], ![18, 0, 0, 0, 1]] where
  M :=![![![5, -5, -2, 0, 3], ![0, 8, -10, -10, -15], ![20, 35, -27, -30, -45], ![20, 45, -20, -27, -45], ![-8, -15, 8, 10, 16]]]
  hmulB := by decide  
  f := ![![![-23, -15, 4, -40, -111]], ![![-5, -3, 0, -10, -30]], ![![-20, -15, 7, -30, -75]], ![![-21, -10, -2, -43, -132]], ![![-6, -5, 2, -10, -26]]]
  g := ![![![2, -5, -2, 0, 3], ![20, 8, -10, -10, -15], ![55, 35, -27, -30, -45], ![44, 45, -20, -27, -45], ![-17, -15, 8, 10, 16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-23, -15, 4, -40, -111]] ![![5, -5, -2, 0, 3]]
  ![![53, 0, 0, 0, 0]] where
 M := ![![![53, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 7, -11, -8, -50]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![1, 7, -11, -8, -50]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![41, 26, 31, 1, 0], ![30, 37, 46, 0, 1]] where
  M :=![![![1, 7, -11, -8, -50], ![16, -9, 14, 46, 154], ![-92, -60, 35, -96, -218], ![142, 115, -113, 109, 78], ![-28, -48, 60, 18, 179]]]
  hmulB := by decide  
  f := ![![![-149, 87, -21, -46, -122]], ![![92, -41, 4, 18, 58]], ![![-36, 60, -23, -36, -74]], ![![-81, 74, -25, -43, -98]], ![![-46, 65, -26, -40, -83]]]
  g := ![![![31, 35, 43, -8, -50], ![-110, -117, -144, 46, 154], ![176, 178, 221, -96, -218], ![-113, -95, -120, 109, 78], ![-104, -121, -148, 18, 179]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [44, 0, 57, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [40, 56, 31], [21, 2, 28], [0, 1]]
 g := ![![[42, 20, 12], [52, 18, 57], [50, 45], [17, 8, 4], [1]], ![[44, 26, 3, 33], [3, 12, 16, 34], [55, 21], [48, 10, 6, 24], [49, 18, 16, 55]], ![[18, 26, 58, 4], [24, 51, 40, 20], [31, 9], [5, 32, 14, 5], [53, 34, 51, 4]]]
 h' := ![![[40, 56, 31], [13, 16, 22], [49, 38, 36], [19, 50, 35], [15, 0, 2], [0, 1]], ![[21, 2, 28], [30, 46, 9], [40, 13, 11], [49, 21, 27], [12, 30, 4], [40, 56, 31]], ![[0, 1], [57, 56, 28], [42, 8, 12], [52, 47, 56], [26, 29, 53], [21, 2, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34, 2], []]
 b := ![[], [29, 42, 38], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [44, 0, 57, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-96334, -193284, 4224, 6000, 187116]
  a := ![-11, -27, 25, 28, 67]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-100946, -123264, -148968, 6000, 187116]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 205379 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, -87, 21, 46, 122]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![149, -87, 21, 46, 122]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![6, 57, 1, 0, 0], ![3, 2, 0, 1, 0], ![45, 10, 0, 0, 1]] where
  M :=![![![149, -87, 21, 46, 122], ![-92, 41, -4, -18, -58], ![36, -60, 23, 36, 74], ![-54, -5, 5, 3, -6], ![-8, 18, -6, -10, -21]]]
  hmulB := by decide  
  f := ![![![-1, -7, 11, 8, 50]], ![![-16, 9, -14, -46, -154]], ![![-14, 9, -13, -42, -140]], ![![-3, -2, 2, -3, -4]], ![![-3, -3, 5, -2, 9]]]
  g := ![![![-95, -44, 21, 46, 122], ![44, 15, -4, -18, -58], ![-60, -37, 23, 36, 74], ![3, -4, 5, 3, -6], ![17, 10, -6, -10, -21]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P1 : CertificateIrreducibleZModOfList' 59 2 2 5 [5, 50, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 58], [0, 1]]
 g := ![![[10, 12], [16, 46], [26], [9, 53], [9, 1]], ![[0, 47], [17, 13], [26], [14, 6], [18, 58]]]
 h' := ![![[9, 58], [38, 22], [7, 39], [14, 12], [14, 17], [0, 1]], ![[0, 1], [0, 37], [4, 20], [4, 47], [49, 42], [9, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57]]
 b := ![[], [34, 58]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N1 : CertifiedPrimeIdeal' SI59N1 59 where
  n := 2
  hpos := by decide
  P := [5, 50, 1]
  hirr := P59P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-231, -525, 457, 625, 852]
  a := ![0, 0, 4, 5, 4]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-732, -616, 457, 625, 852]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N1 B_one_repr
lemma NI59N1 : Nat.card (O ⧸ I59N1) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![1, 7, -11, -8, -50]] ![![149, -87, 21, 46, 122]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19, -184, 154, 170, 270]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![-19, -184, 154, 170, 270]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![11, 7, 20, 30, 1]] where
  M :=![![![-19, -184, 154, 170, 270], ![-340, -599, 380, 448, 690], ![-896, -1890, 883, 1172, 1926], ![-724, -1470, 436, 715, 1254], ![276, 586, -208, -312, -535]]]
  hmulB := by decide  
  f := ![![![1, 4, -6, -6, -30]], ![![12, 1, 4, 24, 78]], ![![-48, -30, 23, -52, -102]], ![![76, 70, -68, 47, -6]], ![![23, 25, -26, 8, -31]]]
  g := ![![![-49, -34, -86, -130, 270], ![-130, -89, -220, -332, 690], ![-362, -252, -617, -928, 1926], ![-238, -168, -404, -605, 1254], ![101, 71, 172, 258, -535]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 4 2 5 [52, 8, 15, 28, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 4, 5, 41], [47, 2, 55, 9], [25, 54, 1, 11], [0, 1]]
 g := ![![[16, 54, 29, 48], [39, 34, 14], [53, 58, 5, 20], [47, 37, 33, 1], []], ![[26, 37, 7, 56, 4, 13], [6, 4, 15], [3, 20, 40, 17, 32, 15], [18, 27, 6, 55, 14, 27], [58, 17, 9, 33, 30, 52]], ![[42, 25, 33, 36, 38, 42], [11, 50, 48], [36, 41, 60, 46, 23, 48], [52, 0, 38, 14, 15, 58], [8, 23, 9, 20, 29, 58]], ![[46, 26, 7, 5, 22, 21], [5, 56, 13], [25, 4, 52, 25, 14, 24], [27, 12, 0, 10, 10, 11], [47, 4, 8, 36, 0, 50]]]
 h' := ![![[22, 4, 5, 41], [45, 48, 51, 32], [50, 53, 45, 21], [57, 18, 28, 9], [0, 0, 0, 1], [0, 1]], ![[47, 2, 55, 9], [12, 42, 29, 10], [43, 29, 28, 25], [20, 11, 32, 44], [7, 7, 10, 9], [22, 4, 5, 41]], ![[25, 54, 1, 11], [13, 5, 26, 5], [55, 45, 3, 29], [38, 36, 47, 31], [12, 38, 46, 52], [47, 2, 55, 9]], ![[0, 1], [46, 27, 16, 14], [1, 56, 46, 47], [14, 57, 15, 38], [5, 16, 5, 60], [25, 54, 1, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [43, 56, 52], []]
 b := ![[], [], [42, 9, 36, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 4
  hpos := by decide
  P := [52, 8, 15, 28, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4946284012, 6057215676, -3121955262, 890239692, 1197979816]
  a := ![40, 101, -95, -92, -233]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-134942524, -38174476, -443959862, -574576308, 1197979816]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 13845841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -4, 6, 6, 30]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![-1, -4, 6, 6, 30]] 
 ![![61, 0, 0, 0, 0], ![11, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![55, 0, 0, 1, 0], ![37, 0, 0, 0, 1]] where
  M :=![![![-1, -4, 6, 6, 30], ![-12, -1, -4, -24, -78], ![48, 30, -23, 52, 102], ![-76, -70, 68, -47, 6], ![12, 26, -32, -16, -113]]]
  hmulB := by decide  
  f := ![![![19, 184, -154, -170, -270]], ![![9, 43, -34, -38, -60]], ![![15, 34, -17, -22, -36]], ![![29, 190, -146, -165, -264]], ![![7, 102, -90, -98, -155]]]
  g := ![![![-23, -4, 6, 6, 30], ![69, -1, -4, -24, -78], ![-113, 30, -23, 52, 102], ![49, -70, 68, -47, 6], ![79, 26, -32, -16, -113]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![-19, -184, 154, 170, 270]] ![![-1, -4, 6, 6, 30]]
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


lemma PB103I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB103I1 : PrimesBelowBoundCertificateInterval O 23 61 103 where
  m := 9
  g := ![3, 2, 3, 2, 2, 2, 2, 2, 2]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB103I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0, I29N1, I29N2]
    · exact ![I31N0, I31N1]
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
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
    · exact ![841, 841, 29]
    · exact ![29791, 961]
    · exact ![50653, 37, 37]
    · exact ![2825761, 41]
    · exact ![3418801, 43]
    · exact ![4879681, 47]
    · exact ![7890481, 53]
    · exact ![205379, 3481]
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
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
  β := ![I29N2, I37N1, I37N2, I41N1, I43N1, I47N1, I53N1, I61N1]
  Il := ![[I29N2], [], [I37N1, I37N2], [I41N1], [I43N1], [I47N1], [I53N1], [], [I61N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
