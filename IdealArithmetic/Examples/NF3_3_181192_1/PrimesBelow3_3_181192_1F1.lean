
import IdealArithmetic.Examples.NF3_3_181192_1.RI3_3_181192_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0]] 
 ![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [4, 9, 18, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 14, 19], [29, 22, 18], [0, 1]]
 g := ![![[21, 15, 26], [14, 25], [6, 24, 28], [19, 1], []], ![[12, 10, 36, 5], [], [22, 32, 33, 17], [26, 3], [28, 28]], ![[22, 27, 10, 20], [25, 25], [20, 29, 2, 35], [0, 11], [29, 28]]]
 h' := ![![[27, 14, 19], [2, 11, 27], [13, 2, 5], [35, 10, 19], [0, 0, 1], [0, 1]], ![[29, 22, 18], [12, 8, 26], [7, 27], [3, 3, 16], [25, 22, 22], [27, 14, 19]], ![[0, 1], [27, 18, 21], [33, 8, 32], [3, 24, 2], [22, 15, 14], [29, 22, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26, 6], []]
 b := ![[], [14, 7, 25], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [4, 9, 18, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-434824, -208976, -145040]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-11752, -5648, -3920]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 50653 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def PBC37 : ContainsPrimesAboveP 37 ![I37N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![37, 0, 0]]) timesTableT_eq_Table B_one_repr 37 (by decide) 𝕀

instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, -2, -2]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![-5, -2, -2]] 
 ![![41, 0, 0], ![0, 41, 0], ![23, 1, 1]] where
  M :=![![![-5, -2, -2], ![-112, -53, -12], ![-214, -102, -61]]]
  hmulB := by decide  
  f := ![![![-49, -2, 2]], ![![104, 3, -4]], ![![-25, -1, 1]]]
  g := ![![![1, 0, -2], ![4, -1, -12], ![29, -1, -61]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [29, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 40], [0, 1]]
 g := ![![[12, 2], [40], [8], [7, 31], [1]], ![[13, 39], [40], [8], [2, 10], [1]]]
 h' := ![![[21, 40], [25, 24], [18, 32], [2, 7], [12, 21], [0, 1]], ![[0, 1], [37, 17], [34, 9], [26, 34], [2, 20], [21, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [34, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [29, 20, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![445, 137, 1408]
  a := ![3, -3, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-779, -31, 1408]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-49, -2, 2]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-49, -2, 2]] 
 ![![41, 0, 0], ![35, 1, 0], ![31, 0, 1]] where
  M :=![![![-49, -2, 2], ![104, 3, -4], ![-2, 2, -1]]]
  hmulB := by decide  
  f := ![![![-5, -2, -2]], ![![-7, -3, -2]], ![![-9, -4, -3]]]
  g := ![![![-1, -2, 2], ![3, 3, -4], ![-1, 2, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![-5, -2, -2]] ![![-49, -2, 2]]
  ![![41, 0, 0]] where
 M := ![![![41, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19168, 9028, 3773]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![19168, 9028, 3773]] 
 ![![43, 0, 0], ![0, 43, 0], ![40, 8, 1]] where
  M :=![![![19168, 9028, 3773], ![221798, 104465, 43658], ![687481, 323798, 135322]]]
  hmulB := by decide  
  f := ![![![-922, -66, 47]], ![![2406, 319, -170]], ![![-435, -12, 16]]]
  g := ![![![-3064, -492, 3773], ![-35454, -5693, 43658], ![-109893, -17646, 135322]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [19, 9, 1] where
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
 g := ![![[5, 9], [0, 11], [31], [0, 38], [1]], ![[10, 34], [30, 32], [31], [2, 5], [1]]]
 h' := ![![[34, 42], [0, 3], [13, 22], [0, 26], [24, 34], [0, 1]], ![[0, 1], [16, 40], [30, 21], [24, 17], [19, 9], [34, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [24, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [19, 9, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![227401, 109834, 120982]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-107253, -19954, 120982]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![922, 66, -47]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![922, 66, -47]] 
 ![![43, 0, 0], ![9, 1, 0], ![4, 0, 1]] where
  M :=![![![922, 66, -47], ![-2406, -319, 170], ![1073, 428, -168]]]
  hmulB := by decide  
  f := ![![![-19168, -9028, -3773]], ![![-9170, -4319, -1805]], ![![-17771, -8370, -3498]]]
  g := ![![![12, 66, -47], ![-5, -319, 170], ![-49, 428, -168]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![19168, 9028, 3773]] ![![922, 66, -47]]
  ![![43, 0, 0]] where
 M := ![![![-43, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0]] 
 ![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [21, 33, 45, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [32, 45, 6], [17, 1, 41], [0, 1]]
 g := ![![[41, 21, 6], [4, 8, 7], [13, 44, 16], [18, 2, 1], []], ![[36, 36, 36, 8], [39, 10, 25, 3], [30, 44, 17, 27], [24, 14, 4, 6], [1, 36]], ![[8, 31, 29, 30], [10, 8, 5, 40], [18, 32, 26, 5], [18, 25, 15, 23], [13, 36]]]
 h' := ![![[32, 45, 6], [10, 16, 37], [9, 14, 30], [45, 22, 43], [0, 0, 1], [0, 1]], ![[17, 1, 41], [33, 20, 39], [44, 4, 20], [27, 5, 34], [16, 23, 1], [32, 45, 6]], ![[0, 1], [28, 11, 18], [22, 29, 44], [26, 20, 17], [16, 24, 45], [17, 1, 41]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 10], []]
 b := ![[], [31, 32, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [21, 33, 45, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-952690, -465723, -411156]
  a := ![-4, 3, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-20270, -9909, -8748]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 103823 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def PBC47 : ContainsPrimesAboveP 47 ![I47N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![47, 0, 0]]) timesTableT_eq_Table B_one_repr 47 (by decide) 𝕀

instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3253, -252, 172]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-3253, -252, 172]] 
 ![![53, 0, 0], ![0, 1, 0], ![27, 0, 1]] where
  M :=![![![-3253, -252, 172], ![8784, 1299, -664], ![-4492, -1828, 715]]]
  hmulB := by decide  
  f := ![![![285007, 134236, 56100]], ![![62224, 29307, 12248]], ![![338061, 159224, 66543]]]
  g := ![![![-149, -252, 172], ![504, 1299, -664], ![-449, -1828, 715]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N0 : Nat.card (O ⧸ I53N0) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N0)

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := prime_ideal_of_norm_prime hp53.out _ NI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-828, -390, -163]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-828, -390, -163]] 
 ![![53, 0, 0], ![14, 1, 0], ![8, 0, 1]] where
  M :=![![![-828, -390, -163], ![-9582, -4513, -1886], ![-29699, -13988, -5846]]]
  hmulB := by decide  
  f := ![![![1630, 104, -79]], ![![354, 19, -16]], ![![273, 26, -16]]]
  g := ![![![112, -390, -163], ![1296, -4513, -1886], ![4017, -13988, -5846]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1

def I53N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![26, 12, 5]] i)))

def SI53N2: IdealEqSpanCertificate' Table ![![26, 12, 5]] 
 ![![53, 0, 0], ![38, 1, 0], ![20, 0, 1]] where
  M :=![![![26, 12, 5], ![294, 139, 58], ![913, 430, 180]]]
  hmulB := by decide  
  f := ![![![80, -10, 1]], ![![58, -5, 0]], ![![21, -8, 2]]]
  g := ![![![-10, 12, 5], ![-116, 139, 58], ![-359, 430, 180]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N2 : Nat.card (O ⧸ I53N2) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N2)

lemma isPrimeI53N2 : Ideal.IsPrime I53N2 := prime_ideal_of_norm_prime hp53.out _ NI53N2
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-3253, -252, 172]] ![![-828, -390, -163]]
  ![![-80, 10, -1]] where
 M := ![![![-80, 10, -1]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI53N1 : IdealMulLeCertificate' Table 
  ![![-80, 10, -1]] ![![26, 12, 5]]
  ![![53, 0, 0]] where
 M := ![![![-53, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0]] 
 ![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [20, 27, 19, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [28, 5, 19], [12, 53, 40], [0, 1]]
 g := ![![[34, 11, 20], [32, 33, 16], [8, 35], [27, 8, 7], [1]], ![[51, 50, 23, 48], [28, 48, 16, 17], [41, 16], [28, 22, 35, 7], [43, 13, 56, 15]], ![[17, 29, 53, 38], [50, 10, 6, 24], [8, 28], [41, 35, 33, 56], [52, 9, 41, 44]]]
 h' := ![![[28, 5, 19], [9, 56, 43], [39, 39, 55], [50, 42, 34], [39, 32, 40], [0, 1]], ![[12, 53, 40], [16, 8, 39], [18, 9, 57], [37, 21, 4], [29, 14, 14], [28, 5, 19]], ![[0, 1], [44, 54, 36], [38, 11, 6], [27, 55, 21], [39, 13, 5], [12, 53, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 31], []]
 b := ![[], [16, 36, 17], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [20, 27, 19, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-433591, -208329, -144196]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-7349, -3531, -2444]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 205379 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def PBC59 : ContainsPrimesAboveP 59 ![I59N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![59, 0, 0]]) timesTableT_eq_Table B_one_repr 59 (by decide) 𝕀

instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0]] 
 ![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [52, 45, 60, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [48, 52, 44], [14, 8, 17], [0, 1]]
 g := ![![[46, 41, 12], [42, 27], [31, 48, 60], [18, 33, 1], [1]], ![[30, 38, 22, 35], [41, 41], [23, 59, 26, 30], [45, 8, 8, 32], [36, 24, 33, 28]], ![[15, 44, 47, 54], [55, 1], [51, 53, 48, 38], [45, 6, 1, 37], [53, 24, 15, 33]]]
 h' := ![![[48, 52, 44], [17, 60, 16], [35, 27, 24], [40, 56, 50], [9, 16, 1], [0, 1]], ![[14, 8, 17], [25, 49, 23], [12, 0, 38], [36, 48, 58], [18, 11, 41], [48, 52, 44]], ![[0, 1], [48, 13, 22], [23, 34, 60], [42, 18, 14], [49, 34, 19], [14, 8, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50], []]
 b := ![[], [31, 46], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [52, 45, 60, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![224935670, 107463212, 67457094]
  a := ![22, -1, 43]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3687470, 1761692, 1105854]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 226981 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def PBC61 : ContainsPrimesAboveP 61 ![I61N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![61, 0, 0]]) timesTableT_eq_Table B_one_repr 61 (by decide) 𝕀

instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0]] 
 ![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [35, 2, 15, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 7, 32], [12, 59, 35], [0, 1]]
 g := ![![[18, 32, 33], [10, 9, 10], [39, 15], [24, 15], [52, 1], []], ![[13, 6, 29, 41], [48, 54, 54, 50], [2, 55], [58, 1], [40, 64], [29, 19]], ![[28, 49, 47, 24], [2, 12, 58, 54], [31, 37], [17, 39], [6, 49], [26, 19]]]
 h' := ![![[40, 7, 32], [52, 23, 10], [31, 15, 12], [18, 6, 22], [56, 62, 22], [0, 0, 1], [0, 1]], ![[12, 59, 35], [55, 5, 53], [13, 25, 49], [63, 7, 16], [63, 64, 66], [49, 38, 59], [40, 7, 32]], ![[0, 1], [38, 39, 4], [64, 27, 6], [55, 54, 29], [28, 8, 46], [38, 29, 7], [12, 59, 35]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 25], []]
 b := ![[], [62, 4, 39], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [35, 2, 15, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10318, 4824, 2077]
  a := ![0, 1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![154, 72, 31]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 300763 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def PBC67 : ContainsPrimesAboveP 67 ![I67N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![67, 0, 0]]) timesTableT_eq_Table B_one_repr 67 (by decide) 𝕀


def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![111, 40, -16]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![111, 40, -16]] 
 ![![71, 0, 0], ![20, 1, 0], ![12, 0, 1]] where
  M :=![![![111, 40, -16], ![-784, -329, 128], ![1312, 584, -225]]]
  hmulB := by decide  
  f := ![![![-727, -344, -144]], ![![-324, -153, -64]], ![![-492, -232, -97]]]
  g := ![![![-7, 40, -16], ![60, -329, 128], ![-108, 584, -225]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N0 : Nat.card (O ⧸ I71N0) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N0)

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := prime_ideal_of_norm_prime hp71.out _ NI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![259, 114, -44]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![259, 114, -44]] 
 ![![71, 0, 0], ![30, 1, 0], ![67, 0, 1]] where
  M :=![![![259, 114, -44], ![-2148, -955, 368], ![3824, 1706, -657]]]
  hmulB := by decide  
  f := ![![![373, 166, 68]], ![![214, 97, 40]], ![![529, 240, 99]]]
  g := ![![![-3, 114, -44], ![26, -955, 368], ![-47, 1706, -657]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![111, 40, -16]] ![![111, 40, -16]]
  ![![-40031, -18064, 6944]] where
 M := ![![![-40031, -18064, 6944]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI71N1 : IdealMulLeCertificate' Table 
  ![![-40031, -18064, 6944]] ![![259, 114, -44]]
  ![![71, 0, 0]] where
 M := ![![![54987299, 24534050, -9448396]]]
 hmul := by decide  
 g := ![![![![774469, 345550, -133076]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N0, I71N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N0
    exact isPrimeI71N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0 ⊙ MulI71N1)
instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-55, -28, -12]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![-55, -28, -12]] 
 ![![73, 0, 0], ![31, 1, 0], ![60, 0, 1]] where
  M :=![![![-55, -28, -12], ![-704, -327, -136], ![-2148, -1012, -423]]]
  hmulB := by decide  
  f := ![![![689, 300, -116]], ![![215, 93, -36]], ![![704, 308, -119]]]
  g := ![![![21, -28, -12], ![241, -327, -136], ![748, -1012, -423]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N0 : Nat.card (O ⧸ I73N0) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N0)

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := prime_ideal_of_norm_prime hp73.out _ NI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1448, -682, -285]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-1448, -682, -285]] 
 ![![73, 0, 0], ![52, 1, 0], ![31, 0, 1]] where
  M :=![![![-1448, -682, -285], ![-16754, -7891, -3298], ![-51933, -24460, -10222]]]
  hmulB := by decide  
  f := ![![![7278, 304, -301]], ![![4970, 209, -206]], ![![3097, 126, -127]]]
  g := ![![![587, -682, -285], ![6792, -7891, -3298], ![21053, -24460, -10222]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1

def I73N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-106, -18, -3]] i)))

def SI73N2: IdealEqSpanCertificate' Table ![![-106, -18, -3]] 
 ![![73, 0, 0], ![62, 1, 0], ![4, 0, 1]] where
  M :=![![![-106, -18, -3], ![-198, -163, -78], ![-1131, -528, -220]]]
  hmulB := by decide  
  f := ![![![5324, 2376, -915]], ![![3910, 1745, -672]], ![![1385, 618, -238]]]
  g := ![![![14, -18, -3], ![140, -163, -78], ![445, -528, -220]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N2 : Nat.card (O ⧸ I73N2) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N2)

lemma isPrimeI73N2 : Ideal.IsPrime I73N2 := prime_ideal_of_norm_prime hp73.out _ NI73N2
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![-55, -28, -12]] ![![-1448, -682, -285]]
  ![![1171948, 551978, 230683]] where
 M := ![![![1171948, 551978, 230683]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI73N1 : IdealMulLeCertificate' Table 
  ![![1171948, 551978, 230683]] ![![-106, -18, -3]]
  ![![73, 0, 0]] where
 M := ![![![-494420605, -232868102, -97320388]]]
 hmul := by decide  
 g := ![![![![-6772885, -3189974, -1333156]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1, I73N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
    exact isPrimeI73N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0 ⊙ MulI73N1)
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6, -140, 45]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![6, -140, 45]] 
 ![![79, 0, 0], ![5, 1, 0], ![35, 0, 1]] where
  M :=![![![6, -140, 45], ![2150, 1271, -470], ![-5175, -2330, 896]]]
  hmulB := by decide  
  f := ![![![-43716, -20590, -8605]], ![![-9170, -4319, -1805]], ![![-39215, -18470, -7719]]]
  g := ![![![-11, -140, 45], ![155, 1271, -470], ![-315, -2330, 896]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N0 : Nat.card (O ⧸ I79N0) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N0)

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := prime_ideal_of_norm_prime hp79.out _ NI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1217, 574, 240]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![1217, 574, 240]] 
 ![![79, 0, 0], ![74, 1, 0], ![72, 0, 1]] where
  M :=![![![1217, 574, 240], ![14108, 6643, 2776], ![43716, 20590, 8605]]]
  hmulB := by decide  
  f := ![![![5175, 2330, -896]], ![![4294, 1935, -744]], ![![5708, 2566, -987]]]
  g := ![![![-741, 574, 240], ![-8574, 6643, 2776], ![-26576, 20590, 8605]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1

def I79N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![0, 0, -1]] i)))

def SI79N2: IdealEqSpanCertificate' Table ![![0, 0, -1]] 
 ![![79, 0, 0], ![78, 1, 0], ![0, 0, 1]] where
  M :=![![![0, 0, -1], ![-54, -25, -2], ![-53, -26, -26]]]
  hmulB := by decide  
  f := ![![![-598, -26, 25]], ![![-574, -25, 24]], ![![-1, 0, 0]]]
  g := ![![![0, 0, -1], ![24, -25, -2], ![25, -26, -26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N2 : Nat.card (O ⧸ I79N2) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N2)

lemma isPrimeI79N2 : Ideal.IsPrime I79N2 := prime_ideal_of_norm_prime hp79.out _ NI79N2
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![6, -140, 45]] ![![1217, 574, 240]]
  ![![-598, -26, 25]] where
 M := ![![![-598, -26, 25]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI79N1 : IdealMulLeCertificate' Table 
  ![![-598, -26, 25]] ![![0, 0, -1]]
  ![![79, 0, 0]] where
 M := ![![![79, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1, I79N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
    exact isPrimeI79N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0 ⊙ MulI79N1)


lemma PB95I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB95I1 : PrimesBelowBoundCertificateInterval O 31 79 95 where
  m := 11
  g := ![1, 2, 2, 1, 3, 1, 1, 1, 3, 3, 3]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB95I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0]
    · exact ![I53N0, I53N1, I53N2]
    · exact ![I59N0]
    · exact ![I61N0]
    · exact ![I67N0]
    · exact ![I71N0, I71N0, I71N1]
    · exact ![I73N0, I73N1, I73N2]
    · exact ![I79N0, I79N1, I79N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC37
    · exact PBC41
    · exact PBC43
    · exact PBC47
    · exact PBC53
    · exact PBC59
    · exact PBC61
    · exact PBC67
    · exact PBC71
    · exact PBC73
    · exact PBC79
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![50653]
    · exact ![1681, 41]
    · exact ![1849, 43]
    · exact ![103823]
    · exact ![53, 53, 53]
    · exact ![205379]
    · exact ![226981]
    · exact ![300763]
    · exact ![71, 71, 71]
    · exact ![73, 73, 73]
    · exact ![79, 79, 79]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N0
      exact NI71N1
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
      exact NI73N2
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
      exact NI79N2
  β := ![I41N1, I43N1, I53N0, I53N1, I53N2, I71N0, I71N1, I73N0, I73N1, I73N2, I79N0, I79N1, I79N2]
  Il := ![[], [I41N1], [I43N1], [], [I53N0, I53N1, I53N2], [], [], [], [I71N0, I71N0, I71N1], [I73N0, I73N1, I73N2], [I79N0, I79N1, I79N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
