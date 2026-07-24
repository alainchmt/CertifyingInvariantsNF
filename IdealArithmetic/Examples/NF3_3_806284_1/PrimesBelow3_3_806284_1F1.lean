
import IdealArithmetic.Examples.NF3_3_806284_1.RI3_3_806284_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19525, -216, 396]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![-19525, -216, 396]] 
 ![![37, 0, 0], ![0, 37, 0], ![36, 23, 1]] where
  M :=![![![-19525, -216, 396], ![40788, 455, -828], ![-63036, -720, 1283]]]
  hmulB := by decide  
  f := ![![![335, 216, 36]], ![![3708, 2387, 396]], ![![3132, 2017, 335]]]
  g := ![![![-913, -252, 396], ![1908, 527, -828], ![-2952, -817, 1283]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [2, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 36], [0, 1]]
 g := ![![[12, 25], [7], [15, 1], [21], [1]], ![[4, 12], [7], [28, 36], [21], [1]]]
 h' := ![![[13, 36], [35, 32], [7, 9], [36, 36], [35, 13], [0, 1]], ![[0, 1], [7, 5], [13, 28], [23, 1], [19, 24], [13, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31]]
 b := ![[], [1, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [2, 24, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![311, 802, 392]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-373, -222, 392]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-335, -216, -36]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-335, -216, -36]] 
 ![![37, 0, 0], ![29, 1, 0], ![9, 0, 1]] where
  M :=![![![-335, -216, -36], ![-3708, -2387, -396], ![-18540, -11952, -1991]]]
  hmulB := by decide  
  f := ![![![19525, 216, -396]], ![![14201, 157, -288]], ![![6453, 72, -131]]]
  g := ![![![169, -216, -36], ![1867, -2387, -396], ![9351, -11952, -1991]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![-19525, -216, 396]] ![![-335, -216, -36]]
  ![![37, 0, 0]] where
 M := ![![![-37, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-33, -11, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-33, -11, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![8, 30, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-33, -11, 1], ![103, 7, -23], ![-1236, -535, 30]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-8, -30, 41]], ![![-1, -1, 1], ![7, 17, -23], ![-36, -35, 30]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [31, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [26, 40], [0, 1]]
 g := ![![[19, 4], [36], [8], [15, 20], [1]], ![[0, 37], [36], [8], [2, 21], [1]]]
 h' := ![![[26, 40], [30, 2], [30, 35], [27, 34], [10, 26], [0, 1]], ![[0, 1], [0, 39], [38, 6], [9, 7], [30, 15], [26, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [10, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [31, 15, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-807, 838, 878]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-191, -622, 878]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-18, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-18, 1, 0]] 
 ![![41, 0, 0], ![23, 1, 0], ![11, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-18, 1, 0], ![0, -17, 2], ![103, 51, -19]]]
  hmulB := by decide  
  f := ![![![541, -30, 0], ![1230, 0, 0]], ![![307, -17, 0], ![698, 0, 0]], ![![139, 1, -1], ![316, 21, 0]]]
  g := ![![![1, 0, 0], ![-23, 41, 0], ![-11, 0, 41]], ![![-1, 1, 0], ![9, -17, 2], ![-21, 51, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-33, -11, 1]] ![![41, 0, 0], ![-18, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-738, 41, 0]], ![![-1353, -451, 41], ![697, 205, -41]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-18, 1, 0]]], ![![![-33, -11, 1]], ![![17, 5, -1]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-27, -3, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-27, -3, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![16, 40, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-27, -3, 1], ![103, 21, -7], ![-412, -127, 28]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-16, -40, 43]], ![![-1, -1, 1], ![5, 7, -7], ![-20, -29, 28]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [31, 31, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 42], [0, 1]]
 g := ![![[1, 25], [5, 40], [36], [38, 15], [1]], ![[0, 18], [12, 3], [36], [3, 28], [1]]]
 h' := ![![[12, 42], [17, 38], [33, 13], [26, 6], [12, 12], [0, 1]], ![[0, 1], [0, 5], [17, 30], [12, 37], [27, 31], [12, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [35, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [31, 31, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2040, 26, 149]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-8, -138, 149]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![7, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![7, 1, 0]] 
 ![![43, 0, 0], ![7, 1, 0], ![15, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![7, 1, 0], ![0, 8, 2], ![103, 51, 6]]]
  hmulB := by decide  
  f := ![![![190, 27, 0], ![-1161, 0, 0]], ![![28, 4, 0], ![-171, 0, 0]], ![![64, 5, -1], ![-391, 22, 0]]]
  g := ![![![1, 0, 0], ![-7, 43, 0], ![-15, 0, 43]], ![![0, 1, 0], ![-2, 8, 2], ![-8, 51, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-27, -3, 1]] ![![43, 0, 0], ![7, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![301, 43, 0]], ![![-1161, -129, 43], ![-86, 0, 0]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![7, 1, 0]]], ![![![-27, -3, 1]], ![![-2, 0, 0]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-16, -13, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-16, -13, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![31, 34, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-16, -13, 1], ![103, 22, -27], ![-1442, -637, 49]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-31, -34, 47]], ![![-1, -1, 1], ![20, 20, -27], ![-63, -49, 49]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [5, 40, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 46], [0, 1]]
 g := ![![[8, 24], [18, 42], [11, 1], [38, 2], [1]], ![[35, 23], [30, 5], [18, 46], [5, 45], [1]]]
 h' := ![![[7, 46], [4, 27], [39, 29], [45, 46], [42, 7], [0, 1]], ![[0, 1], [5, 20], [7, 18], [38, 1], [44, 40], [7, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42]]
 b := ![[], [44, 21]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [5, 40, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-469, 1590, 1078]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-721, -746, 1078]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-20, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-20, 1, 0]] 
 ![![47, 0, 0], ![27, 1, 0], ![45, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-20, 1, 0], ![0, -19, 2], ![103, 51, -21]]]
  hmulB := by decide  
  f := ![![![21, 664, -70], ![47, 1645, 0]], ![![21, 379, -40], ![48, 940, 0]], ![![15, 636, -67], ![33, 1575, 0]]]
  g := ![![![1, 0, 0], ![-27, 47, 0], ![-45, 0, 47]], ![![-1, 1, 0], ![9, -19, 2], ![-7, 51, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![-16, -13, 1]] ![![47, 0, 0], ![-20, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![-940, 47, 0]], ![![-752, -611, 47], ![423, 282, -47]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![-20, 1, 0]]], ![![![-16, -13, 1]], ![![9, 6, -1]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-46, 23, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-46, 23, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![7, 23, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-46, 23, 1], ![103, 28, 45], ![2266, 1199, -17]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-7, -23, 53]], ![![-1, 0, 1], ![-4, -19, 45], ![45, 30, -17]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [25, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [48, 52], [0, 1]]
 g := ![![[32, 17], [36], [], [], [48, 1]], ![[0, 36], [36], [], [], [43, 52]]]
 h' := ![![[48, 52], [1, 32], [0, 47], [43], [19], [0, 1]], ![[0, 1], [0, 21], [30, 6], [43], [19], [48, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [46, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [25, 5, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![334, 840, 449]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-53, -179, 449]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![8, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![8, 1, 0]] 
 ![![53, 0, 0], ![8, 1, 0], ![17, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![8, 1, 0], ![0, 9, 2], ![103, 51, 7]]]
  hmulB := by decide  
  f := ![![![145, 18, 0], ![-954, 0, 0]], ![![8, 1, 0], ![-52, 0, 0]], ![![45, 1, -1], ![-296, 27, 0]]]
  g := ![![![1, 0, 0], ![-8, 53, 0], ![-17, 0, 53]], ![![0, 1, 0], ![-2, 9, 2], ![-8, 51, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![-46, 23, 1]] ![![53, 0, 0], ![8, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![424, 53, 0]], ![![-2438, 1219, 53], ![-265, 212, 53]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![8, 1, 0]]], ![![![-46, 23, 1]], ![![-5, 4, 1]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![26, 1, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![26, 1, 0]] 
 ![![59, 0, 0], ![26, 1, 0], ![3, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![26, 1, 0], ![0, 27, 2], ![103, 51, 25]]]
  hmulB := by decide  
  f := ![![![339, 13, 0], ![-767, 0, 0]], ![![130, 5, 0], ![-294, 0, 0]], ![![-33, -15, -1], ![75, 30, 0]]]
  g := ![![![1, 0, 0], ![-26, 59, 0], ![-3, 0, 59]], ![![0, 1, 0], ![-12, 27, 2], ![-22, 51, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N0 : Nat.card (O ⧸ I59N0) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N0)

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := prime_ideal_of_norm_prime hp59.out _ NI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-16, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-16, 1, 0]] 
 ![![59, 0, 0], ![43, 1, 0], ![57, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-16, 1, 0], ![0, -15, 2], ![103, 51, -17]]]
  hmulB := by decide  
  f := ![![![17, 659, -88], ![59, 2596, 0]], ![![17, 479, -64], ![60, 1888, 0]], ![![11, 637, -85], ![37, 2508, 0]]]
  g := ![![![1, 0, 0], ![-43, 59, 0], ![-57, 0, 59]], ![![-1, 1, 0], ![9, -15, 2], ![-19, 51, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-10, 1, 0]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-10, 1, 0]] 
 ![![59, 0, 0], ![49, 1, 0], ![14, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-10, 1, 0], ![0, -9, 2], ![103, 51, -11]]]
  hmulB := by decide  
  f := ![![![201, -20, 0], ![1180, 0, 0]], ![![171, -17, 0], ![1004, 0, 0]], ![![46, 0, -1], ![270, 30, 0]]]
  g := ![![![1, 0, 0], ![-49, 59, 0], ![-14, 0, 59]], ![![-1, 1, 0], ![7, -9, 2], ![-38, 51, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![26, 1, 0]] ![![59, 0, 0], ![-16, 1, 0]]
  ![![59, 0, 0], ![-31, -24, 1]] where
 M := ![![![3481, 0, 0], ![-944, 59, 0]], ![![1534, 59, 0], ![-416, 11, 2]]]
 hmul := by decide  
 g := ![![![![59, 0, 0], ![0, 0, 0]], ![![15, 25, -1], ![59, 0, 0]]], ![![![26, 1, 0], ![0, 0, 0]], ![![25, 25, -1], ![61, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-31, -24, 1]] ![![59, 0, 0], ![-10, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-590, 59, 0]], ![![-1829, -1416, 59], ![413, 236, -59]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-10, 1, 0]]], ![![![-31, -24, 1]], ![![7, 4, -1]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 6, -2]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![19, 6, -2]] 
 ![![61, 0, 0], ![23, 1, 0], ![29, 0, 1]] where
  M :=![![![19, 6, -2], ![-206, -77, 14], ![824, 254, -91]]]
  hmulB := by decide  
  f := ![![![3451, 38, -70]], ![![1183, 13, -24]], ![![1823, 20, -37]]]
  g := ![![![-1, 6, -2], ![19, -77, 14], ![-39, 254, -91]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N0 : Nat.card (O ⧸ I61N0) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N0)

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := prime_ideal_of_norm_prime hp61.out _ NI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![34, 24, 5]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![34, 24, 5]] 
 ![![61, 0, 0], ![41, 1, 0], ![54, 0, 1]] where
  M :=![![![34, 24, 5], ![515, 313, 43], ![1957, 1354, 270]]]
  hmulB := by decide  
  f := ![![![26288, 290, -533]], ![![16769, 185, -340]], ![![24661, 272, -500]]]
  g := ![![![-20, 24, 5], ![-240, 313, 43], ![-1117, 1354, 270]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 12, 2]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![19, 12, 2]] 
 ![![61, 0, 0], ![58, 1, 0], ![58, 0, 1]] where
  M :=![![![19, 12, 2], ![206, 133, 22], ![1030, 664, 111]]]
  hmulB := by decide  
  f := ![![![155, -4, -2]], ![![144, -3, -2]], ![![144, -8, -1]]]
  g := ![![![-13, 12, 2], ![-144, 133, 22], ![-720, 664, 111]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![19, 6, -2]] ![![34, 24, 5]]
  ![![-178, -374, -187]] where
 M := ![![![-178, -374, -187]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![-178, -374, -187]] ![![19, 12, 2]]
  ![![61, 0, 0]] where
 M := ![![![-273036, -176046, -29341]]]
 hmul := by decide  
 g := ![![![![-4476, -2886, -481]]]]
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


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [6, 9, 45, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [62, 32, 66], [27, 34, 1], [0, 1]]
 g := ![![[12, 14, 26], [61, 57, 26], [31, 49], [19, 36], [22, 1], []], ![[27, 40, 4, 50], [26, 49, 45, 12], [25, 59], [34, 36], [24, 17], [25, 1]], ![[28, 21, 61, 24], [3, 11, 1, 19], [9, 65], [39, 10], [38, 19], [23, 1]]]
 h' := ![![[62, 32, 66], [36, 57, 48], [55, 40, 48], [24, 3, 60], [2, 64, 6], [0, 0, 1], [0, 1]], ![[27, 34, 1], [49, 32, 34], [19, 24, 51], [13, 0, 27], [4, 15, 6], [9, 52, 34], [62, 32, 66]], ![[0, 1], [61, 45, 52], [23, 3, 35], [55, 64, 47], [50, 55, 55], [55, 15, 32], [27, 34, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65, 18], []]
 b := ![[], [51, 26, 18], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [6, 9, 45, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![117943919, 98982986, 27543633]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1760357, 1477358, 411099]
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

instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![4, 1, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![4, 1, 0]] 
 ![![71, 0, 0], ![4, 1, 0], ![61, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![4, 1, 0], ![0, 5, 2], ![103, 51, 3]]]
  hmulB := by decide  
  f := ![![![57, 14, 0], ![-994, 0, 0]], ![![-4, -1, 0], ![72, 0, 0]], ![![51, 10, -1], ![-890, 36, 0]]]
  g := ![![![1, 0, 0], ![-4, 71, 0], ![-61, 0, 71]], ![![0, 1, 0], ![-2, 5, 2], ![-4, 51, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N0 : Nat.card (O ⧸ I71N0) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N0)

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := prime_ideal_of_norm_prime hp71.out _ NI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![32, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![32, 1, 0]] 
 ![![71, 0, 0], ![32, 1, 0], ![40, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![32, 1, 0], ![0, 33, 2], ![103, 51, 31]]]
  hmulB := by decide  
  f := ![![![385, 12, 0], ![-852, 0, 0]], ![![160, 5, 0], ![-354, 0, 0]], ![![216, -10, -1], ![-478, 36, 0]]]
  g := ![![![1, 0, 0], ![-32, 71, 0], ![-40, 0, 71]], ![![0, 1, 0], ![-16, 33, 2], ![-39, 51, 31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![35, 1, 0]] i)))

def SI71N2: IdealEqSpanCertificate' Table ![![71, 0, 0], ![35, 1, 0]] 
 ![![71, 0, 0], ![35, 1, 0], ![9, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![35, 1, 0], ![0, 36, 2], ![103, 51, 34]]]
  hmulB := by decide  
  f := ![![![2346, 67, 0], ![-4757, 0, 0]], ![![1120, 32, 0], ![-2271, 0, 0]], ![![254, -11, -1], ![-515, 36, 0]]]
  g := ![![![1, 0, 0], ![-35, 71, 0], ![-9, 0, 71]], ![![0, 1, 0], ![-18, 36, 2], ![-28, 51, 34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![4, 1, 0]] ![![71, 0, 0], ![32, 1, 0]]
  ![![71, 0, 0], ![-7, -17, 1]] where
 M := ![![![5041, 0, 0], ![2272, 71, 0]], ![![284, 71, 0], ![128, 37, 2]]]
 hmul := by decide  
 g := ![![![![71, 0, 0], ![0, 0, 0]], ![![32, 1, 0], ![0, 0, 0]]], ![![![4, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![-7, -17, 1]] ![![71, 0, 0], ![35, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![2485, 71, 0]], ![![-497, -1207, 71], ![-142, -568, 0]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![35, 1, 0]]], ![![![-7, -17, 1]], ![![-2, -8, 0]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1, I71N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
    exact isPrimeI71N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0 ⊙ MulI71N1)
instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1085, 12, -22]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![1085, 12, -22]] 
 ![![73, 0, 0], ![29, 1, 0], ![3, 0, 1]] where
  M :=![![![1085, 12, -22], ![-2266, -25, 46], ![3502, 40, -71]]]
  hmulB := by decide  
  f := ![![![65, 28, -2]], ![![23, 11, 0]], ![![45, 20, -1]]]
  g := ![![![11, 12, -22], ![-23, -25, 46], ![35, 40, -71]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N0 : Nat.card (O ⧸ I73N0) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N0)

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := prime_ideal_of_norm_prime hp73.out _ NI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![93, 60, 10]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![93, 60, 10]] 
 ![![73, 0, 0], ![51, 1, 0], ![61, 0, 1]] where
  M :=![![![93, 60, 10], ![1030, 663, 110], ![5150, 3320, 553]]]
  hmulB := by decide  
  f := ![![![-1439, -20, 30]], ![![-963, -13, 20]], ![![-1273, -20, 27]]]
  g := ![![![-49, 60, 10], ![-541, 663, 110], ![-2711, 3320, 553]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1

def I73N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10, 6, 1]] i)))

def SI73N2: IdealEqSpanCertificate' Table ![![10, 6, 1]] 
 ![![73, 0, 0], ![66, 1, 0], ![52, 0, 1]] where
  M :=![![![10, 6, 1], ![103, 67, 11], ![515, 332, 56]]]
  hmulB := by decide  
  f := ![![![100, -4, -1]], ![![89, -3, -1]], ![![67, -6, 0]]]
  g := ![![![-6, 6, 1], ![-67, 67, 11], ![-333, 332, 56]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N2 : Nat.card (O ⧸ I73N2) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N2)

lemma isPrimeI73N2 : Ideal.IsPrime I73N2 := prime_ideal_of_norm_prime hp73.out _ NI73N2
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![1085, 12, -22]] ![![93, 60, 10]]
  ![![-35, 16, 4]] where
 M := ![![![-35, 16, 4]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI73N1 : IdealMulLeCertificate' Table 
  ![![-35, 16, 4]] ![![10, 6, 1]]
  ![![73, 0, 0]] where
 M := ![![![3358, 2190, 365]]]
 hmul := by decide  
 g := ![![![![46, 30, 5]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0]] 
 ![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [20, 16, 58, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [42, 47, 1], [58, 31, 78], [0, 1]]
 g := ![![[69, 65, 52], [36], [62, 63, 4], [5, 68, 31], [21, 1], []], ![[9, 35, 33, 44], [28, 75, 65, 36], [54, 38, 35, 26], [13, 56, 30, 46], [11, 13], [36, 1]], ![[12, 78, 75, 77], [44, 37, 64, 43], [56, 26, 16, 59], [30, 7, 21, 6], [59, 76], [38, 1]]]
 h' := ![![[42, 47, 1], [70, 0, 17], [24, 6], [58, 54, 2], [54, 39, 30], [0, 0, 1], [0, 1]], ![[58, 31, 78], [43, 25, 53], [39, 45, 6], [69, 78, 37], [69, 9, 21], [17, 34, 31], [42, 47, 1]], ![[0, 1], [19, 54, 9], [56, 28, 73], [24, 26, 40], [14, 31, 28], [76, 45, 47], [58, 31, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62, 27], []]
 b := ![[], [10, 9, 52], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [20, 16, 58, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![46926, 32864, 6794]
  a := ![-1, 2, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![594, 416, 86]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 493039 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def PBC79 : ContainsPrimesAboveP 79 ![I79N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![79, 0, 0]]) timesTableT_eq_Table B_one_repr 79 (by decide) 𝕀



lemma PB200I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB200I1 : PrimesBelowBoundCertificateInterval O 31 79 200 where
  m := 11
  g := ![2, 2, 2, 2, 2, 3, 3, 1, 3, 3, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB200I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1, I59N2]
    · exact ![I61N0, I61N1, I61N2]
    · exact ![I67N0]
    · exact ![I71N0, I71N1, I71N2]
    · exact ![I73N0, I73N1, I73N2]
    · exact ![I79N0]
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
    · exact ![1369, 37]
    · exact ![1681, 41]
    · exact ![1849, 43]
    · exact ![2209, 47]
    · exact ![2809, 53]
    · exact ![59, 59, 59]
    · exact ![61, 61, 61]
    · exact ![300763]
    · exact ![71, 71, 71]
    · exact ![73, 73, 73]
    · exact ![493039]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
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
      exact NI59N2
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
      exact NI61N2
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
      exact NI71N2
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
      exact NI73N2
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
  β := ![I37N1, I41N1, I43N1, I47N1, I53N1, I59N0, I59N1, I59N2, I61N0, I61N1, I61N2, I71N0, I71N1, I71N2, I73N0, I73N1, I73N2]
  Il := ![[I37N1], [I41N1], [I43N1], [I47N1], [I53N1], [I59N0, I59N1, I59N2], [I61N0, I61N1, I61N2], [], [I71N0, I71N1, I71N2], [I73N0, I73N1, I73N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
