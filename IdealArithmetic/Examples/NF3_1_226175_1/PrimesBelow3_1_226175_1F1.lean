
import IdealArithmetic.Examples.NF3_1_226175_1.RI3_1_226175_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![5, 9, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![5, 9, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![5, 9, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![5, 9, 1], ![45, -30, 9], ![405, -270, -30]]]
  hmulB := by decide  
  f := ![![![-4, -9, -1], ![37, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-5, -9, 37]], ![![0, 0, 1], ![0, -3, 9], ![15, 0, -30]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [22, 25, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 36], [0, 1]]
 g := ![![[23, 3], [21], [27, 34], [33], [1]], ![[22, 34], [21], [28, 3], [33], [1]]]
 h' := ![![[12, 36], [23, 15], [35, 13], [17, 16], [15, 12], [0, 1]], ![[0, 1], [18, 22], [6, 24], [24, 21], [11, 25], [12, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [24, 33]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [22, 25, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![112, -50, -59]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![11, 13, -59]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-9, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-9, 1, 0]] 
 ![![37, 0, 0], ![28, 1, 0], ![30, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-9, 1, 0], ![0, -9, 1], ![45, -35, -9]]]
  hmulB := by decide  
  f := ![![![316, -35, 0], ![1295, 0, 0]], ![![244, -27, 0], ![1000, 0, 0]], ![![264, -29, 0], ![1082, 1, 0]]]
  g := ![![![1, 0, 0], ![-28, 37, 0], ![-30, 0, 37]], ![![-1, 1, 0], ![6, -9, 1], ![35, -35, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![5, 9, 1]] ![![37, 0, 0], ![-9, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-333, 37, 0]], ![![185, 333, 37], ![0, -111, 0]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-9, 1, 0]]], ![![![5, 9, 1]], ![![0, -3, 0]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![39, -2, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![39, -2, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![39, 39, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![39, -2, 1], ![45, 4, -2], ![-90, 115, 4]]]
  hmulB := by decide  
  f := ![![![-38, 2, -1], ![41, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-39, -39, 41]], ![![0, -1, 1], ![3, 2, -2], ![-6, -1, 4]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [33, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 40], [0, 1]]
 g := ![![[33, 5], [21], [10], [11, 37], [1]], ![[0, 36], [21], [10], [21, 4], [1]]]
 h' := ![![[18, 40], [12, 13], [34, 29], [6, 25], [8, 18], [0, 1]], ![[0, 1], [0, 28], [23, 12], [5, 16], [4, 23], [18, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [27, 38]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [33, 23, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-529, 783, -248]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![223, 255, -248]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![2, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![2, 1, 0]] 
 ![![41, 0, 0], ![2, 1, 0], ![37, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![2, 1, 0], ![0, 2, 1], ![45, -35, 2]]]
  hmulB := by decide  
  f := ![![![39, 19, 0], ![-779, 0, 0]], ![![-2, -1, 0], ![42, 0, 0]], ![![35, 17, 0], ![-699, 1, 0]]]
  g := ![![![1, 0, 0], ![-2, 41, 0], ![-37, 0, 41]], ![![0, 1, 0], ![-1, 2, 1], ![1, -35, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![39, -2, 1]] ![![41, 0, 0], ![2, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![82, 41, 0]], ![![1599, -82, 41], ![123, 0, 0]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![2, 1, 0]]], ![![![39, -2, 1]], ![![3, 0, 0]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![7, -12, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![7, -12, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![7, 31, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![7, -12, 1], ![45, -28, -12], ![-540, 465, -28]]]
  hmulB := by decide  
  f := ![![![-6, 12, -1], ![43, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-7, -31, 43]], ![![0, -1, 1], ![3, 8, -12], ![-8, 31, -28]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [10, 31, 1] where
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
 g := ![![[16, 13], [19, 16], [16], [26, 15], [1]], ![[0, 30], [39, 27], [16], [34, 28], [1]]]
 h' := ![![[12, 42], [25, 23], [16, 4], [41, 4], [33, 12], [0, 1]], ![[0, 1], [0, 20], [21, 39], [3, 39], [5, 31], [12, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38]]
 b := ![[], [15, 19]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [10, 31, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2032, 18, 63]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![37, -45, 63]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![12, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![12, 1, 0]] 
 ![![43, 0, 0], ![12, 1, 0], ![28, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![12, 1, 0], ![0, 12, 1], ![45, -35, 12]]]
  hmulB := by decide  
  f := ![![![169, 14, 0], ![-602, 0, 0]], ![![36, 3, 0], ![-128, 0, 0]], ![![100, 8, 0], ![-356, 1, 0]]]
  g := ![![![1, 0, 0], ![-12, 43, 0], ![-28, 0, 43]], ![![0, 1, 0], ![-4, 12, 1], ![3, -35, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![7, -12, 1]] ![![43, 0, 0], ![12, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![516, 43, 0]], ![![301, -516, 43], ![129, -172, 0]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![12, 1, 0]]], ![![![7, -12, 1]], ![![3, -4, 0]]]]
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


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [15, 44, 22, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 40, 28], [4, 6, 19], [0, 1]]
 g := ![![[8, 20, 4], [37, 9, 4], [44, 41, 37], [17, 25, 1], []], ![[32, 4, 1, 24], [24, 43, 36, 36], [5, 6, 17, 42], [7, 19, 39, 21], [32, 32]], ![[0, 25, 4, 46], [30, 2, 21, 10], [19, 14, 15, 20], [17, 26, 13, 38], [41, 32]]]
 h' := ![![[21, 40, 28], [9, 27, 2], [45, 11, 45], [27, 5, 15], [0, 0, 1], [0, 1]], ![[4, 6, 19], [28, 6, 16], [25, 10, 14], [17, 41, 42], [8, 27, 6], [21, 40, 28]], ![[0, 1], [0, 14, 29], [18, 26, 35], [39, 1, 37], [12, 20, 40], [4, 6, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30, 10], []]
 b := ![[], [1, 2, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [15, 44, 22, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-103823, 133151, -39668]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2209, 2833, -844]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![20, 1, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![20, 1, 0]] 
 ![![53, 0, 0], ![20, 1, 0], ![24, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![20, 1, 0], ![0, 20, 1], ![45, -35, 20]]]
  hmulB := by decide  
  f := ![![![121, 6, 0], ![-318, 0, 0]], ![![20, 1, 0], ![-52, 0, 0]], ![![48, 2, 0], ![-126, 1, 0]]]
  g := ![![![1, 0, 0], ![-20, 53, 0], ![-24, 0, 53]], ![![0, 1, 0], ![-8, 20, 1], ![5, -35, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N0 : Nat.card (O ⧸ I53N0) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N0)

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := prime_ideal_of_norm_prime hp53.out _ NI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-16, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-16, 1, 0]] 
 ![![53, 0, 0], ![37, 1, 0], ![9, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-16, 1, 0], ![0, -16, 1], ![45, -35, -16]]]
  hmulB := by decide  
  f := ![![![257, -16, 0], ![848, 0, 0]], ![![177, -11, 0], ![584, 0, 0]], ![![69, -4, 0], ![228, 1, 0]]]
  g := ![![![1, 0, 0], ![-37, 53, 0], ![-9, 0, 53]], ![![-1, 1, 0], ![11, -16, 1], ![28, -35, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1

def I53N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-4, 1, 0]] i)))

def SI53N2: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-4, 1, 0]] 
 ![![53, 0, 0], ![49, 1, 0], ![37, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-4, 1, 0], ![0, -4, 1], ![45, -35, -4]]]
  hmulB := by decide  
  f := ![![![169, -42, 0], ![2226, 0, 0]], ![![157, -39, 0], ![2068, 0, 0]], ![![121, -30, 0], ![1594, 1, 0]]]
  g := ![![![1, 0, 0], ![-49, 53, 0], ![-37, 0, 53]], ![![-1, 1, 0], ![3, -4, 1], ![36, -35, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N2 : Nat.card (O ⧸ I53N2) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N2)

lemma isPrimeI53N2 : Ideal.IsPrime I53N2 := prime_ideal_of_norm_prime hp53.out _ NI53N2
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![20, 1, 0]] ![![53, 0, 0], ![-16, 1, 0]]
  ![![53, 0, 0], ![-2, 4, 1]] where
 M := ![![![2809, 0, 0], ![-848, 53, 0]], ![![1060, 53, 0], ![-320, 4, 1]]]
 hmul := by decide  
 g := ![![![![53, 0, 0], ![0, 0, 0]], ![![-14, -3, -1], ![53, 0, 0]]], ![![![20, 1, 0], ![0, 0, 0]], ![![-6, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI53N1 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![-2, 4, 1]] ![![53, 0, 0], ![-4, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-212, 53, 0]], ![![-106, 212, 53], ![53, -53, 0]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-4, 1, 0]]], ![![![-2, 4, 1]], ![![1, -1, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![44, -3, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![44, -3, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![44, 56, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![44, -3, 1], ![45, 9, -3], ![-135, 150, 9]]]
  hmulB := by decide  
  f := ![![![-43, 3, -1], ![59, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-44, -56, 59]], ![![0, -1, 1], ![3, 3, -3], ![-9, -6, 9]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [47, 42, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [17, 58], [0, 1]]
 g := ![![[26, 26], [8, 5], [12], [51, 36], [17, 1]], ![[55, 33], [34, 54], [12], [14, 23], [34, 58]]]
 h' := ![![[17, 58], [37, 47], [38, 51], [22, 22], [27, 6], [0, 1]], ![[0, 1], [10, 12], [20, 8], [42, 37], [11, 53], [17, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [58, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [47, 42, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![137, -67, -76]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![59, 71, -76]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![3, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![3, 1, 0]] 
 ![![59, 0, 0], ![3, 1, 0], ![50, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![3, 1, 0], ![0, 3, 1], ![45, -35, 3]]]
  hmulB := by decide  
  f := ![![![55, 18, 0], ![-1062, 0, 0]], ![![-3, -1, 0], ![60, 0, 0]], ![![46, 15, 0], ![-888, 1, 0]]]
  g := ![![![1, 0, 0], ![-3, 59, 0], ![-50, 0, 59]], ![![0, 1, 0], ![-1, 3, 1], ![0, -35, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![44, -3, 1]] ![![59, 0, 0], ![3, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![177, 59, 0]], ![![2596, -177, 59], ![177, 0, 0]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![3, 1, 0]]], ![![![44, -3, 1]], ![![3, 0, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0]] 
 ![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [17, 56, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [32, 28, 20], [23, 32, 41], [0, 1]]
 g := ![![[34, 45, 22], [24, 12], [24, 53, 58], [52, 29, 36], [1]], ![[32, 2, 9, 25], [15, 41], [2, 10, 21, 45], [30, 58, 46, 5], [57, 48, 57, 9]], ![[16, 15, 58, 5], [11, 57], [1, 52, 24, 42], [39, 0, 54, 9], [55, 9, 24, 52]]]
 h' := ![![[32, 28, 20], [14, 46, 49], [19, 58, 45], [31, 56, 27], [44, 5, 55], [0, 1]], ![[23, 32, 41], [16, 19, 48], [37, 54, 38], [37, 16, 32], [18, 24, 30], [32, 28, 20]], ![[0, 1], [38, 57, 25], [15, 10, 39], [16, 50, 2], [8, 32, 37], [23, 32, 41]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34, 18], []]
 b := ![[], [22, 42, 54], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [17, 56, 6, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![236375, -134871, -31110]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3875, -2211, -510]
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


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [38, 66, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 64, 17], [56, 2, 50], [0, 1]]
 g := ![![[5, 0, 26], [6, 40, 23], [46, 37], [58, 1], [0, 1], []], ![[4, 22, 32, 26], [57, 65, 60, 29], [18, 62], [50, 6], [22, 4], [32, 21]], ![[61, 22, 19, 42], [55, 12, 53, 57], [22, 24], [46, 59], [33, 9], [66, 21]]]
 h' := ![![[11, 64, 17], [40, 0, 19], [43, 59, 31], [7, 20, 38], [0, 29, 1], [0, 0, 1], [0, 1]], ![[56, 2, 50], [5, 4, 38], [46, 27, 60], [23, 15, 14], [28, 19, 26], [44, 39, 2], [11, 64, 17]], ![[0, 1], [46, 63, 10], [35, 48, 43], [0, 32, 15], [41, 19, 40], [25, 28, 64], [56, 2, 50]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55, 4], []]
 b := ![[], [5, 60, 51], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [38, 66, 0, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-14204, 11457, 134]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-212, 171, 2]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![1, -26, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![1, -26, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![1, 45, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![1, -26, 1], ![45, -34, -26], ![-1170, 955, -34]]]
  hmulB := by decide  
  f := ![![![0, -6, 1], ![-19, 2, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-1, -45, 71]], ![![0, -1, 1], ![1, 16, -26], ![-16, 35, -34]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [57, 46, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 70], [0, 1]]
 g := ![![[17, 5], [66, 57], [70, 54], [25], [57], [1]], ![[0, 66], [0, 14], [0, 17], [25], [57], [1]]]
 h' := ![![[25, 70], [1, 17], [57, 46], [66, 57], [0, 66], [14, 25], [0, 1]], ![[0, 1], [0, 54], [0, 25], [0, 14], [17, 5], [0, 46], [25, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54]]
 b := ![[], [53, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [57, 46, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![237, 86, -47]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4, 31, -47]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![26, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![26, 1, 0]] 
 ![![71, 0, 0], ![26, 1, 0], ![34, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![26, 1, 0], ![0, 26, 1], ![45, -35, 26]]]
  hmulB := by decide  
  f := ![![![651, 25, 0], ![-1775, 0, 0]], ![![234, 9, 0], ![-638, 0, 0]], ![![270, 10, 0], ![-736, 1, 0]]]
  g := ![![![1, 0, 0], ![-26, 71, 0], ![-34, 0, 71]], ![![0, 1, 0], ![-10, 26, 1], ![1, -35, 26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![1, -26, 1]] ![![71, 0, 0], ![26, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![1846, 71, 0]], ![![71, -1846, 71], ![71, -710, 0]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![26, 1, 0]]], ![![![1, -26, 1]], ![![1, -10, 0]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0)
instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![17, 37, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![17, 37, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![17, 37, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![17, 37, 1], ![45, -18, 37], ![1665, -1250, -18]]]
  hmulB := by decide  
  f := ![![![-16, -37, -1], ![73, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-17, -37, 73]], ![![0, 0, 1], ![-8, -19, 37], ![27, -8, -18]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [58, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [51, 72], [0, 1]]
 g := ![![[18, 12], [50], [70], [52, 49], [46], [1]], ![[46, 61], [50], [70], [69, 24], [46], [1]]]
 h' := ![![[51, 72], [19, 42], [46, 14], [50, 17], [39, 7], [15, 51], [0, 1]], ![[0, 1], [44, 31], [30, 59], [41, 56], [31, 66], [61, 22], [51, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22]]
 b := ![[], [48, 11]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [58, 22, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1694, 1320, 12]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-26, 12, 12]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![36, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![36, 1, 0]] 
 ![![73, 0, 0], ![36, 1, 0], ![18, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![36, 1, 0], ![0, 36, 1], ![45, -35, 36]]]
  hmulB := by decide  
  f := ![![![541, 15, 0], ![-1095, 0, 0]], ![![252, 7, 0], ![-510, 0, 0]], ![![90, 2, 0], ![-182, 1, 0]]]
  g := ![![![1, 0, 0], ![-36, 73, 0], ![-18, 0, 73]], ![![0, 1, 0], ![-18, 36, 1], ![9, -35, 36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![17, 37, 1]] ![![73, 0, 0], ![36, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![2628, 73, 0]], ![![1241, 2701, 73], ![657, 1314, 73]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![36, 1, 0]]], ![![![17, 37, 1]], ![![9, 18, 1]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0)
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-37, 1, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-37, 1, 0]] 
 ![![79, 0, 0], ![42, 1, 0], ![53, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-37, 1, 0], ![0, -37, 1], ![45, -35, -37]]]
  hmulB := by decide  
  f := ![![![2332, -63, 0], ![4977, 0, 0]], ![![1222, -33, 0], ![2608, 0, 0]], ![![1572, -42, 0], ![3355, 1, 0]]]
  g := ![![![1, 0, 0], ![-42, 79, 0], ![-53, 0, 79]], ![![-1, 1, 0], ![19, -37, 1], ![44, -35, -37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N0 : Nat.card (O ⧸ I79N0) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N0)

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := prime_ideal_of_norm_prime hp79.out _ NI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-29, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-29, 1, 0]] 
 ![![79, 0, 0], ![50, 1, 0], ![28, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-29, 1, 0], ![0, -29, 1], ![45, -35, -29]]]
  hmulB := by decide  
  f := ![![![1277, -44, 0], ![3476, 0, 0]], ![![784, -27, 0], ![2134, 0, 0]], ![![446, -15, 0], ![1214, 1, 0]]]
  g := ![![![1, 0, 0], ![-50, 79, 0], ![-28, 0, 79]], ![![-1, 1, 0], ![18, -29, 1], ![33, -35, -29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1

def I79N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-13, 1, 0]] i)))

def SI79N2: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-13, 1, 0]] 
 ![![79, 0, 0], ![66, 1, 0], ![68, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-13, 1, 0], ![0, -13, 1], ![45, -35, -13]]]
  hmulB := by decide  
  f := ![![![976, -75, 0], ![5925, 0, 0]], ![![820, -63, 0], ![4978, 0, 0]], ![![848, -65, 0], ![5148, 1, 0]]]
  g := ![![![1, 0, 0], ![-66, 79, 0], ![-68, 0, 79]], ![![-1, 1, 0], ![10, -13, 1], ![41, -35, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N2 : Nat.card (O ⧸ I79N2) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N2)

lemma isPrimeI79N2 : Ideal.IsPrime I79N2 := prime_ideal_of_norm_prime hp79.out _ NI79N2
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-37, 1, 0]] ![![79, 0, 0], ![-29, 1, 0]]
  ![![79, 0, 0], ![46, 13, 1]] where
 M := ![![![6241, 0, 0], ![-2291, 79, 0]], ![![-2923, 79, 0], ![1073, -66, 1]]]
 hmul := by decide  
 g := ![![![![33, -13, -1], ![79, 0, 0]], ![![-29, 1, 0], ![0, 0, 0]]], ![![![-37, 1, 0], ![0, 0, 0]], ![![-33, -14, -1], ![80, 0, 0]]]]
 hle2 := by decide  

def MulI79N1 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![46, 13, 1]] ![![79, 0, 0], ![-13, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![-1027, 79, 0]], ![![3634, 1027, 79], ![-553, -158, 0]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![-13, 1, 0]]], ![![![46, 13, 1]], ![![-7, -2, 0]]]]
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


lemma PB135I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB135I1 : PrimesBelowBoundCertificateInterval O 31 79 135 where
  m := 11
  g := ![2, 2, 2, 1, 3, 2, 1, 1, 2, 2, 3]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB135I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0]
    · exact ![I53N0, I53N1, I53N2]
    · exact ![I59N0, I59N1]
    · exact ![I61N0]
    · exact ![I67N0]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1]
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
    · exact ![1369, 37]
    · exact ![1681, 41]
    · exact ![1849, 43]
    · exact ![103823]
    · exact ![53, 53, 53]
    · exact ![3481, 59]
    · exact ![226981]
    · exact ![300763]
    · exact ![5041, 71]
    · exact ![5329, 73]
    · exact ![79, 79, 79]
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
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
      exact NI79N2
  β := ![I37N1, I41N1, I43N1, I53N0, I53N1, I53N2, I59N1, I71N1, I73N1, I79N0, I79N1, I79N2]
  Il := ![[I37N1], [I41N1], [I43N1], [], [I53N0, I53N1, I53N2], [I59N1], [], [], [I71N1], [I73N1], [I79N0, I79N1, I79N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
