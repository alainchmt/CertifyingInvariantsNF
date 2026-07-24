
import IdealArithmetic.Examples.NF3_1_853335_2.RI3_1_853335_2
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [11, 18, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 31, 4], [29, 5, 33], [0, 1]]
 g := ![![[30, 15, 3], [27, 4], [11, 10, 12], [32, 1], []], ![[35, 13, 10, 26], [36, 30], [19, 25, 16, 1], [1, 25], [20, 16]], ![[32, 33, 22, 28], [11, 3], [27, 24, 25, 16], [23, 36], [28, 16]]]
 h' := ![![[3, 31, 4], [25, 1, 15], [27, 16, 35], [18, 5, 7], [0, 0, 1], [0, 1]], ![[29, 5, 33], [8, 35, 5], [16, 12, 17], [36, 36, 18], [11, 20, 5], [3, 31, 4]], ![[0, 1], [20, 1, 17], [17, 9, 22], [9, 33, 12], [15, 17, 31], [29, 5, 33]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23, 32], []]
 b := ![[], [27, 5, 29], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [11, 18, 5, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-18056, -2960, -1369]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-488, -80, -37]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0]] 
 ![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [18, 21, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 1, 33], [30, 39, 8], [0, 1]]
 g := ![![[29, 6, 31], [34, 2], [32, 37], [20, 0, 1], []], ![[1, 24, 36, 21], [16, 1], [9, 8], [28, 10, 16, 9], [25, 23]], ![[13, 5, 24, 40], [22, 10], [5, 10], [23, 3, 33, 8], [9, 23]]]
 h' := ![![[11, 1, 33], [12, 35, 20], [38, 40, 24], [9, 31, 23], [0, 0, 1], [0, 1]], ![[30, 39, 8], [8, 22, 8], [3, 8, 1], [40, 14, 34], [40, 26, 39], [11, 1, 33]], ![[0, 1], [37, 25, 13], [8, 34, 16], [37, 37, 25], [0, 15, 1], [30, 39, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 36], []]
 b := ![[], [11, 6, 25], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [18, 21, 0, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-75317, 15129, 5658]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1837, 369, 138]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 68921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def PBC41 : ContainsPrimesAboveP 41 ![I41N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![41, 0, 0]]) timesTableT_eq_Table B_one_repr 41 (by decide) 𝕀


def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![14, 1, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![14, 1, 0]] 
 ![![43, 0, 0], ![14, 1, 0], ![15, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![14, 1, 0], ![0, 14, 7], ![203, 21, 14]]]
  hmulB := by decide  
  f := ![![![253, 18, 0], ![-774, 0, 0]], ![![70, 5, 0], ![-214, 0, 0]], ![![85, -6, -6], ![-260, 37, 0]]]
  g := ![![![1, 0, 0], ![-14, 43, 0], ![-15, 0, 43]], ![![0, 1, 0], ![-7, 14, 7], ![-7, 21, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N0)

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := prime_ideal_of_norm_prime hp43.out _ NI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-7, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-7, 1, 0]] 
 ![![43, 0, 0], ![36, 1, 0], ![36, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-7, 1, 0], ![0, -7, 7], ![203, 21, -7]]]
  hmulB := by decide  
  f := ![![![274, -39, 0], ![1677, 0, 0]], ![![232, -33, 0], ![1420, 0, 0]], ![![232, -27, -6], ![1420, 37, 0]]]
  g := ![![![1, 0, 0], ![-36, 43, 0], ![-36, 0, 43]], ![![-1, 1, 0], ![0, -7, 7], ![-7, 21, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![14, 1, 0]] ![![43, 0, 0], ![-7, 1, 0]]
  ![![43, 0, 0], ![-14, 1, 1]] where
 M := ![![![1849, 0, 0], ![-301, 43, 0]], ![![602, 43, 0], ![-98, 7, 7]]]
 hmul := by decide  
 g := ![![![![43, 0, 0], ![0, 0, 0]], ![![7, 0, -1], ![43, 0, 0]]], ![![![14, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![7, 0, 0]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-14, 1, 1]] ![![43, 0, 0], ![-7, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-301, 43, 0]], ![![-602, 43, 43], ![301, 0, 0]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-7, 1, 0]]], ![![![-14, 1, 1]], ![![7, 0, 0]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1, I43N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
    exact isPrimeI43N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0 ⊙ MulI43N1)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-34, -5, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-34, -5, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![13, 42, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-34, -5, 1], ![203, -13, -35], ![-1015, -76, -13]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-13, -42, 47]], ![![-1, -1, 1], ![14, 31, -35], ![-18, 10, -13]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [11, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 46], [0, 1]]
 g := ![![[22, 12], [31, 37], [8, 3], [46, 2], [1]], ![[32, 35], [7, 10], [34, 44], [32, 45], [1]]]
 h' := ![![[40, 46], [35, 23], [6, 32], [11, 12], [36, 40], [0, 1]], ![[0, 1], [15, 24], [17, 15], [21, 35], [38, 7], [40, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [8, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [11, 7, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3253, -134, 149]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![28, -136, 149]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-12, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-12, 1, 0]] 
 ![![47, 0, 0], ![35, 1, 0], ![13, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-12, 1, 0], ![0, -12, 7], ![203, 21, -12]]]
  hmulB := by decide  
  f := ![![![73, -6, 0], ![282, 0, 0]], ![![61, -5, 0], ![236, 0, 0]], ![![35, 4, -4], ![136, 27, 0]]]
  g := ![![![1, 0, 0], ![-35, 47, 0], ![-13, 0, 47]], ![![-1, 1, 0], ![7, -12, 7], ![-8, 21, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![-34, -5, 1]] ![![47, 0, 0], ![-12, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![-564, 47, 0]], ![![-1598, -235, 47], ![611, 47, -47]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![-12, 1, 0]]], ![![![-34, -5, 1]], ![![13, 1, -1]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![3, -8, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![3, -8, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![3, 45, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![3, -8, 1], ![203, 24, -56], ![-1624, -139, 24]]]
  hmulB := by decide  
  f := ![![![-2, 8, -1], ![53, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-3, -45, 53]], ![![0, -1, 1], ![7, 48, -56], ![-32, -23, 24]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [25, 49, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 52], [0, 1]]
 g := ![![[38, 17], [28], [52, 16], [28], [4, 1]], ![[0, 36], [28], [10, 37], [28], [8, 52]]]
 h' := ![![[4, 52], [31, 32], [25, 9], [25, 4], [6, 44], [0, 1]], ![[0, 1], [0, 21], [8, 44], [41, 49], [23, 9], [4, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48]]
 b := ![[], [5, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [25, 49, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1143, 186, 43]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-24, -33, 43]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![3, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![3, 1, 0]] 
 ![![53, 0, 0], ![3, 1, 0], ![29, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![3, 1, 0], ![0, 3, 7], ![203, 21, 3]]]
  hmulB := by decide  
  f := ![![![49, 16, 0], ![-848, 0, 0]], ![![-3, -1, 0], ![54, 0, 0]], ![![25, 6, -5], ![-432, 38, 0]]]
  g := ![![![1, 0, 0], ![-3, 53, 0], ![-29, 0, 53]], ![![0, 1, 0], ![-4, 3, 7], ![1, 21, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![3, -8, 1]] ![![53, 0, 0], ![3, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![159, 53, 0]], ![![159, -424, 53], ![212, 0, -53]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![3, 1, 0]]], ![![![3, -8, 1]], ![![4, 0, -1]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![17, 1, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![17, 1, 0]] 
 ![![59, 0, 0], ![17, 1, 0], ![43, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![17, 1, 0], ![0, 17, 7], ![203, 21, 17]]]
  hmulB := by decide  
  f := ![![![86, 5, 0], ![-295, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![50, -2, -2], ![-171, 17, 0]]]
  g := ![![![1, 0, 0], ![-17, 59, 0], ![-43, 0, 59]], ![![0, 1, 0], ![-10, 17, 7], ![-15, 21, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N0 : Nat.card (O ⧸ I59N0) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N0)

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := prime_ideal_of_norm_prime hp59.out _ NI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![19, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![19, 1, 0]] 
 ![![59, 0, 0], ![19, 1, 0], ![58, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![19, 1, 0], ![0, 19, 7], ![203, 21, 19]]]
  hmulB := by decide  
  f := ![![![381, 20, 0], ![-1180, 0, 0]], ![![95, 5, 0], ![-294, 0, 0]], ![![352, 13, -2], ![-1090, 17, 0]]]
  g := ![![![1, 0, 0], ![-19, 59, 0], ![-58, 0, 59]], ![![0, 1, 0], ![-13, 19, 7], ![-22, 21, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![23, 1, 0]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![59, 0, 0], ![23, 1, 0]] 
 ![![59, 0, 0], ![23, 1, 0], ![34, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![23, 1, 0], ![0, 23, 7], ![203, 21, 23]]]
  hmulB := by decide  
  f := ![![![323, 14, 0], ![-826, 0, 0]], ![![115, 5, 0], ![-294, 0, 0]], ![![176, 1, -2], ![-450, 17, 0]]]
  g := ![![![1, 0, 0], ![-23, 59, 0], ![-34, 0, 59]], ![![0, 1, 0], ![-13, 23, 7], ![-18, 21, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![17, 1, 0]] ![![59, 0, 0], ![19, 1, 0]]
  ![![59, 0, 0], ![4, 22, 1]] where
 M := ![![![3481, 0, 0], ![1121, 59, 0]], ![![1003, 59, 0], ![323, 36, 7]]]
 hmul := by decide  
 g := ![![![![55, -22, -1], ![59, 0, 0]], ![![15, -21, -1], ![59, 0, 0]]], ![![![13, -21, -1], ![59, 0, 0]], ![![5, -2, 0], ![7, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![4, 22, 1]] ![![59, 0, 0], ![23, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![1357, 59, 0]], ![![236, 1298, 59], ![295, 531, 177]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![23, 1, 0]]], ![![![4, 22, 1]], ![![5, 9, 3]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![2, -16, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![2, -16, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![2, 45, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![2, -16, 1], ![203, 23, -112], ![-3248, -307, 23]]]
  hmulB := by decide  
  f := ![![![-1, 16, -1], ![61, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-2, -45, 61]], ![![0, -1, 1], ![7, 83, -112], ![-54, -22, 23]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [59, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [52, 60], [0, 1]]
 g := ![![[26, 4], [47], [7, 45], [37, 57], [52, 1]], ![[51, 57], [47], [29, 16], [12, 4], [43, 60]]]
 h' := ![![[52, 60], [46, 2], [14, 13], [13, 44], [43, 22], [0, 1]], ![[0, 1], [28, 59], [19, 48], [44, 17], [28, 39], [52, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [28, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [59, 9, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![465, 62, 19]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![7, -13, 19]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-10, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-10, 1, 0]] 
 ![![61, 0, 0], ![51, 1, 0], ![38, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-10, 1, 0], ![0, -10, 7], ![203, 21, -10]]]
  hmulB := by decide  
  f := ![![![571, -57, 0], ![3477, 0, 0]], ![![481, -48, 0], ![2929, 0, 0]], ![![358, -30, -4], ![2180, 35, 0]]]
  g := ![![![1, 0, 0], ![-51, 61, 0], ![-38, 0, 61]], ![![-1, 1, 0], ![4, -10, 7], ![-8, 21, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![2, -16, 1]] ![![61, 0, 0], ![-10, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-610, 61, 0]], ![![122, -976, 61], ![183, 183, -122]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-10, 1, 0]]], ![![![2, -16, 1]], ![![3, 3, -2]]]]
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
instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-43, 4, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-43, 4, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![24, 4, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-43, 4, 1], ![203, -22, 28], ![812, 113, -22]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-24, -4, 67]], ![![-1, 0, 1], ![-7, -2, 28], ![20, 3, -22]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [17, 64, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 66], [0, 1]]
 g := ![![[55, 4], [43, 9], [6], [64], [9], [1]], ![[0, 63], [3, 58], [6], [64], [9], [1]]]
 h' := ![![[3, 66], [6, 65], [42, 64], [55, 26], [2, 59], [50, 3], [0, 1]], ![[0, 1], [0, 2], [33, 3], [66, 41], [45, 8], [59, 64], [3, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [59, 50]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [17, 64, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7796, 2081, 2614]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-820, -125, 2614]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-28, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-28, 1, 0]] 
 ![![67, 0, 0], ![39, 1, 0], ![22, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-28, 1, 0], ![0, -28, 7], ![203, 21, -28]]]
  hmulB := by decide  
  f := ![![![561, -20, 0], ![1340, 0, 0]], ![![365, -13, 0], ![872, 0, 0]], ![![226, 12, -5], ![540, 48, 0]]]
  g := ![![![1, 0, 0], ![-39, 67, 0], ![-22, 0, 67]], ![![-1, 1, 0], ![14, -28, 7], ![0, 21, -28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![-43, 4, 1]] ![![67, 0, 0], ![-28, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-1876, 67, 0]], ![![-2881, 268, 67], ![1407, -134, 0]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-28, 1, 0]]], ![![![-43, 4, 1]], ![![21, -2, 0]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-52, 10, -3]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-52, 10, -3]] 
 ![![71, 0, 0], ![0, 71, 0], ![41, 44, 1]] where
  M :=![![![-52, 10, -3], ![-609, -115, 70], ![2030, 123, -115]]]
  hmulB := by decide  
  f := ![![![65, 11, 5]], ![![1015, 170, 77]], ![![698, 117, 53]]]
  g := ![![![1, 2, -3], ![-49, -45, 70], ![95, 73, -115]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [27, 54, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 70], [0, 1]]
 g := ![![[2, 50], [22, 25], [44, 57], [6], [5], [1]], ![[0, 21], [21, 46], [19, 14], [6], [5], [1]]]
 h' := ![![[17, 70], [45, 60], [19, 66], [17, 25], [26, 19], [44, 17], [0, 1]], ![[0, 1], [0, 11], [5, 5], [16, 46], [65, 52], [49, 54], [17, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [15, 40]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [27, 54, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1244, 59, 32]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-36, -19, 32]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-65, -11, -5]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![-65, -11, -5]] 
 ![![71, 0, 0], ![47, 1, 0], ![9, 0, 1]] where
  M :=![![![-65, -11, -5], ![-1015, -170, -77], ![-2233, -376, -170]]]
  hmulB := by decide  
  f := ![![![52, -10, 3]], ![![43, -5, 1]], ![![-22, -3, 2]]]
  g := ![![![7, -11, -5], ![108, -170, -77], ![239, -376, -170]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-52, 10, -3]] ![![-65, -11, -5]]
  ![![71, 0, 0]] where
 M := ![![![-71, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0]] 
 ![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [71, 34, 62, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 26, 65], [10, 46, 8], [0, 1]]
 g := ![![[37, 40, 4], [6, 2], [22, 36], [12, 62, 50], [11, 1], []], ![[1, 61, 48, 8], [45, 50], [70, 27], [41, 32, 16, 27], [7, 72], [69, 64]], ![[26, 51, 17, 12], [17, 72], [62, 16], [3, 7, 30, 4], [56, 19], [53, 64]]]
 h' := ![![[1, 26, 65], [67, 1, 71], [36, 18, 32], [24, 54, 6], [22, 66, 14], [0, 0, 1], [0, 1]], ![[10, 46, 8], [9, 51, 46], [49, 68, 14], [36, 15, 63], [63, 8, 43], [66, 24, 46], [1, 26, 65]], ![[0, 1], [30, 21, 29], [19, 60, 27], [48, 4, 4], [62, 72, 16], [60, 49, 26], [10, 46, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 8], []]
 b := ![[], [9, 20, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [71, 34, 62, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![150088, 28835, 12556]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2056, 395, 172]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 389017 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def PBC73 : ContainsPrimesAboveP 73 ![I73N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![73, 0, 0]]) timesTableT_eq_Table B_one_repr 73 (by decide) 𝕀

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


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [39, 66, 68, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [48, 15, 63], [42, 63, 16], [0, 1]]
 g := ![![[17, 12, 40], [10, 31, 10], [3, 70, 10], [39, 1, 23], [11, 1], []], ![[21, 56, 22, 61], [19, 49, 78, 41], [72, 14, 70, 41], [26, 9, 61, 12], [43, 19], [45, 19]], ![[56, 33, 55, 2], [62, 19, 61, 55], [66, 15, 66, 25], [9, 70, 56, 4], [58, 67], [13, 19]]]
 h' := ![![[48, 15, 63], [5, 49, 44], [41, 0, 57], [59, 44, 57], [45, 25, 55], [0, 0, 1], [0, 1]], ![[42, 63, 16], [48, 35, 13], [50, 34, 36], [47, 62, 43], [77, 53, 63], [75, 20, 63], [48, 15, 63]], ![[0, 1], [17, 74, 22], [37, 45, 65], [7, 52, 58], [78, 1, 40], [72, 59, 15], [42, 63, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60, 46], []]
 b := ![[], [78, 45, 72], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [39, 66, 68, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2485893, -125452, 126084]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-31467, -1588, 1596]
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



lemma PB262I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB262I1 : PrimesBelowBoundCertificateInterval O 31 79 262 where
  m := 11
  g := ![1, 1, 3, 2, 2, 3, 2, 2, 2, 1, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB262I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0]
    · exact ![I43N0, I43N1, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1, I59N2]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1]
    · exact ![I73N0]
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
    · exact ![50653]
    · exact ![68921]
    · exact ![43, 43, 43]
    · exact ![2209, 47]
    · exact ![2809, 53]
    · exact ![59, 59, 59]
    · exact ![3721, 61]
    · exact ![4489, 67]
    · exact ![5041, 71]
    · exact ![389017]
    · exact ![493039]
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
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
  β := ![I43N0, I43N1, I47N1, I53N1, I59N0, I59N1, I59N2, I61N1, I67N1, I71N1]
  Il := ![[], [], [I43N0, I43N1, I43N1], [I47N1], [I53N1], [I59N0, I59N1, I59N2], [I61N1], [I67N1], [I71N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
