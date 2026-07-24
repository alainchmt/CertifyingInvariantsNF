
import IdealArithmetic.Examples.NF3_1_730732_1.RI3_1_730732_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![39, 1, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![39, 1, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![2, 1, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![39, 1, 1], ![-105, 3, 3], ![-177, -107, 4]]]
  hmulB := by decide  
  f := ![![![-38, -1, -1], ![37, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![-1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-2, -1, 37]], ![![1, 0, 1], ![-3, 0, 3], ![-5, -3, 4]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [6, 33, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 36], [0, 1]]
 g := ![![[24, 12], [9], [29, 34], [16], [1]], ![[35, 25], [9], [17, 3], [16], [1]]]
 h' := ![![[4, 36], [30, 7], [11, 34], [14, 16], [31, 4], [0, 1]], ![[0, 1], [21, 30], [36, 3], [4, 21], [10, 33], [4, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [18, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [6, 33, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-733, -459, -200]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-9, -7, -200]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-3, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-3, 1, 0]] 
 ![![37, 0, 0], ![34, 1, 0], ![33, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-3, 1, 0], ![1, -3, 2], ![-106, -36, -2]]]
  hmulB := by decide  
  f := ![![![-56, 179, -120], ![37, 2220, 0]], ![![-51, 164, -110], ![38, 2035, 0]], ![![-51, 160, -107], ![20, 1980, 0]]]
  g := ![![![1, 0, 0], ![-34, 37, 0], ![-33, 0, 37]], ![![-1, 1, 0], ![1, -3, 2], ![32, -36, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![39, 1, 1]] ![![37, 0, 0], ![-3, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-111, 37, 0]], ![![1443, 37, 37], ![-222, 0, 0]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-3, 1, 0]]], ![![![39, 1, 1]], ![![-6, 0, 0]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![18, 7, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![18, 7, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![18, 7, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![18, 7, 1], ![-99, -18, 15], ![-813, -323, -11]]]
  hmulB := by decide  
  f := ![![![-17, -7, -1], ![41, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-18, -7, 41]], ![![0, 0, 1], ![-9, -3, 15], ![-15, -6, -11]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [30, 27, 1] where
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
 g := ![![[5, 39], [36], [5], [18, 32], [1]], ![[18, 2], [36], [5], [15, 9], [1]]]
 h' := ![![[14, 40], [19, 30], [22, 6], [34, 28], [11, 14], [0, 1]], ![[0, 1], [29, 11], [24, 35], [16, 13], [2, 27], [14, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [25, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [30, 27, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![437, -1117, -757]
  a := ![2, -2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![343, 102, -757]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-15, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-15, 1, 0]] 
 ![![41, 0, 0], ![26, 1, 0], ![11, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-15, 1, 0], ![1, -15, 2], ![-106, -36, -14]]]
  hmulB := by decide  
  f := ![![![241, -4496, 600], ![-164, -12300, 0]], ![![146, -2847, 380], ![-122, -7790, 0]], ![![76, -1207, 161], ![-13, -3300, 0]]]
  g := ![![![1, 0, 0], ![-26, 41, 0], ![-11, 0, 41]], ![![-1, 1, 0], ![9, -15, 2], ![24, -36, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![18, 7, 1]] ![![41, 0, 0], ![-15, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-615, 41, 0]], ![![738, 287, 41], ![-369, -123, 0]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-15, 1, 0]]], ![![![18, 7, 1]], ![![-9, -3, 0]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0]] 
 ![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [9, 12, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 20, 20], [12, 22, 23], [0, 1]]
 g := ![![[30, 5, 21], [1, 34, 23], [31, 38], [31, 0, 1], []], ![[30, 16, 23, 5], [38, 38, 42, 19], [19, 41], [40, 27, 14, 5], [26, 13]], ![[32, 34, 27, 36], [24, 39, 13, 38], [6, 6], [37, 14, 1, 41], [23, 13]]]
 h' := ![![[31, 20, 20], [34, 40, 35], [33, 32, 18], [22, 15, 34], [0, 0, 1], [0, 1]], ![[12, 22, 23], [16, 31, 22], [7, 16, 4], [7, 10, 16], [39, 37, 22], [31, 20, 20]], ![[0, 1], [29, 15, 29], [14, 38, 21], [38, 18, 36], [23, 6, 20], [12, 22, 23]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41, 7], []]
 b := ![[], [2, 10, 19], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [9, 12, 0, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2792262319, -1394248340, -304315300]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-64936333, -32424380, -7077100]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 79507 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def PBC43 : ContainsPrimesAboveP 43 ![I43N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![43, 0, 0]]) timesTableT_eq_Table B_one_repr 43 (by decide) 𝕀

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


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [36, 13, 21, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 39, 21], [33, 7, 26], [0, 1]]
 g := ![![[25, 23, 8], [42, 24, 8], [6, 8, 34], [5, 26, 1], []], ![[1, 33, 35, 36], [34, 30, 2, 42], [30, 20, 32, 14], [5, 34, 43, 42], [38, 18]], ![[39, 17, 36, 22], [45, 31, 21, 45], [31, 9, 7, 15], [16, 44, 21, 19], [33, 18]]]
 h' := ![![[40, 39, 21], [39, 32, 14], [19, 27, 14], [8, 33, 38], [0, 0, 1], [0, 1]], ![[33, 7, 26], [8, 35, 18], [23, 28, 7], [39, 29, 19], [44, 4, 7], [40, 39, 21]], ![[0, 1], [38, 27, 15], [41, 39, 26], [14, 32, 37], [42, 43, 39], [33, 7, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25, 38], []]
 b := ![[], [21, 0, 34], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [36, 13, 21, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-988081, -566350, -169858]
  a := ![-2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-21023, -12050, -3614]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10829923, 483230, -265368]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-10829923, 483230, -265368]] 
 ![![53, 0, 0], ![0, 53, 0], ![50, 45, 1]] where
  M :=![![![-10829923, 483230, -265368], ![28612238, -1276675, 701092], ![-32381252, 1444848, -793445]]]
  hmulB := by decide  
  f := ![![![-403, -62, 80]], ![![-8542, -3283, -44]], ![![-7616, -2911, -25]]]
  g := ![![![46009, 234430, -265368], ![-121554, -619355, 701092], ![137566, 700941, -793445]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [36, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [32, 52], [0, 1]]
 g := ![![[5, 28], [52], [39, 16], [43], [32, 1]], ![[0, 25], [52], [21, 37], [43], [11, 52]]]
 h' := ![![[32, 52], [23, 44], [27, 23], [26, 49], [14, 34], [0, 1]], ![[0, 1], [0, 9], [21, 30], [4, 4], [42, 19], [32, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [1, 43]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [36, 21, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-691, -447, -176]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![153, 141, -176]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![403, 62, -80]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![403, 62, -80]] 
 ![![53, 0, 0], ![15, 1, 0], ![47, 0, 1]] where
  M :=![![![403, 62, -80], ![8542, 3283, 44], ![-892, 3448, 3345]]]
  hmulB := by decide  
  f := ![![![10829923, -483230, 265368]], ![![2525219, -112675, 61876]], ![![10214861, -455786, 250297]]]
  g := ![![![61, 62, -80], ![-807, 3283, 44], ![-3959, 3448, 3345]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-10829923, 483230, -265368]] ![![403, 62, -80]]
  ![![53, 0, 0]] where
 M := ![![![-53, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-78, 3, -2]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-78, 3, -2]] 
 ![![59, 0, 0], ![0, 59, 0], ![39, 28, 1]] where
  M :=![![![-78, 3, -2], ![215, -6, 4], ![-176, 34, -3]]]
  hmulB := by decide  
  f := ![![![2, 1, 0]], ![![1, 2, 2]], ![![0, 1, 1]]]
  g := ![![![0, 1, -2], ![1, -2, 4], ![-1, 2, -3]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [13, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [47, 58], [0, 1]]
 g := ![![[10, 9], [0, 5], [19], [22, 51], [47, 1]], ![[20, 50], [58, 54], [19], [0, 8], [35, 58]]]
 h' := ![![[47, 58], [0, 56], [11, 51], [9, 45], [38, 13], [0, 1]], ![[0, 1], [36, 3], [48, 8], [0, 14], [0, 46], [47, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41]]
 b := ![[], [5, 50]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [13, 12, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-12321, -4439, 560]
  a := ![2, 19, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-579, -341, 560]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![2, 1, 0]] 
 ![![59, 0, 0], ![2, 1, 0], ![28, 0, 1]] where
  M :=![![![2, 1, 0], ![1, 2, 2], ![-106, -36, 3]]]
  hmulB := by decide  
  f := ![![![-78, 3, -2]], ![![1, 0, 0]], ![![-40, 2, -1]]]
  g := ![![![0, 1, 0], ![-1, 2, 2], ![-2, -36, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-78, 3, -2]] ![![2, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![59, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-72043005, -30017992, -2429237]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![-72043005, -30017992, -2429237]] 
 ![![61, 0, 0], ![14, 1, 0], ![55, 0, 1]] where
  M :=![![![-72043005, -30017992, -2429237], ![227481130, 15409527, -62465221], ![3354382979, 1253123539, -14608465]]]
  hmulB := by decide  
  f := ![![![-78051529268091064, 3482650852012023, -1912513897397131]], ![![-14532988291428967, 648460376497934, -356105028802179]], ![![-74200108415460437, 3310800867269258, -1818141679780730]]]
  g := ![![![7898638, -30017992, -2429237], ![56513687, 15409527, -62465221], ![-219440672, 1253123539, -14608465]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N0 : Nat.card (O ⧸ I61N0) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N0)

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := prime_ideal_of_norm_prime hp61.out _ NI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![21, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![21, 1, 0]] 
 ![![61, 0, 0], ![21, 1, 0], ![24, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![21, 1, 0], ![1, 21, 2], ![-106, -36, 22]]]
  hmulB := by decide  
  f := ![![![-1263, -33584, -3200], ![-976, 97600, 0]], ![![-445, -11545, -1100], ![-304, 33550, 0]], ![![-510, -13214, -1259], ![-346, 38400, 0]]]
  g := ![![![1, 0, 0], ![-21, 61, 0], ![-24, 0, 61]], ![![0, 1, 0], ![-8, 21, 2], ![2, -36, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![25, 1, 0]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![61, 0, 0], ![25, 1, 0]] 
 ![![61, 0, 0], ![25, 1, 0], ![54, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![25, 1, 0], ![1, 25, 2], ![-106, -36, 26]]]
  hmulB := by decide  
  f := ![![![628, 22539, 1804], ![671, -55022, 0]], ![![244, 9220, 738], ![306, -22509, 0]], ![![567, 19953, 1597], ![567, -48708, 0]]]
  g := ![![![1, 0, 0], ![-25, 61, 0], ![-54, 0, 61]], ![![0, 1, 0], ![-12, 25, 2], ![-10, -36, 26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![-72043005, -30017992, -2429237]] ![![61, 0, 0], ![21, 1, 0]]
  ![![61, 0, 0], ![-5, -13, 1]] where
 M := ![![![-4394623305, -1831097512, -148183457], ![-1285421975, -614968305, -113479198]]]
 hmul := by decide  
 g := ![![![![-71087920, -27534771, -2620254], ![11652037, 0, 0]], ![![-20773000, -9302770, -1920213], ![3653795, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-5, -13, 1]] ![![61, 0, 0], ![25, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![1525, 61, 0]], ![![-305, -793, 61], ![-244, -366, 0]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![25, 1, 0]]], ![![![-5, -13, 1]], ![![-4, -6, 0]]]]
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


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [54, 17, 55, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [44, 16, 13], [35, 50, 54], [0, 1]]
 g := ![![[24, 7, 56], [17, 51, 39], [35, 65], [46, 49], [12, 1], []], ![[43, 30, 60, 63], [46, 27, 65, 11], [5, 39], [36, 26], [28, 21], [32, 35]], ![[59, 29, 0, 1], [32, 0, 43, 26], [28, 1], [3, 6], [59, 55], [58, 35]]]
 h' := ![![[44, 16, 13], [20, 65, 49], [19, 53, 46], [10, 27, 47], [22, 10, 60], [0, 0, 1], [0, 1]], ![[35, 50, 54], [7, 11, 12], [60, 16, 41], [53, 48, 21], [11, 39, 48], [7, 46, 50], [44, 16, 13]], ![[0, 1], [39, 58, 6], [46, 65, 47], [34, 59, 66], [53, 18, 26], [36, 21, 16], [35, 50, 54]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40, 62], []]
 b := ![[], [56, 66, 21], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [54, 17, 55, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![99763, -29346, -55074]
  a := ![-2, 3, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1489, -438, -822]
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


def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![0, 1, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![0, 1, 0]] 
 ![![71, 0, 0], ![0, 1, 0], ![36, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![0, 1, 0], ![1, 0, 2], ![-106, -36, 1]]]
  hmulB := by decide  
  f := ![![![0, 0, -2], ![0, 71, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, -1], ![0, 36, 0]]]
  g := ![![![1, 0, 0], ![0, 71, 0], ![-36, 0, 71]], ![![0, 1, 0], ![-1, 0, 2], ![-2, -36, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N0 : Nat.card (O ⧸ I71N0) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N0)

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := prime_ideal_of_norm_prime hp71.out _ NI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59803, 45774, 20445]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![59803, 45774, 20445]] 
 ![![71, 0, 0], ![70, 1, 0], ![0, 0, 1]] where
  M :=![![![59803, 45774, 20445], ![-2121396, -676217, 111993], ![-6303639, -3099459, -630443]]]
  hmulB := by decide  
  f := ![![![-773433985918, 34510541373, -18951624147]], ![![-733760511455, 32740315204, -17979496221]], ![![-32571155931, 1453321479, -798098243]]]
  g := ![![![-44287, 45774, 20445], ![636814, -676217, 111993], ![2967021, -3099459, -630443]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![0, 1, 0]] ![![71, 0, 0], ![0, 1, 0]]
  ![![773433985918, -34510541373, 18951624147]] where
 M := ![![![5041, 0, 0], ![0, 71, 0]], ![![0, 71, 0], ![1, 0, 2]]]
 hmul := by decide  
 g := ![![![![-4246013, -3249954, -1451595]], ![![2121396, 676217, -111993]]], ![![![2121396, 676217, -111993]], ![![176725, 86664, 17471]]]]
 hle2 := by decide  
def MulI71N1 : IdealMulLeCertificate' Table 
  ![![773433985918, -34510541373, 18951624147]] ![![59803, 45774, 20445]]
  ![![71, 0, 0]] where
 M := ![![![-71, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![235186, 107109, 15984]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![235186, 107109, 15984]] 
 ![![73, 0, 0], ![5, 1, 0], ![61, 0, 1]] where
  M :=![![![235186, 107109, 15984], ![-1587195, -340238, 230202], ![-12488418, -4990788, -233129]]]
  hmulB := by decide  
  f := ![![![1228208723878, -54802541331, 30095070210]], ![![39673474463, -1770226169, 972127926]], ![![1076617144558, -48038541345, 26380588189]]]
  g := ![![![-17471, 107109, 15984], ![-190799, -340238, 230202], ![365567, -4990788, -233129]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N0 : Nat.card (O ⧸ I73N0) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N0)

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := prime_ideal_of_norm_prime hp73.out _ NI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![25, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![25, 1, 0]] 
 ![![73, 0, 0], ![25, 1, 0], ![53, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![25, 1, 0], ![1, 25, 2], ![-106, -36, 26]]]
  hmulB := by decide  
  f := ![![![-1359, -42736, -3420], ![-1022, 124830, 0]], ![![-485, -14621, -1170], ![-291, 42705, 0]], ![![-999, -31028, -2483], ![-706, 90630, 0]]]
  g := ![![![1, 0, 0], ![-25, 73, 0], ![-53, 0, 73]], ![![0, 1, 0], ![-10, 25, 2], ![-8, -36, 26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1

def I73N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-31, 1, 0]] i)))

def SI73N2: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-31, 1, 0]] 
 ![![73, 0, 0], ![42, 1, 0], ![31, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-31, 1, 0], ![1, -31, 2], ![-106, -36, -30]]]
  hmulB := by decide  
  f := ![![![-974, 44625, -2880], ![1095, 105120, 0]], ![![-548, 25659, -1656], ![658, 60444, 0]], ![![-403, 18950, -1223], ![490, 44640, 0]]]
  g := ![![![1, 0, 0], ![-42, 73, 0], ![-31, 0, 73]], ![![-1, 1, 0], ![17, -31, 2], ![32, -36, -30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N2 : Nat.card (O ⧸ I73N2) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N2)

lemma isPrimeI73N2 : Ideal.IsPrime I73N2 := prime_ideal_of_norm_prime hp73.out _ NI73N2
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![235186, 107109, 15984]] ![![73, 0, 0], ![25, 1, 0]]
  ![![73, 0, 0], ![-10, 15, 1]] where
 M := ![![![17168578, 7818957, 1166832], ![4292455, 2337487, 629802]]]
 hmul := by decide  
 g := ![![![![233906, 109029, 16112], ![-9344, 0, 0]], ![![58635, 32269, 8644], ![-1210, 0, 0]]]]
 hle2 := by decide  

def MulI73N1 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-10, 15, 1]] ![![73, 0, 0], ![-31, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-2263, 73, 0]], ![![-730, 1095, 73], ![219, -511, 0]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-31, 1, 0]]], ![![![-10, 15, 1]], ![![3, -7, 0]]]]
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


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [38, 54, 44, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [35, 19, 5], [0, 59, 74], [0, 1]]
 g := ![![[76, 28, 22], [64, 52, 5], [9], [46, 14, 38], [35, 1], []], ![[77, 72, 69, 18], [49, 69, 7, 18], [75, 42, 60, 19], [33, 67, 11, 31], [63, 5], [38, 25]], ![[0, 51, 8, 70], [71, 77, 47, 3], [76, 63, 55, 60], [46, 76, 70, 68], [15, 45], [48, 25]]]
 h' := ![![[35, 19, 5], [17, 63, 38], [53, 9, 59], [69, 76], [13, 47, 65], [0, 0, 1], [0, 1]], ![[0, 59, 74], [62, 71, 29], [8, 36, 50], [43, 22, 64], [63, 48, 41], [18, 66, 59], [35, 19, 5]], ![[0, 1], [67, 24, 12], [35, 34, 49], [69, 60, 15], [32, 63, 52], [72, 13, 19], [0, 59, 74]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46, 61], []]
 b := ![[], [2, 13, 51], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [38, 54, 44, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![724272, 313235, 37130]
  a := ![2, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![9168, 3965, 470]
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



lemma PB242I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB242I1 : PrimesBelowBoundCertificateInterval O 31 79 242 where
  m := 11
  g := ![2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB242I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0]
    · exact ![I47N0]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1, I61N2]
    · exact ![I67N0]
    · exact ![I71N0, I71N0, I71N1]
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
    · exact ![79507]
    · exact ![103823]
    · exact ![2809, 53]
    · exact ![3481, 59]
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
  β := ![I37N1, I41N1, I53N1, I59N1, I61N0, I61N1, I61N2, I71N0, I71N1, I73N0, I73N1, I73N2]
  Il := ![[I37N1], [I41N1], [], [], [I53N1], [I59N1], [I61N0, I61N1, I61N2], [], [I71N0, I71N0, I71N1], [I73N0, I73N1, I73N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
