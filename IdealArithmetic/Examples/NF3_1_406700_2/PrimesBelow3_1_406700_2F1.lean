
import IdealArithmetic.Examples.NF3_1_406700_2.RI3_1_406700_2
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [21, 31, 27, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 9, 35], [36, 27, 2], [0, 1]]
 g := ![![[3, 0, 25], [26, 27], [3, 8, 25], [10, 1], []], ![[3, 6], [10, 36], [32, 3, 28, 23], [16, 26], [4, 4]], ![[9, 21, 22, 13], [1, 11], [17, 2, 22, 32], [28, 7], [0, 4]]]
 h' := ![![[11, 9, 35], [19, 12, 5], [11, 31, 8], [12, 2, 32], [0, 0, 1], [0, 1]], ![[36, 27, 2], [3, 21], [19, 14, 6], [34, 31, 9], [0, 27, 27], [11, 9, 35]], ![[0, 1], [12, 4, 32], [25, 29, 23], [5, 4, 33], [1, 10, 9], [36, 27, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34, 19], []]
 b := ![[], [26, 34, 28], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [21, 31, 27, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-348984, -148925, -68450]
  a := ![-1, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-9432, -4025, -1850]
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


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [4, 19, 24, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 30, 36], [9, 10, 5], [0, 1]]
 g := ![![[39, 35, 2], [26, 40], [40, 1], [24, 17, 1], []], ![[17, 24, 8, 39], [17, 21], [18, 32], [19, 26, 29, 33], [2, 25]], ![[2, 18, 35, 23], [5, 31], [16, 20], [11, 33, 38, 31], [33, 25]]]
 h' := ![![[8, 30, 36], [3, 35, 17], [36, 9, 32], [27, 9, 40], [0, 0, 1], [0, 1]], ![[9, 10, 5], [5, 17, 36], [14, 21, 29], [2, 10, 27], [15, 14, 10], [8, 30, 36]], ![[0, 1], [25, 30, 29], [2, 11, 21], [36, 22, 15], [31, 27, 30], [9, 10, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33, 14], []]
 b := ![[], [40, 31, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [4, 19, 24, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![643782, 410861, 693925]
  a := ![2, -5, 11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![15702, 10021, 16925]
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

instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![5, -5, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![5, -5, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![5, 38, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![5, -5, 1], ![-72, -14, -23], ![290, 97, -28]]]
  hmulB := by decide  
  f := ![![![-4, 5, -1], ![43, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-5, -38, 43]], ![![0, -1, 1], ![1, 20, -23], ![10, 27, -28]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [11, 25, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 42], [0, 1]]
 g := ![![[14, 4], [15, 35], [13], [18, 23], [1]], ![[0, 39], [0, 8], [13], [2, 20], [1]]]
 h' := ![![[18, 42], [7, 2], [17, 11], [17, 20], [32, 18], [0, 1]], ![[0, 1], [0, 41], [0, 32], [33, 23], [12, 25], [18, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [36, 39]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [11, 25, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2992882, -1541941, -1541446]
  a := ![-65, 2, -261]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![109636, 1326349, -1541446]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-20, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-20, 1, 0]] 
 ![![43, 0, 0], ![23, 1, 0], ![28, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-20, 1, 0], ![1, -21, 5], ![-67, -24, -18]]]
  hmulB := by decide  
  f := ![![![-49, 1888, -450], ![86, 3870, 0]], ![![-27, 1007, -240], ![44, 2064, 0]], ![![-24, 1229, -293], ![73, 2520, 0]]]
  g := ![![![1, 0, 0], ![-23, 43, 0], ![-28, 0, 43]], ![![-1, 1, 0], ![8, -21, 5], ![23, -24, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![5, -5, 1]] ![![43, 0, 0], ![-20, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-860, 43, 0]], ![![215, -215, 43], ![-172, 86, -43]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-20, 1, 0]]], ![![![5, -5, 1]], ![![-4, 2, -1]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![38, -2, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![38, -2, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![38, 45, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![38, -2, 1], ![-69, 16, -8], ![89, 25, 11]]]
  hmulB := by decide  
  f := ![![![-37, 2, -1], ![47, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-38, -45, 47]], ![![0, -1, 1], ![5, 8, -8], ![-7, -10, 11]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [3, 35, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 46], [0, 1]]
 g := ![![[43, 16], [31, 17], [15, 34], [11, 3], [1]], ![[0, 31], [0, 30], [0, 13], [0, 44], [1]]]
 h' := ![![[12, 46], [1, 43], [2, 39], [14, 38], [44, 12], [0, 1]], ![[0, 1], [0, 4], [0, 8], [0, 9], [0, 35], [12, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37]]
 b := ![[], [30, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [3, 35, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![404, -563, -3220]
  a := ![-2, 4, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2612, 3071, -3220]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![8, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![8, 1, 0]] 
 ![![47, 0, 0], ![8, 1, 0], ![36, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![8, 1, 0], ![1, 7, 5], ![-67, -24, 10]]]
  hmulB := by decide  
  f := ![![![-1, 41, 30], ![47, -282, 0]], ![![1, 7, 5], ![1, -47, 0]], ![![4, 32, 23], ![8, -216, 0]]]
  g := ![![![1, 0, 0], ![-8, 47, 0], ![-36, 0, 47]], ![![0, 1, 0], ![-5, 7, 5], ![-5, -24, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![38, -2, 1]] ![![47, 0, 0], ![8, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![376, 47, 0]], ![![1786, -94, 47], ![235, 0, 0]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![8, 1, 0]]], ![![![38, -2, 1]], ![![5, 0, 0]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![19, 22, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![19, 22, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![19, 22, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![19, 22, 1], ![-45, -27, 112], ![-1519, -551, 40]]]
  hmulB := by decide  
  f := ![![![-18, -22, -1], ![53, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-19, -22, 53]], ![![0, 0, 1], ![-41, -47, 112], ![-43, -27, 40]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [33, 44, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 52], [0, 1]]
 g := ![![[19, 47], [37], [45, 13], [25], [9, 1]], ![[18, 6], [37], [3, 40], [25], [18, 52]]]
 h' := ![![[9, 52], [52, 43], [52, 39], [40, 15], [21, 48], [0, 1]], ![[0, 1], [15, 10], [32, 14], [16, 38], [29, 5], [9, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51]]
 b := ![[], [31, 52]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [33, 44, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1135, -575, -785]
  a := ![-1, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![260, 315, -785]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-6, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-6, 1, 0]] 
 ![![53, 0, 0], ![47, 1, 0], ![13, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-6, 1, 0], ![1, -7, 5], ![-67, -24, -4]]]
  hmulB := by decide  
  f := ![![![-1107, 8002, -5720], ![318, 60632, 0]], ![![-983, 7093, -5070], ![266, 53742, 0]], ![![-267, 1962, -1403], ![118, 14872, 0]]]
  g := ![![![1, 0, 0], ![-47, 53, 0], ![-13, 0, 53]], ![![-1, 1, 0], ![5, -7, 5], ![21, -24, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![19, 22, 1]] ![![53, 0, 0], ![-6, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-318, 53, 0]], ![![1007, 1166, 53], ![-159, -159, 106]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-6, 1, 0]]], ![![![19, 22, 1]], ![![-3, -3, 2]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0]] 
 ![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [12, 51, 45, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [33, 21, 33], [40, 37, 26], [0, 1]]
 g := ![![[12, 42, 27], [20, 31, 49], [10, 28], [14, 18, 19], [1]], ![[20, 51, 49, 18], [44, 19, 23, 47], [53, 26], [41, 45, 0, 50], [41, 39, 15, 6]], ![[32, 23, 8, 49], [52, 11, 48, 26], [13, 22], [18, 10, 31, 36], [33, 11, 22, 53]]]
 h' := ![![[33, 21, 33], [55, 11, 33], [20, 51, 52], [9, 40, 38], [47, 8, 14], [0, 1]], ![[40, 37, 26], [27, 4, 50], [7, 50, 8], [17, 19, 12], [45, 27, 15], [33, 21, 33]], ![[0, 1], [35, 44, 35], [30, 17, 58], [3, 0, 9], [2, 24, 30], [40, 37, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21, 27], []]
 b := ![[], [21, 4, 26], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [12, 51, 45, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3899723, 1118286, -1347678]
  a := ![2, 18, 9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![66097, 18954, -22842]
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


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [32, 11, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [58, 45, 50], [58, 15, 11], [0, 1]]
 g := ![![[2, 6, 25], [14, 58], [20, 48, 46], [3, 38, 36], [1]], ![[35, 17, 8, 50], [51, 27], [27, 53, 18, 2], [16, 60, 41, 43], [45, 27, 43, 11]], ![[43, 44, 36, 30], [34, 39], [28, 49, 10, 26], [46, 57, 56, 43], [55, 48, 21, 50]]]
 h' := ![![[58, 45, 50], [25, 21, 56], [31, 18, 27], [26, 19, 31], [29, 50, 55], [0, 1]], ![[58, 15, 11], [40, 48, 60], [56, 54, 24], [10, 48, 12], [58, 39, 31], [58, 45, 50]], ![[0, 1], [58, 53, 6], [32, 50, 10], [57, 55, 18], [43, 33, 36], [58, 15, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 33], []]
 b := ![[], [55, 53, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [32, 11, 6, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-355630, -241133, -425353]
  a := ![-2, 4, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5830, -3953, -6973]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![28, 29, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![28, 29, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![28, 29, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![28, 29, 1], ![-38, -25, 147], ![-1988, -719, 63]]]
  hmulB := by decide  
  f := ![![![-27, -29, -1], ![67, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-28, -29, 67]], ![![0, 0, 1], ![-62, -64, 147], ![-56, -38, 63]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [52, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [55, 66], [0, 1]]
 g := ![![[26, 37], [1, 9], [35], [54], [10], [1]], ![[51, 30], [27, 58], [35], [54], [10], [1]]]
 h' := ![![[55, 66], [15, 38], [60, 64], [65, 13], [40, 56], [15, 55], [0, 1]], ![[0, 1], [28, 29], [29, 3], [43, 54], [38, 11], [25, 12], [55, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [63, 44]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [52, 12, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3079, -1837, -2175]
  a := ![2, -1, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![863, 914, -2175]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-13, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-13, 1, 0]] 
 ![![67, 0, 0], ![54, 1, 0], ![4, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-13, 1, 0], ![1, -14, 5], ![-67, -24, -11]]]
  hmulB := by decide  
  f := ![![![-2085, 31738, -11340], ![938, 151956, 0]], ![![-1683, 25567, -9135], ![738, 122409, 0]], ![![-114, 1894, -677], ![110, 9072, 0]]]
  g := ![![![1, 0, 0], ![-54, 67, 0], ![-4, 0, 67]], ![![-1, 1, 0], ![11, -14, 5], ![19, -24, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![28, 29, 1]] ![![67, 0, 0], ![-13, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-871, 67, 0]], ![![1876, 1943, 67], ![-402, -402, 134]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-13, 1, 0]]], ![![![28, 29, 1]], ![![-6, -6, 2]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11, -3, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-11, -3, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![60, 68, 1]] where
  M :=![![![-11, -3, 1], ![-70, -32, -13], ![156, 49, -40]]]
  hmulB := by decide  
  f := ![![![-27, 1, -1]], ![![68, -4, 3]], ![![42, -3, 2]]]
  g := ![![![-1, -1, 1], ![10, 12, -13], ![36, 39, -40]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [40, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [59, 70], [0, 1]]
 g := ![![[50, 16], [58, 64], [26, 16], [27], [2], [1]], ![[0, 55], [0, 7], [47, 55], [27], [2], [1]]]
 h' := ![![[59, 70], [23, 67], [25, 8], [45, 4], [29, 13], [31, 59], [0, 1]], ![[0, 1], [0, 4], [0, 63], [68, 67], [15, 58], [33, 12], [59, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [54, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [40, 12, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-17995, -9200, -9240]
  a := ![-5, 0, -20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![7555, 8720, -9240]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-27, 1, -1]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![-27, 1, -1]] 
 ![![71, 0, 0], ![13, 1, 0], ![40, 0, 1]] where
  M :=![![![-27, 1, -1], ![68, -4, 3], ![-22, -1, -2]]]
  hmulB := by decide  
  f := ![![![-11, -3, 1]], ![![-3, -1, 0]], ![![-4, -1, 0]]]
  g := ![![![0, 1, -1], ![0, -4, 3], ![1, -1, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-11, -3, 1]] ![![-27, 1, -1]]
  ![![71, 0, 0]] where
 M := ![![![71, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![13, -14, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![13, -14, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![13, 59, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![13, -14, 1], ![-81, 3, -68], ![893, 313, -38]]]
  hmulB := by decide  
  f := ![![![-12, 14, -1], ![73, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-13, -59, 73]], ![![0, -1, 1], ![11, 55, -68], ![19, 35, -38]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [69, 33, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 72], [0, 1]]
 g := ![![[10, 18], [48], [71], [23, 49], [67], [1]], ![[0, 55], [48], [71], [12, 24], [67], [1]]]
 h' := ![![[40, 72], [44, 50], [61, 11], [19, 12], [65, 7], [4, 40], [0, 1]], ![[0, 1], [0, 23], [63, 62], [61, 61], [53, 66], [71, 33], [40, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58]]
 b := ![[], [4, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [69, 33, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![14725, 2280, -6858]
  a := ![4, -12, 18]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1423, 5574, -6858]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-5, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-5, 1, 0]] 
 ![![73, 0, 0], ![68, 1, 0], ![38, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-5, 1, 0], ![1, -6, 5], ![-67, -24, -3]]]
  hmulB := by decide  
  f := ![![![-1376, 8349, -6960], ![219, 101616, 0]], ![![-1280, 7773, -6480], ![220, 94608, 0]], ![![-716, 4346, -3623], ![118, 52896, 0]]]
  g := ![![![1, 0, 0], ![-68, 73, 0], ![-38, 0, 73]], ![![-1, 1, 0], ![3, -6, 5], ![23, -24, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![13, -14, 1]] ![![73, 0, 0], ![-5, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-365, 73, 0]], ![![949, -1022, 73], ![-146, 73, -73]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-5, 1, 0]]], ![![![13, -14, 1]], ![![-2, 1, -1]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![28, -6, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![28, -6, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![28, 73, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![28, -6, 1], ![-73, 10, -28], ![357, 121, -7]]]
  hmulB := by decide  
  f := ![![![-27, 6, -1], ![79, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-28, -73, 79]], ![![0, -1, 1], ![9, 26, -28], ![7, 8, -7]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [71, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [60, 78], [0, 1]]
 g := ![![[47, 67], [34, 65], [44, 22], [40, 44], [45], [1]], ![[38, 12], [63, 14], [21, 57], [73, 35], [45], [1]]]
 h' := ![![[60, 78], [35, 64], [36, 67], [4, 38], [29, 26], [8, 60], [0, 1]], ![[0, 1], [4, 15], [27, 12], [72, 41], [9, 53], [53, 19], [60, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [49, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [71, 19, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-130392, -69353, -72484]
  a := ![14, -2, 57]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![24040, 66101, -72484]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![28, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![28, 1, 0]] 
 ![![79, 0, 0], ![28, 1, 0], ![7, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![28, 1, 0], ![1, 27, 5], ![-67, -24, 30]]]
  hmulB := by decide  
  f := ![![![-2399, -82920, -15360], ![-1896, 242688, 0]], ![![-864, -29368, -5440], ![-631, 85952, 0]], ![![-231, -7348, -1361], ![-116, 21504, 0]]]
  g := ![![![1, 0, 0], ![-28, 79, 0], ![-7, 0, 79]], ![![0, 1, 0], ![-10, 27, 5], ![5, -24, 30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![28, -6, 1]] ![![79, 0, 0], ![28, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![2212, 79, 0]], ![![2212, -474, 79], ![711, -158, 0]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![28, 1, 0]]], ![![![28, -6, 1]], ![![9, -2, 0]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0)


lemma PB181I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB181I1 : PrimesBelowBoundCertificateInterval O 31 79 181 where
  m := 11
  g := ![1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB181I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0]
    · exact ![I61N0]
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1]
    · exact ![I79N0, I79N1]
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
    · exact ![1849, 43]
    · exact ![2209, 47]
    · exact ![2809, 53]
    · exact ![205379]
    · exact ![226981]
    · exact ![4489, 67]
    · exact ![5041, 71]
    · exact ![5329, 73]
    · exact ![6241, 79]
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
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
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
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I43N1, I47N1, I53N1, I67N1, I71N1, I73N1, I79N1]
  Il := ![[], [], [I43N1], [I47N1], [I53N1], [], [], [I67N1], [I71N1], [I73N1], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
