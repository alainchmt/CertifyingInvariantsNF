
import IdealArithmetic.Examples.NF3_1_251451_1.RI3_1_251451_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![6, 1, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![6, 1, 0]] 
 ![![37, 0, 0], ![6, 1, 0], ![1, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![6, 1, 0], ![0, 6, 1], ![49, -36, 6]]]
  hmulB := by decide  
  f := ![![![127, 21, 0], ![-777, 0, 0]], ![![18, 3, 0], ![-110, 0, 0]], ![![-5, -1, 0], ![31, 1, 0]]]
  g := ![![![1, 0, 0], ![-6, 37, 0], ![-1, 0, 37]], ![![0, 1, 0], ![-1, 6, 1], ![7, -36, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4, 3, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-4, 3, 0]] 
 ![![37, 0, 0], ![11, 1, 0], ![27, 0, 1]] where
  M :=![![![-4, 3, 0], ![0, -4, 3], ![147, -108, -4]]]
  hmulB := by decide  
  f := ![![![-340, -12, -9]], ![![-113, -4, -3]], ![![-264, -9, -7]]]
  g := ![![![-1, 3, 0], ![-1, -4, 3], ![39, -108, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-17, 1, 0]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-17, 1, 0]] 
 ![![37, 0, 0], ![20, 1, 0], ![7, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-17, 1, 0], ![0, -17, 1], ![49, -36, -17]]]
  hmulB := by decide  
  f := ![![![545, -32, 0], ![1184, 0, 0]], ![![290, -17, 0], ![630, 0, 0]], ![![127, -7, 0], ![276, 1, 0]]]
  g := ![![![1, 0, 0], ![-20, 37, 0], ![-7, 0, 37]], ![![-1, 1, 0], ![9, -17, 1], ![24, -36, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![6, 1, 0]] ![![-4, 3, 0]]
  ![![37, 0, 0], ![29, 17, 1]] where
 M := ![![![-148, 111, 0]], ![![-24, 14, 3]]]
 hmul := by decide  
 g := ![![![![-4, 3, 0], ![0, 0, 0]]], ![![![-3, -1, 0], ![3, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![29, 17, 1]] ![![37, 0, 0], ![-17, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-629, 37, 0]], ![![1073, 629, 37], ![-444, -296, 0]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-17, 1, 0]]], ![![![29, 17, 1]], ![![-12, -8, 0]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0]] 
 ![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [32, 37, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 7, 11], [38, 33, 30], [0, 1]]
 g := ![![[22, 33, 4], [28, 32], [16, 25], [22, 31, 1], []], ![[34, 21, 37, 34], [9, 5], [14, 37], [27, 29, 19, 7], [10, 39]], ![[26, 36, 19, 34], [38, 32], [25, 5], [14, 25, 18, 35], [32, 39]]]
 h' := ![![[34, 7, 11], [27, 8, 2], [29, 30, 14], [34, 39, 36], [0, 0, 1], [0, 1]], ![[38, 33, 30], [3, 27, 31], [2, 7, 13], [9, 38, 18], [16, 6, 33], [34, 7, 11]], ![[0, 1], [23, 6, 8], [38, 4, 14], [31, 5, 28], [10, 35, 7], [38, 33, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40, 16], []]
 b := ![[], [7, 27, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [32, 37, 10, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3854, -738, -1722]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![94, -18, -42]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![1, 1, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![1, 1, 0]] 
 ![![43, 0, 0], ![1, 1, 0], ![42, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![1, 1, 0], ![0, 1, 1], ![49, -36, 1]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![43, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, -1, 0], ![42, 1, 0]]]
  g := ![![![1, 0, 0], ![-1, 43, 0], ![-42, 0, 43]], ![![0, 1, 0], ![-1, 1, 1], ![1, -36, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N0)

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := prime_ideal_of_norm_prime hp43.out _ NI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4146, -143, -110]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-4146, -143, -110]] 
 ![![43, 0, 0], ![2, 1, 0], ![39, 0, 1]] where
  M :=![![![-4146, -143, -110], ![-5390, -186, -143], ![-7007, -242, -186]]]
  hmulB := by decide  
  f := ![![![10, -22, 11]], ![![13, -10, 0]], ![![-16, 11, 1]]]
  g := ![![![10, -143, -110], ![13, -186, -143], ![17, -242, -186]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1

def I43N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-3, 1, 0]] i)))

def SI43N2: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-3, 1, 0]] 
 ![![43, 0, 0], ![40, 1, 0], ![34, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-3, 1, 0], ![0, -3, 1], ![49, -36, -3]]]
  hmulB := by decide  
  f := ![![![94, -31, 0], ![1333, 0, 0]], ![![88, -29, 0], ![1248, 0, 0]], ![![76, -25, 0], ![1078, 1, 0]]]
  g := ![![![1, 0, 0], ![-40, 43, 0], ![-34, 0, 43]], ![![-1, 1, 0], ![2, -3, 1], ![37, -36, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N2 : Nat.card (O ⧸ I43N2) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N2)

lemma isPrimeI43N2 : Ideal.IsPrime I43N2 := prime_ideal_of_norm_prime hp43.out _ NI43N2
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![1, 1, 0]] ![![-4146, -143, -110]]
  ![![43, 0, 0], ![45, 3, 1]] where
 M := ![![![-178278, -6149, -4730]], ![![-9536, -329, -253]]]
 hmul := by decide  
 g := ![![![![-1986, 1, -62], ![-2064, 0, 0]]], ![![![-137, -2, -4], ![-81, 0, 0]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![45, 3, 1]] ![![43, 0, 0], ![-3, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-129, 43, 0]], ![![1935, 129, 43], ![-86, 0, 0]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-3, 1, 0]]], ![![![45, 3, 1]], ![![-2, 0, 0]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![39, -12, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![39, -12, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![39, 35, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![39, -12, 1], ![49, 3, -12], ![-588, 481, 3]]]
  hmulB := by decide  
  f := ![![![-38, 12, -1], ![47, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-39, -35, 47]], ![![0, -1, 1], ![11, 9, -12], ![-15, 8, 3]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [7, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 46], [0, 1]]
 g := ![![[9, 27], [42, 32], [17, 4], [29, 21], [1]], ![[0, 20], [0, 15], [0, 43], [22, 26], [1]]]
 h' := ![![[31, 46], [35, 11], [22, 19], [32, 2], [40, 31], [0, 1]], ![[0, 1], [0, 36], [0, 28], [0, 45], [14, 16], [31, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [9, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [7, 16, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-596, 845, -278]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![218, 225, -278]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![12, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![12, 1, 0]] 
 ![![47, 0, 0], ![12, 1, 0], ![44, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![12, 1, 0], ![0, 12, 1], ![49, -36, 12]]]
  hmulB := by decide  
  f := ![![![25, 2, 0], ![-94, 0, 0]], ![![-12, -1, 0], ![48, 0, 0]], ![![28, 2, 0], ![-106, 1, 0]]]
  g := ![![![1, 0, 0], ![-12, 47, 0], ![-44, 0, 47]], ![![0, 1, 0], ![-4, 12, 1], ![-1, -36, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![39, -12, 1]] ![![47, 0, 0], ![12, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![564, 47, 0]], ![![1833, -564, 47], ![517, -141, 0]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![12, 1, 0]]], ![![![39, -12, 1]], ![![11, -3, 0]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![62, -36, -9]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![62, -36, -9]] 
 ![![53, 0, 0], ![0, 53, 0], ![52, 4, 1]] where
  M :=![![![62, -36, -9], ![-441, 386, -36], ![-1764, 855, 386]]]
  hmulB := by decide  
  f := ![![![-3392, -117, -90]], ![![-4410, -152, -117]], ![![-3769, -130, -100]]]
  g := ![![![10, 0, -9], ![27, 10, -36], ![-412, -13, 386]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [41, 44, 1] where
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
 g := ![![[14, 36], [38], [1, 13], [10], [9, 1]], ![[20, 17], [38], [12, 40], [10], [18, 52]]]
 h' := ![![[9, 52], [17, 47], [12, 12], [18, 38], [2, 40], [0, 1]], ![[0, 1], [16, 6], [14, 41], [42, 15], [44, 13], [9, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39]]
 b := ![[], [5, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [41, 44, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1223, 37, 49]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-25, -3, 49]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3392, 117, 90]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![3392, 117, 90]] 
 ![![53, 0, 0], ![49, 1, 0], ![37, 0, 1]] where
  M :=![![![3392, 117, 90], ![4410, 152, 117], ![5733, 198, 152]]]
  hmulB := by decide  
  f := ![![![-62, 36, 9]], ![![-49, 26, 9]], ![![-10, 9, -1]]]
  g := ![![![-107, 117, 90], ![-139, 152, 117], ![-181, 198, 152]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![62, -36, -9]] ![![3392, 117, 90]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![5, 1, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![5, 1, 0]] 
 ![![59, 0, 0], ![5, 1, 0], ![34, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![5, 1, 0], ![0, 5, 1], ![49, -36, 5]]]
  hmulB := by decide  
  f := ![![![51, 10, 0], ![-590, 0, 0]], ![![-5, -1, 0], ![60, 0, 0]], ![![26, 5, 0], ![-300, 1, 0]]]
  g := ![![![1, 0, 0], ![-5, 59, 0], ![-34, 0, 59]], ![![0, 1, 0], ![-1, 5, 1], ![1, -36, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N0 : Nat.card (O ⧸ I59N0) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N0)

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := prime_ideal_of_norm_prime hp59.out _ NI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![13, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![13, 1, 0]] 
 ![![59, 0, 0], ![13, 1, 0], ![8, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![13, 1, 0], ![0, 13, 1], ![49, -36, 13]]]
  hmulB := by decide  
  f := ![![![417, 32, 0], ![-1888, 0, 0]], ![![91, 7, 0], ![-412, 0, 0]], ![![42, 3, 0], ![-190, 1, 0]]]
  g := ![![![1, 0, 0], ![-13, 59, 0], ![-8, 0, 59]], ![![0, 1, 0], ![-3, 13, 1], ![7, -36, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-18, 1, 0]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-18, 1, 0]] 
 ![![59, 0, 0], ![41, 1, 0], ![30, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-18, 1, 0], ![0, -18, 1], ![49, -36, -18]]]
  hmulB := by decide  
  f := ![![![559, -31, 0], ![1829, 0, 0]], ![![397, -22, 0], ![1299, 0, 0]], ![![294, -16, 0], ![962, 1, 0]]]
  g := ![![![1, 0, 0], ![-41, 59, 0], ![-30, 0, 59]], ![![-1, 1, 0], ![12, -18, 1], ![35, -36, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![5, 1, 0]] ![![59, 0, 0], ![13, 1, 0]]
  ![![59, 0, 0], ![6, 18, 1]] where
 M := ![![![3481, 0, 0], ![767, 59, 0]], ![![295, 59, 0], ![65, 18, 1]]]
 hmul := by decide  
 g := ![![![![53, -18, -1], ![59, 0, 0]], ![![7, -17, -1], ![59, 0, 0]]], ![![![-1, -17, -1], ![59, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![6, 18, 1]] ![![59, 0, 0], ![-18, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-1062, 59, 0]], ![![354, 1062, 59], ![-59, -354, 0]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-18, 1, 0]]], ![![![6, 18, 1]], ![![-1, -6, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0]] 
 ![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [5, 10, 25, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [43, 22, 55], [54, 38, 6], [0, 1]]
 g := ![![[28, 13, 41], [17, 42], [1, 31, 56], [3, 3, 15], [1]], ![[14, 34, 41, 26], [59, 42], [36, 42, 37, 43], [31, 42, 37, 32], [19, 51, 29, 28]], ![[24, 14, 17, 31], [30, 46], [6, 16, 27, 55], [17, 33], [15, 27, 46, 33]]]
 h' := ![![[43, 22, 55], [1, 57, 38], [56, 60, 46], [46, 41, 42], [56, 51, 36], [0, 1]], ![[54, 38, 6], [37, 12, 4], [24, 22, 46], [58, 59, 8], [51, 16, 25], [43, 22, 55]], ![[0, 1], [58, 53, 19], [5, 40, 30], [19, 22, 11], [9, 55], [54, 38, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50], []]
 b := ![[], [24, 49], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [5, 10, 25, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-120597, 148230, -42578]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1977, 2430, -698]
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


def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, -2, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![3, -2, 0]] 
 ![![67, 0, 0], ![32, 1, 0], ![48, 0, 1]] where
  M :=![![![3, -2, 0], ![0, 3, -2], ![-98, 72, 3]]]
  hmulB := by decide  
  f := ![![![153, 6, 4]], ![![76, 3, 2]], ![![114, 4, 3]]]
  g := ![![![1, -2, 0], ![0, 3, -2], ![-38, 72, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N0 : Nat.card (O ⧸ I67N0) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N0)

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := prime_ideal_of_norm_prime hp67.out _ NI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-16, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-16, 1, 0]] 
 ![![67, 0, 0], ![51, 1, 0], ![12, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-16, 1, 0], ![0, -16, 1], ![49, -36, -16]]]
  hmulB := by decide  
  f := ![![![465, -29, 0], ![1943, 0, 0]], ![![353, -22, 0], ![1475, 0, 0]], ![![100, -6, 0], ![418, 1, 0]]]
  g := ![![![1, 0, 0], ![-51, 67, 0], ![-12, 0, 67]], ![![-1, 1, 0], ![12, -16, 1], ![31, -36, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![3, -2, 0]] ![![67, 0, 0], ![-16, 1, 0]]
  ![![67, 0, 0], ![24, 16, 1]] where
 M := ![![![201, -134, 0], ![-48, 35, -2]]]
 hmul := by decide  
 g := ![![![![-21, -18, -1], ![67, 0, 0]], ![![-24, -15, -1], ![65, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![24, 16, 1]] ![![67, 0, 0], ![-16, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-1072, 67, 0]], ![![1608, 1072, 67], ![-335, -268, 0]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-16, 1, 0]]], ![![![24, 16, 1]], ![![-5, -4, 0]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1, I67N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
    exact isPrimeI67N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0 ⊙ MulI67N1)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![3, -31, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![3, -31, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![3, 40, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![3, -31, 1], ![49, -33, -31], ![-1519, 1165, -33]]]
  hmulB := by decide  
  f := ![![![-2, 31, -1], ![71, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-3, -40, 71]], ![![0, -1, 1], ![2, 17, -31], ![-20, 35, -33]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [34, 63, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 70], [0, 1]]
 g := ![![[29, 19], [62, 64], [1, 27], [30], [64], [1]], ![[39, 52], [6, 7], [4, 44], [30], [64], [1]]]
 h' := ![![[8, 70], [22, 44], [37, 63], [11, 58], [45, 39], [37, 8], [0, 1]], ![[0, 1], [19, 27], [44, 8], [49, 13], [2, 32], [30, 63], [8, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [63, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [34, 63, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![132, -86, -98]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![6, 54, -98]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![31, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![31, 1, 0]] 
 ![![71, 0, 0], ![31, 1, 0], ![33, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![31, 1, 0], ![0, 31, 1], ![49, -36, 31]]]
  hmulB := by decide  
  f := ![![![714, 23, 0], ![-1633, 0, 0]], ![![310, 10, 0], ![-709, 0, 0]], ![![324, 10, 0], ![-741, 1, 0]]]
  g := ![![![1, 0, 0], ![-31, 71, 0], ![-33, 0, 71]], ![![0, 1, 0], ![-14, 31, 1], ![2, -36, 31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![3, -31, 1]] ![![71, 0, 0], ![31, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![2201, 71, 0]], ![![213, -2201, 71], ![142, -994, 0]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![31, 1, 0]]], ![![![3, -31, 1]], ![![2, -14, 0]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![32, -19, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![32, -19, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![32, 54, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![32, -19, 1], ![49, -4, -19], ![-931, 733, -4]]]
  hmulB := by decide  
  f := ![![![-31, 19, -1], ![73, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-32, -54, 73]], ![![0, -1, 1], ![9, 14, -19], ![-11, 13, -4]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [40, 70, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 72], [0, 1]]
 g := ![![[20, 12], [54], [70], [23, 36], [9], [1]], ![[56, 61], [54], [70], [58, 37], [9], [1]]]
 h' := ![![[3, 72], [28, 31], [12, 28], [29, 17], [72, 6], [33, 3], [0, 1]], ![[0, 1], [48, 42], [23, 45], [7, 56], [17, 67], [42, 70], [3, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [14, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [40, 70, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1973, 49, 397]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-147, -293, 397]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![19, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![19, 1, 0]] 
 ![![73, 0, 0], ![19, 1, 0], ![4, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![19, 1, 0], ![0, 19, 1], ![49, -36, 19]]]
  hmulB := by decide  
  f := ![![![609, 32, 0], ![-2336, 0, 0]], ![![133, 7, 0], ![-510, 0, 0]], ![![24, 1, 0], ![-92, 1, 0]]]
  g := ![![![1, 0, 0], ![-19, 73, 0], ![-4, 0, 73]], ![![0, 1, 0], ![-5, 19, 1], ![9, -36, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![32, -19, 1]] ![![73, 0, 0], ![19, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![1387, 73, 0]], ![![2336, -1387, 73], ![657, -365, 0]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![19, 1, 0]]], ![![![32, -19, 1]], ![![9, -5, 0]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![41, -20, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![41, -20, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![41, 59, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![41, -20, 1], ![49, 5, -20], ![-980, 769, 5]]]
  hmulB := by decide  
  f := ![![![-40, 20, -1], ![79, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-41, -59, 79]], ![![0, -1, 1], ![11, 15, -20], ![-15, 6, 5]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [7, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [56, 78], [0, 1]]
 g := ![![[71, 40], [22, 52], [46, 22], [15, 25], [55], [1]], ![[20, 39], [11, 27], [14, 57], [72, 54], [55], [1]]]
 h' := ![![[56, 78], [4, 35], [73, 17], [53, 38], [59, 5], [72, 56], [0, 1]], ![[0, 1], [68, 44], [77, 62], [48, 41], [23, 74], [48, 23], [56, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [73]]
 b := ![[], [5, 76]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [7, 23, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-309, 328, -48]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![21, 40, -48]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![20, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![20, 1, 0]] 
 ![![79, 0, 0], ![20, 1, 0], ![74, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![20, 1, 0], ![0, 20, 1], ![49, -36, 20]]]
  hmulB := by decide  
  f := ![![![41, 2, 0], ![-158, 0, 0]], ![![-20, -1, 0], ![80, 0, 0]], ![![46, 2, 0], ![-178, 1, 0]]]
  g := ![![![1, 0, 0], ![-20, 79, 0], ![-74, 0, 79]], ![![0, 1, 0], ![-6, 20, 1], ![-9, -36, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![41, -20, 1]] ![![79, 0, 0], ![20, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![1580, 79, 0]], ![![3239, -1580, 79], ![869, -395, 0]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![20, 1, 0]]], ![![![41, -20, 1]], ![![11, -5, 0]]]]
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


lemma PB142I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB142I1 : PrimesBelowBoundCertificateInterval O 31 79 142 where
  m := 11
  g := ![3, 1, 3, 2, 2, 3, 1, 3, 2, 2, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB142I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0]
    · exact ![I43N0, I43N1, I43N2]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1, I59N2]
    · exact ![I61N0]
    · exact ![I67N0, I67N1, I67N1]
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
    · exact ![37, 37, 37]
    · exact ![68921]
    · exact ![43, 43, 43]
    · exact ![2209, 47]
    · exact ![2809, 53]
    · exact ![59, 59, 59]
    · exact ![226981]
    · exact ![67, 67, 67]
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
      exact NI37N1
      exact NI37N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
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
  β := ![I37N0, I37N1, I37N2, I43N0, I43N1, I43N2, I47N1, I53N1, I59N0, I59N1, I59N2, I67N0, I67N1, I71N1, I73N1, I79N1]
  Il := ![[I37N0, I37N1, I37N2], [], [I43N0, I43N1, I43N2], [I47N1], [I53N1], [I59N0, I59N1, I59N2], [], [I67N0, I67N1, I67N1], [I71N1], [I73N1], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
