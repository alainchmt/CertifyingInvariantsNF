
import IdealArithmetic.Examples.NF3_3_219961_2.RI3_3_219961_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![10, 1, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![10, 1, 0]] 
 ![![37, 0, 0], ![10, 1, 0], ![28, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![10, 1, 0], ![0, 11, 4], ![152, 39, 10]]]
  hmulB := by decide  
  f := ![![![141, 14, 0], ![-518, 0, 0]], ![![30, 3, 0], ![-110, 0, 0]], ![![104, 2, -3], ![-382, 28, 0]]]
  g := ![![![1, 0, 0], ![-10, 37, 0], ![-28, 0, 37]], ![![0, 1, 0], ![-6, 11, 4], ![-14, 39, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-7, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-7, 1, 0]] 
 ![![37, 0, 0], ![30, 1, 0], ![8, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-7, 1, 0], ![0, -6, 4], ![152, 39, -7]]]
  hmulB := by decide  
  f := ![![![155, -22, 0], ![814, 0, 0]], ![![134, -19, 0], ![704, 0, 0]], ![![46, -2, -3], ![242, 28, 0]]]
  g := ![![![1, 0, 0], ![-30, 37, 0], ![-8, 0, 37]], ![![-1, 1, 0], ![4, -6, 4], ![-26, 39, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-4, 1, 0]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-4, 1, 0]] 
 ![![37, 0, 0], ![33, 1, 0], ![34, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-4, 1, 0], ![0, -3, 4], ![152, 39, -4]]]
  hmulB := by decide  
  f := ![![![121, -30, 0], ![1110, 0, 0]], ![![109, -27, 0], ![1000, 0, 0]], ![![114, -26, -3], ![1046, 28, 0]]]
  g := ![![![1, 0, 0], ![-33, 37, 0], ![-34, 0, 37]], ![![-1, 1, 0], ![-1, -3, 4], ![-27, 39, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![10, 1, 0]] ![![37, 0, 0], ![-7, 1, 0]]
  ![![37, 0, 0], ![-36, 1, 1]] where
 M := ![![![1369, 0, 0], ![-259, 37, 0]], ![![370, 37, 0], ![-70, 4, 4]]]
 hmul := by decide  
 g := ![![![![37, 0, 0], ![0, 0, 0]], ![![29, 0, -1], ![37, 0, 0]]], ![![![10, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![4, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![-36, 1, 1]] ![![37, 0, 0], ![-4, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-148, 37, 0]], ![![-1332, 37, 37], ![296, 0, 0]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-4, 1, 0]]], ![![![-36, 1, 1]], ![![8, 0, 0]]]]
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


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [35, 24, 15, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 27, 12], [30, 13, 29], [0, 1]]
 g := ![![[13, 14, 32], [24, 9], [1, 10], [37, 26, 1], []], ![[40, 39, 2, 19], [11, 21], [3, 8], [22, 31, 12, 19], [5, 21]], ![[25, 9, 15, 26], [8, 40], [0, 40], [28, 37, 25, 26], [29, 21]]]
 h' := ![![[37, 27, 12], [3, 38, 27], [8, 35, 38], [17, 6, 16], [0, 0, 1], [0, 1]], ![[30, 13, 29], [27, 30, 28], [17, 17, 12], [32, 0, 34], [5, 36, 13], [37, 27, 12]], ![[0, 1], [6, 14, 27], [9, 30, 32], [38, 35, 32], [8, 5, 27], [30, 13, 29]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 22], []]
 b := ![[], [39, 2, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [35, 24, 15, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3184593, -1436804, -537756]
  a := ![0, -2, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-77673, -35044, -13116]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![175, 60, 16]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![175, 60, 16]] 
 ![![43, 0, 0], ![11, 1, 0], ![10, 0, 1]] where
  M :=![![![175, 60, 16], ![2432, 859, 240], ![8512, 2948, 799]]]
  hmulB := by decide  
  f := ![![![-21179, -772, 656]], ![![-3099, -113, 96]], ![![-8234, -300, 255]]]
  g := ![![![-15, 60, 16], ![-219, 859, 240], ![-742, 2948, 799]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N0)

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := prime_ideal_of_norm_prime hp43.out _ NI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-307, -40, 18]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-307, -40, 18]] 
 ![![43, 0, 0], ![13, 1, 0], ![19, 0, 1]] where
  M :=![![![-307, -40, 18], ![2736, 355, -160], ![-6764, -876, 395]]]
  hmulB := by decide  
  f := ![![![-65, -32, -10]], ![![-55, -21, -6]], ![![-133, -52, -15]]]
  g := ![![![-3, -40, 18], ![27, 355, -160], ![-67, -876, 395]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1

def I43N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-39, -14, -4]] i)))

def SI43N2: IdealEqSpanCertificate' Table ![![-39, -14, -4]] 
 ![![43, 0, 0], ![18, 1, 0], ![22, 0, 1]] where
  M :=![![![-39, -14, -4], ![-608, -209, -56], ![-1976, -698, -195]]]
  hmulB := by decide  
  f := ![![![1667, 62, -52]], ![![514, 19, -16]], ![![1118, 42, -35]]]
  g := ![![![7, -14, -4], ![102, -209, -56], ![346, -698, -195]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N2 : Nat.card (O ⧸ I43N2) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N2)

lemma isPrimeI43N2 : Ideal.IsPrime I43N2 := prime_ideal_of_norm_prime hp43.out _ NI43N2
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![175, 60, 16]] ![![-307, -40, 18]]
  ![![2211, 284, -130]] where
 M := ![![![2211, 284, -130]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![2211, 284, -130]] ![![-39, -14, -4]]
  ![![43, 0, 0]] where
 M := ![![![-2021, 430, 602]]]
 hmul := by decide  
 g := ![![![![-47, 10, 14]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0]] 
 ![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [3, 32, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 44, 15], [12, 2, 32], [0, 1]]
 g := ![![[21, 13, 21], [4, 5, 6], [26, 10, 1], [31, 43, 1], []], ![[42, 37, 28, 19], [18, 23, 45, 11], [10, 18, 16, 44], [21, 8, 2, 13], [44, 37]], ![[8, 15, 12, 34], [46, 27, 39, 17], [25, 7, 39, 21], [19, 25, 36, 6], [27, 37]]]
 h' := ![![[31, 44, 15], [35, 19, 31], [16, 32, 10], [1, 7, 1], [0, 0, 1], [0, 1]], ![[12, 2, 32], [3, 10, 18], [39, 9, 30], [13, 13, 13], [30, 34, 2], [31, 44, 15]], ![[0, 1], [7, 18, 45], [43, 6, 7], [7, 27, 33], [16, 13, 44], [12, 2, 32]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 25], []]
 b := ![[], [33, 25, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [3, 32, 4, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1568766, 809951, 341126]
  a := ![-1, 1, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![33378, 17233, 7258]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0]] 
 ![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [37, 34, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [51, 10, 21], [50, 42, 32], [0, 1]]
 g := ![![[33, 44, 47], [26, 43], [29, 40, 42], [3, 25], [1]], ![[9, 19, 37, 23], [51, 40], [36, 22, 8, 50], [36, 52], [52, 11, 50, 39]], ![[23, 39, 8, 8], [24, 11], [32, 6, 25, 18], [15, 42], [16, 44, 5, 14]]]
 h' := ![![[51, 10, 21], [2, 47, 43], [40, 9, 34], [39, 5, 25], [16, 19, 48], [0, 1]], ![[50, 42, 32], [10, 8, 37], [25, 39, 27], [39, 39, 42], [29, 12, 30], [51, 10, 21]], ![[0, 1], [30, 51, 26], [32, 5, 45], [52, 9, 39], [17, 22, 28], [50, 42, 32]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52, 48], []]
 b := ![[], [34, 17, 28], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [37, 34, 5, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-240991, -10070, -20458]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4547, -190, -386]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 148877 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def PBC53 : ContainsPrimesAboveP 53 ![I53N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![53, 0, 0]]) timesTableT_eq_Table B_one_repr 53 (by decide) 𝕀

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


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [9, 42, 52, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [17, 5, 9], [49, 53, 50], [0, 1]]
 g := ![![[44, 20, 53], [16, 20, 3], [10, 27], [48, 50, 49], [1]], ![[36, 40, 11, 49], [2, 47, 21, 29], [51, 21], [8, 51, 26, 28], [51, 6, 5, 21]], ![[49, 9, 19, 58], [35, 21, 34, 54], [1, 1], [29, 47], [13, 51, 47, 38]]]
 h' := ![![[17, 5, 9], [33, 19, 42], [35, 51, 48], [40, 34, 26], [50, 17, 7], [0, 1]], ![[49, 53, 50], [30, 29, 37], [49, 11, 53], [6, 28, 32], [29, 15, 52], [17, 5, 9]], ![[0, 1], [56, 11, 39], [55, 56, 17], [51, 56, 1], [4, 27], [49, 53, 50]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44, 44], []]
 b := ![[], [8, 57, 41], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [9, 42, 52, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5884424, -2675414, -998575]
  a := ![1, -2, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-99736, -45346, -16925]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-25, 1, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-25, 1, 0]] 
 ![![61, 0, 0], ![36, 1, 0], ![33, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-25, 1, 0], ![0, -24, 4], ![152, 39, -25]]]
  hmulB := by decide  
  f := ![![![901, -36, 0], ![2196, 0, 0]], ![![526, -21, 0], ![1282, 0, 0]], ![![503, -2, -3], ![1226, 46, 0]]]
  g := ![![![1, 0, 0], ![-36, 61, 0], ![-33, 0, 61]], ![![-1, 1, 0], ![12, -24, 4], ![-7, 39, -25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N0 : Nat.card (O ⧸ I61N0) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N0)

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := prime_ideal_of_norm_prime hp61.out _ NI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-23, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-23, 1, 0]] 
 ![![61, 0, 0], ![38, 1, 0], ![26, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-23, 1, 0], ![0, -22, 4], ![152, 39, -23]]]
  hmulB := by decide  
  f := ![![![507, -22, 0], ![1342, 0, 0]], ![![346, -15, 0], ![916, 0, 0]], ![![244, 6, -3], ![646, 46, 0]]]
  g := ![![![1, 0, 0], ![-38, 61, 0], ![-26, 0, 61]], ![![-1, 1, 0], ![12, -22, 4], ![-12, 39, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-14, 1, 0]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-14, 1, 0]] 
 ![![61, 0, 0], ![47, 1, 0], ![46, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-14, 1, 0], ![0, -13, 4], ![152, 39, -14]]]
  hmulB := by decide  
  f := ![![![757, -54, 0], ![3294, 0, 0]], ![![575, -41, 0], ![2502, 0, 0]], ![![558, -30, -3], ![2428, 46, 0]]]
  g := ![![![1, 0, 0], ![-47, 61, 0], ![-46, 0, 61]], ![![-1, 1, 0], ![7, -13, 4], ![-17, 39, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-25, 1, 0]] ![![61, 0, 0], ![-23, 1, 0]]
  ![![61, 0, 0], ![-24, -27, 1]] where
 M := ![![![3721, 0, 0], ![-1403, 61, 0]], ![![-1525, 61, 0], ![575, -47, 4]]]
 hmul := by decide  
 g := ![![![![61, 0, 0], ![0, 0, 0]], ![![1, 28, -1], ![61, 0, 0]]], ![![![-1, 28, -1], ![61, 0, 0]], ![![11, 1, 0], ![4, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-24, -27, 1]] ![![61, 0, 0], ![-14, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-854, 61, 0]], ![![-1464, -1647, 61], ![488, 366, -122]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-14, 1, 0]]], ![![![-24, -27, 1]], ![![8, 6, -2]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![22, 1, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![22, 1, 0]] 
 ![![67, 0, 0], ![22, 1, 0], ![41, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![22, 1, 0], ![0, 23, 4], ![152, 39, 22]]]
  hmulB := by decide  
  f := ![![![925, 42, 0], ![-2814, 0, 0]], ![![286, 13, 0], ![-870, 0, 0]], ![![547, 19, -1], ![-1664, 17, 0]]]
  g := ![![![1, 0, 0], ![-22, 67, 0], ![-41, 0, 67]], ![![0, 1, 0], ![-10, 23, 4], ![-24, 39, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N0 : Nat.card (O ⧸ I67N0) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N0)

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := prime_ideal_of_norm_prime hp67.out _ NI67N0
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![22, 1, 0]] ![![67, 0, 0], ![22, 1, 0]]
  ![![67, 0, 0], ![-13, 28, 1]] where
 M := ![![![4489, 0, 0], ![1474, 67, 0]], ![![1474, 67, 0], ![484, 45, 4]]]
 hmul := by decide  
 g := ![![![![67, 0, 0], ![0, 0, 0]], ![![22, 1, 0], ![0, 0, 0]]], ![![![22, 1, 0], ![0, 0, 0]], ![![8, -1, 0], ![4, 0, 0]]]]
 hle2 := by decide  
def MulI67N1 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![-13, 28, 1]] ![![67, 0, 0], ![22, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![1474, 67, 0]], ![![-871, 1876, 67], ![-134, 670, 134]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![22, 1, 0]]], ![![![-13, 28, 1]], ![![-2, 10, 2]]]]
 hle2 := by decide  

def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N0, I67N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N0
    exact isPrimeI67N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0 ⊙ MulI67N1)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0]] 
 ![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [4, 65, 51, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [64, 9, 15], [27, 61, 56], [0, 1]]
 g := ![![[55, 10, 10], [7, 39, 43], [69, 58, 10], [23, 45], [20, 1], []], ![[30, 55, 12, 30], [23, 10, 14, 19], [15, 50, 32, 19], [25, 32], [15, 29], [13, 12]], ![[45, 16, 43, 59], [19, 2, 58, 7], [37, 28, 48, 62], [58, 9], [11, 10], [43, 12]]]
 h' := ![![[64, 9, 15], [43, 21, 9], [8, 19, 55], [60, 0, 62], [62, 45, 51], [0, 0, 1], [0, 1]], ![[27, 61, 56], [11, 35, 12], [65, 3, 19], [16, 12, 19], [20, 53, 23], [68, 46, 61], [64, 9, 15]], ![[0, 1], [14, 15, 50], [58, 49, 68], [17, 59, 61], [6, 44, 68], [60, 25, 9], [27, 61, 56]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 18], []]
 b := ![[], [23, 12, 13], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [4, 65, 51, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3098440, -1330398, -468671]
  a := ![0, -2, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-43640, -18738, -6601]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 357911 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def PBC71 : ContainsPrimesAboveP 71 ![I71N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![71, 0, 0]]) timesTableT_eq_Table B_one_repr 71 (by decide) 𝕀

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


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [23, 29, 37, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 38, 39], [3, 34, 34], [0, 1]]
 g := ![![[43, 39, 16], [72, 8], [56, 71], [53, 23, 19], [36, 1], []], ![[40, 18, 25, 20], [17, 37], [30, 2], [22, 44, 22, 26], [52, 61], [50, 61]], ![[55, 3, 41, 47], [29, 49], [58, 38], [57, 44, 4, 43], [21, 57], [55, 61]]]
 h' := ![![[33, 38, 39], [24, 15, 4], [72, 61, 9], [22, 19, 61], [48, 28, 26], [0, 0, 1], [0, 1]], ![[3, 34, 34], [56, 66, 64], [3, 16, 57], [67, 44, 41], [43, 51, 5], [12, 20, 34], [33, 38, 39]], ![[0, 1], [9, 65, 5], [47, 69, 7], [40, 10, 44], [34, 67, 42], [58, 53, 38], [3, 34, 34]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32, 19], []]
 b := ![[], [64, 55, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [23, 29, 37, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2312185064, 1037067784, 387874769]
  a := ![1, 20, 61]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![31673768, 14206408, 5313353]
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


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [62, 62, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 52, 45], [73, 26, 34], [0, 1]]
 g := ![![[0, 14, 26], [11, 23, 10], [42, 59, 52], [33, 48, 44], [73, 1], []], ![[74, 57, 29, 13], [59, 70, 73, 67], [62, 33, 7, 36], [70, 43, 43, 22], [63, 44], [35, 50]], ![[62, 42, 52, 24], [51, 20, 58, 57], [16, 77, 54, 68], [35, 32, 9, 71], [28, 18], [46, 50]]]
 h' := ![![[0, 52, 45], [29, 34, 42], [3, 43, 57], [8, 10, 62], [56, 73, 53], [0, 0, 1], [0, 1]], ![[73, 26, 34], [55, 48, 15], [27, 71, 20], [5, 50, 8], [70, 38, 2], [42, 23, 26], [0, 52, 45]], ![[0, 1], [53, 76, 22], [77, 44, 2], [25, 19, 9], [75, 47, 24], [28, 56, 52], [73, 26, 34]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65, 49], []]
 b := ![[], [38, 65, 27], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [62, 62, 6, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1437089, 616674, 220805]
  a := ![-1, 2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![18191, 7806, 2795]
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



lemma PB105I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB105I1 : PrimesBelowBoundCertificateInterval O 31 79 105 where
  m := 11
  g := ![3, 1, 3, 1, 1, 1, 3, 3, 1, 1, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB105I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0]
    · exact ![I43N0, I43N1, I43N2]
    · exact ![I47N0]
    · exact ![I53N0]
    · exact ![I59N0]
    · exact ![I61N0, I61N1, I61N2]
    · exact ![I67N0, I67N0, I67N0]
    · exact ![I71N0]
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
    · exact ![37, 37, 37]
    · exact ![68921]
    · exact ![43, 43, 43]
    · exact ![103823]
    · exact ![148877]
    · exact ![205379]
    · exact ![61, 61, 61]
    · exact ![67, 67, 67]
    · exact ![357911]
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
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N0
      exact NI67N0
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
  β := ![I37N0, I37N1, I37N2, I43N0, I43N1, I43N2, I61N0, I61N1, I61N2, I67N0]
  Il := ![[I37N0, I37N1, I37N2], [], [I43N0, I43N1, I43N2], [], [], [], [I61N0, I61N1, I61N2], [I67N0, I67N0, I67N0], [], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
