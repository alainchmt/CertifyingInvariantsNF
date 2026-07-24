
import IdealArithmetic.Examples.NF3_1_469300_2.RI3_1_469300_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-127, -61, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-127, -61, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![12, 78, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-127, -61, 1], ![380, -32, -61], ![-23180, -5415, -32]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-12, -78, 139]], ![![-1, -1, 1], ![8, 34, -61], ![-164, -21, -32]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [54, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [134, 138], [0, 1]]
 g := ![![[49, 121], [122, 80], [20], [89, 7], [4], [25], [1]], ![[0, 18], [0, 59], [20], [54, 132], [4], [25], [1]]]
 h' := ![![[134, 138], [84, 128], [38, 91], [59, 24], [41, 110], [37, 137], [85, 134], [0, 1]], ![[0, 1], [0, 11], [0, 48], [78, 115], [47, 29], [47, 2], [110, 5], [134, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [107]]
 b := ![[], [99, 123]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [54, 5, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![814, 565, 91]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2, -47, 91]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![61, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![61, 1, 0]] 
 ![![139, 0, 0], ![61, 1, 0], ![32, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![61, 1, 0], ![0, 61, 1], ![380, 95, 61]]]
  hmulB := by decide  
  f := ![![![2807, 46, 0], ![-6394, 0, 0]], ![![1159, 19, 0], ![-2640, 0, 0]], ![![576, 9, 0], ![-1312, 1, 0]]]
  g := ![![![1, 0, 0], ![-61, 139, 0], ![-32, 0, 139]], ![![0, 1, 0], ![-27, 61, 1], ![-53, 95, 61]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![-127, -61, 1]] ![![139, 0, 0], ![61, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![8479, 139, 0]], ![![-17653, -8479, 139], ![-7367, -3753, 0]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![61, 1, 0]]], ![![![-127, -61, 1]], ![![-53, -27, 0]]]]
 hle2 := by decide  


def PBC139 : ContainsPrimesAboveP 139 ![I139N0, I139N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
    exact isPrimeI139N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 139 (by decide) (𝕀 ⊙ MulI139N0)
instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-22, 64, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-22, 64, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![127, 64, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-22, 64, 1], ![380, 73, 64], ![24320, 6460, 73]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-127, -64, 149]], ![![-1, 0, 1], ![-52, -27, 64], ![101, 12, 73]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [110, 119, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 148], [0, 1]]
 g := ![![[81, 42], [26], [110, 16], [76], [117, 20], [6], [1]], ![[0, 107], [26], [143, 133], [76], [121, 129], [6], [1]]]
 h' := ![![[30, 148], [38, 108], [118, 131], [140, 4], [93, 15], [116, 136], [39, 30], [0, 1]], ![[0, 1], [0, 41], [25, 18], [111, 145], [96, 134], [24, 13], [45, 119], [30, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57]]
 b := ![[], [94, 103]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [110, 119, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4568, 2046, 1210]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1062, -506, 1210]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-64, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-64, 1, 0]] 
 ![![149, 0, 0], ![85, 1, 0], ![76, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-64, 1, 0], ![0, -64, 1], ![380, 95, -64]]]
  hmulB := by decide  
  f := ![![![833, -13, 0], ![1937, 0, 0]], ![![513, -8, 0], ![1193, 0, 0]], ![![412, -6, 0], ![958, 1, 0]]]
  g := ![![![1, 0, 0], ![-85, 149, 0], ![-76, 0, 149]], ![![-1, 1, 0], ![36, -64, 1], ![-19, 95, -64]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![-22, 64, 1]] ![![149, 0, 0], ![-64, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![-9536, 149, 0]], ![![-3278, 9536, 149], ![1788, -4023, 0]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![-64, 1, 0]]], ![![![-22, 64, 1]], ![![12, -27, 0]]]]
 hle2 := by decide  


def PBC149 : ContainsPrimesAboveP 149 ![I149N0, I149N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
    exact isPrimeI149N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 149 (by decide) (𝕀 ⊙ MulI149N0)
instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-49, -7, 1]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![-49, -7, 1]] 
 ![![151, 0, 0], ![38, 1, 0], ![66, 0, 1]] where
  M :=![![![-49, -7, 1], ![380, 46, -7], ![-2660, -285, 46]]]
  hmulB := by decide  
  f := ![![![121, 37, 3]], ![![38, 12, 1]], ![![146, 47, 4]]]
  g := ![![![1, -7, 1], ![-6, 46, -7], ![34, -285, 46]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N0 : Nat.card (O ⧸ I151N0) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N0)

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := prime_ideal_of_norm_prime hp151.out _ NI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![43, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![43, 1, 0]] 
 ![![151, 0, 0], ![43, 1, 0], ![114, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![43, 1, 0], ![0, 43, 1], ![380, 95, 43]]]
  hmulB := by decide  
  f := ![![![3011, 70, 0], ![-10570, 0, 0]], ![![817, 19, 0], ![-2868, 0, 0]], ![![2292, 53, 0], ![-8046, 1, 0]]]
  g := ![![![1, 0, 0], ![-43, 151, 0], ![-114, 0, 151]], ![![0, 1, 0], ![-13, 43, 1], ![-57, 95, 43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1

def I151N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![70, 1, 0]] i)))

def SI151N2: IdealEqSpanCertificate' Table ![![151, 0, 0], ![70, 1, 0]] 
 ![![151, 0, 0], ![70, 1, 0], ![83, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![70, 1, 0], ![0, 70, 1], ![380, 95, 70]]]
  hmulB := by decide  
  f := ![![![2171, 31, 0], ![-4681, 0, 0]], ![![1050, 15, 0], ![-2264, 0, 0]], ![![1223, 17, 0], ![-2637, 1, 0]]]
  g := ![![![1, 0, 0], ![-70, 151, 0], ![-83, 0, 151]], ![![0, 1, 0], ![-33, 70, 1], ![-80, 95, 70]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N2 : Nat.card (O ⧸ I151N2) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N2)

lemma isPrimeI151N2 : Ideal.IsPrime I151N2 := prime_ideal_of_norm_prime hp151.out _ NI151N2
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![-49, -7, 1]] ![![151, 0, 0], ![43, 1, 0]]
  ![![151, 0, 0], ![-27, -70, 1]] where
 M := ![![![-7399, -1057, 151], ![-1727, -255, 36]]]
 hmul := by decide  
 g := ![![![![-22, 63, 0], ![151, 0, 0]], ![![-5, 15, 0], ![36, 0, 0]]]]
 hle2 := by decide  

def MulI151N1 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![-27, -70, 1]] ![![151, 0, 0], ![70, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![10570, 151, 0]], ![![-4077, -10570, 151], ![-1510, -4832, 0]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![70, 1, 0]]], ![![![-27, -70, 1]], ![![-10, -32, 0]]]]
 hle2 := by decide  


def PBC151 : ContainsPrimesAboveP 151 ![I151N0, I151N1, I151N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
    exact isPrimeI151N1
    exact isPrimeI151N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 151 (by decide) (𝕀 ⊙ MulI151N0 ⊙ MulI151N1)
instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![23, 1, 0]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![23, 1, 0]] 
 ![![157, 0, 0], ![23, 1, 0], ![99, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![23, 1, 0], ![0, 23, 1], ![380, 95, 23]]]
  hmulB := by decide  
  f := ![![![852, 37, 0], ![-5809, 0, 0]], ![![92, 4, 0], ![-627, 0, 0]], ![![510, 22, 0], ![-3477, 1, 0]]]
  g := ![![![1, 0, 0], ![-23, 157, 0], ![-99, 0, 157]], ![![0, 1, 0], ![-4, 23, 1], ![-26, 95, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N0 : Nat.card (O ⧸ I157N0) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N0)

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := prime_ideal_of_norm_prime hp157.out _ NI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-15, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-15, 1, 0]] 
 ![![157, 0, 0], ![142, 1, 0], ![89, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-15, 1, 0], ![0, -15, 1], ![380, 95, -15]]]
  hmulB := by decide  
  f := ![![![376, -25, 0], ![3925, 0, 0]], ![![346, -23, 0], ![3612, 0, 0]], ![![212, -14, 0], ![2213, 1, 0]]]
  g := ![![![1, 0, 0], ![-142, 157, 0], ![-89, 0, 157]], ![![-1, 1, 0], ![13, -15, 1], ![-75, 95, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1

def I157N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-8, 1, 0]] i)))

def SI157N2: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-8, 1, 0]] 
 ![![157, 0, 0], ![149, 1, 0], ![93, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-8, 1, 0], ![0, -8, 1], ![380, 95, -8]]]
  hmulB := by decide  
  f := ![![![505, -63, 0], ![9891, 0, 0]], ![![481, -60, 0], ![9421, 0, 0]], ![![313, -39, 0], ![6131, 1, 0]]]
  g := ![![![1, 0, 0], ![-149, 157, 0], ![-93, 0, 157]], ![![-1, 1, 0], ![7, -8, 1], ![-83, 95, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N2 : Nat.card (O ⧸ I157N2) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N2)

lemma isPrimeI157N2 : Ideal.IsPrime I157N2 := prime_ideal_of_norm_prime hp157.out _ NI157N2
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![23, 1, 0]] ![![157, 0, 0], ![-15, 1, 0]]
  ![![157, 0, 0], ![-31, 8, 1]] where
 M := ![![![24649, 0, 0], ![-2355, 157, 0]], ![![3611, 157, 0], ![-345, 8, 1]]]
 hmul := by decide  
 g := ![![![![157, 0, 0], ![0, 0, 0]], ![![16, -7, -1], ![157, 0, 0]]], ![![![23, 1, 0], ![0, 0, 0]], ![![-2, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI157N1 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![-31, 8, 1]] ![![157, 0, 0], ![-8, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![-1256, 157, 0]], ![![-4867, 1256, 157], ![628, 0, 0]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![-8, 1, 0]]], ![![![-31, 8, 1]], ![![4, 0, 0]]]]
 hle2 := by decide  


def PBC157 : ContainsPrimesAboveP 157 ![I157N0, I157N1, I157N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
    exact isPrimeI157N1
    exact isPrimeI157N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 157 (by decide) (𝕀 ⊙ MulI157N0 ⊙ MulI157N1)
instance hp163 : Fact (Nat.Prime 163) := {out := by norm_num}

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0]] 
 ![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [101, 60, 56, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 15, 65], [101, 147, 98], [0, 1]]
 g := ![![[100, 1, 100], [152, 138, 38], [], [39, 135], [8, 15], [142, 107, 1], []], ![[74, 129, 103, 49], [2, 117, 127, 36], [124, 126], [83, 62], [17, 34], [22, 124, 10, 14], [70, 150]], ![[144, 6, 26, 98], [34, 49, 58, 42], [5, 126], [20, 160], [111, 84], [54, 63, 16, 45], [37, 150]]]
 h' := ![![[6, 15, 65], [133, 103, 153], [34, 6, 53], [94, 85], [11, 78, 102], [2, 70, 34], [0, 0, 1], [0, 1]], ![[101, 147, 98], [23, 90, 9], [49, 59, 31], [115, 134, 146], [48, 37, 15], [61, 129, 94], [138, 64, 147], [6, 15, 65]], ![[0, 1], [12, 133, 1], [117, 98, 79], [40, 107, 17], [58, 48, 46], [115, 127, 35], [107, 99, 15], [101, 147, 98]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [127, 15], []]
 b := ![[], [90, 142, 75], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [101, 60, 56, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![31133, -66830, -26406]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![191, -410, -162]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 4330747 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def PBC163 : ContainsPrimesAboveP 163 ![I163N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI163N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![163, 0, 0]]) timesTableT_eq_Table B_one_repr 163 (by decide) 𝕀

instance hp167 : Fact (Nat.Prime 167) := {out := by norm_num}

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0]] 
 ![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [77, 80, 66, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 87, 126], [93, 79, 41], [0, 1]]
 g := ![![[104, 98, 108], [164, 121, 58], [56, 94, 57], [155, 14], [83, 97], [101, 101, 1], []], ![[88, 18, 41, 2], [59, 12, 118, 3], [135, 69, 56, 72], [30, 61], [141, 49], [34, 120, 96, 130], [156, 11]], ![[128, 43, 4, 151], [33, 27, 59, 159], [94, 75, 125, 105], [51, 132], [132, 87], [119, 66, 100, 43], [74, 11]]]
 h' := ![![[8, 87, 126], [64, 6, 129], [30, 37, 15], [30, 149, 97], [129, 69, 101], [72, 8, 40], [0, 0, 1], [0, 1]], ![[93, 79, 41], [63, 146, 92], [130, 45, 2], [77, 53, 51], [7, 129, 140], [3, 81, 160], [76, 89, 79], [8, 87, 126]], ![[0, 1], [40, 15, 113], [141, 85, 150], [35, 132, 19], [156, 136, 93], [119, 78, 134], [112, 78, 87], [93, 79, 41]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [154, 100], []]
 b := ![[], [0, 86, 145], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [77, 80, 66, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3080816, -1512185, -175851]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-18448, -9055, -1053]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 4657463 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def PBC167 : ContainsPrimesAboveP 167 ![I167N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI167N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![167, 0, 0]]) timesTableT_eq_Table B_one_repr 167 (by decide) 𝕀

instance hp173 : Fact (Nat.Prime 173) := {out := by norm_num}

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0]] 
 ![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [36, 5, 17, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [169, 130, 153], [160, 42, 20], [0, 1]]
 g := ![![[77, 169, 37], [1, 73], [61, 135, 138], [26, 153, 41], [114, 73], [111, 156, 1], []], ![[5, 42, 56, 97], [42, 47], [11, 166, 41, 171], [149, 5, 113, 46], [155, 51], [67, 40, 170, 12], [110, 54]], ![[78, 18, 159, 162], [144, 96], [95, 26, 29, 115], [22, 171, 93, 53], [86, 89], [62, 71, 51, 131], [70, 54]]]
 h' := ![![[169, 130, 153], [5, 139, 146], [53, 49, 108], [102, 152, 151], [164, 54, 120], [156, 57, 65], [0, 0, 1], [0, 1]], ![[160, 42, 20], [61, 0, 65], [4, 108, 96], [108, 109, 15], [169, 43, 154], [127, 5, 33], [35, 99, 42], [169, 130, 153]], ![[0, 1], [87, 34, 135], [164, 16, 142], [24, 85, 7], [24, 76, 72], [51, 111, 75], [71, 74, 130], [160, 42, 20]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 149], []]
 b := ![[], [43, 3, 68], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [36, 5, 17, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-240124, -90825, -8823]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1388, -525, -51]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 5177717 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def PBC173 : ContainsPrimesAboveP 173 ![I173N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI173N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![173, 0, 0]]) timesTableT_eq_Table B_one_repr 173 (by decide) 𝕀

instance hp179 : Fact (Nat.Prime 179) := {out := by norm_num}

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![-139, -80, 1]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0], ![-139, -80, 1]] 
 ![![179, 0, 0], ![0, 179, 0], ![40, 99, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![-139, -80, 1], ![380, -44, -80], ![-30400, -7220, -44]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-40, -99, 179]], ![![-1, -1, 1], ![20, 44, -80], ![-160, -16, -44]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [14, 34, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [145, 178], [0, 1]]
 g := ![![[28, 64], [134, 25], [146], [70], [41, 76], [133, 82], [1]], ![[0, 115], [0, 154], [146], [70], [142, 103], [30, 97], [1]]]
 h' := ![![[145, 178], [93, 8], [170, 5], [31, 135], [142, 41], [107, 75], [165, 145], [0, 1]], ![[0, 1], [0, 171], [0, 174], [95, 44], [1, 138], [63, 104], [68, 34], [145, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [110]]
 b := ![[], [40, 55]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [14, 34, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![14489, 4674, 492]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-29, -246, 492]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![80, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![80, 1, 0]] 
 ![![179, 0, 0], ![80, 1, 0], ![44, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![80, 1, 0], ![0, 80, 1], ![380, 95, 80]]]
  hmulB := by decide  
  f := ![![![2961, 37, 0], ![-6623, 0, 0]], ![![1200, 15, 0], ![-2684, 0, 0]], ![![676, 8, 0], ![-1512, 1, 0]]]
  g := ![![![1, 0, 0], ![-80, 179, 0], ![-44, 0, 179]], ![![0, 1, 0], ![-36, 80, 1], ![-60, 95, 80]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![-139, -80, 1]] ![![179, 0, 0], ![80, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![14320, 179, 0]], ![![-24881, -14320, 179], ![-10740, -6444, 0]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![80, 1, 0]]], ![![![-139, -80, 1]], ![![-60, -36, 0]]]]
 hle2 := by decide  


def PBC179 : ContainsPrimesAboveP 179 ![I179N0, I179N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI179N0
    exact isPrimeI179N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 179 (by decide) (𝕀 ⊙ MulI179N0)
instance hp181 : Fact (Nat.Prime 181) := {out := by norm_num}

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0]] 
 ![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 3 2 7 [97, 27, 12, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [109, 142, 166], [60, 38, 15], [0, 1]]
 g := ![![[25, 121, 177], [178, 178], [33, 106, 55], [21, 43], [79, 1, 136], [117, 169, 1], []], ![[125, 117, 124, 45], [44, 13], [127, 160, 91, 176], [101, 176], [86, 151, 59, 125], [65, 139, 34, 60], [99, 44]], ![[19, 104, 165, 87], [37, 5], [92, 131, 103, 142], [33, 138], [25, 105, 122, 33], [121, 96, 147, 9], [69, 44]]]
 h' := ![![[109, 142, 166], [101, 30, 143], [57, 178, 97], [55, 79, 69], [120, 143, 62], [54, 177, 90], [0, 0, 1], [0, 1]], ![[60, 38, 15], [67, 129, 97], [57, 102, 111], [52, 157, 170], [16, 58, 30], [108, 4, 41], [106, 123, 38], [109, 142, 166]], ![[0, 1], [156, 22, 122], [135, 82, 154], [71, 126, 123], [106, 161, 89], [3, 0, 50], [165, 58, 142], [60, 38, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45, 118], []]
 b := ![[], [131, 0, 32], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 3
  hpos := by decide
  P := [97, 27, 12, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![170321, -362, -7240]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![941, -2, -40]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 5929741 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def PBC181 : ContainsPrimesAboveP 181 ![I181N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI181N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![181, 0, 0]]) timesTableT_eq_Table B_one_repr 181 (by decide) 𝕀

instance hp191 : Fact (Nat.Prime 191) := {out := by norm_num}

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![259, 22, -4]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![259, 22, -4]] 
 ![![191, 0, 0], ![0, 191, 0], ![174, 90, 1]] where
  M :=![![![259, 22, -4], ![-1520, -121, 22], ![8360, 570, -121]]]
  hmulB := by decide  
  f := ![![![-11, -2, 0]], ![![0, -11, -2]], ![![-14, -8, -1]]]
  g := ![![![5, 2, -4], ![-28, -11, 22], ![154, 60, -121]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [188, 57, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [134, 190], [0, 1]]
 g := ![![[172, 100], [4, 16], [70, 128], [103, 26], [28, 6], [117, 2], [1]], ![[11, 91], [47, 175], [32, 63], [149, 165], [68, 185], [3, 189], [1]]]
 h' := ![![[134, 190], [12, 181], [19, 4], [118, 117], [84, 147], [160, 31], [3, 134], [0, 1]], ![[0, 1], [9, 10], [173, 187], [134, 74], [109, 44], [112, 160], [5, 57], [134, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [146, 109]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [188, 57, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1708, 1957, 495]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-442, -223, 495]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 2, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![11, 2, 0]] 
 ![![191, 0, 0], ![101, 1, 0], ![113, 0, 1]] where
  M :=![![![11, 2, 0], ![0, 11, 2], ![760, 190, 11]]]
  hmulB := by decide  
  f := ![![![-259, -22, 4]], ![![-129, -11, 2]], ![![-197, -16, 3]]]
  g := ![![![-1, 2, 0], ![-7, 11, 2], ![-103, 190, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![259, 22, -4]] ![![11, 2, 0]]
  ![![191, 0, 0]] where
 M := ![![![-191, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC191 : ContainsPrimesAboveP 191 ![I191N0, I191N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI191N0
    exact isPrimeI191N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 191 (by decide) (𝕀 ⊙ MulI191N0)
instance hp193 : Fact (Nat.Prime 193) := {out := by norm_num}

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-36, -32, 1]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-36, -32, 1]] 
 ![![193, 0, 0], ![0, 193, 0], ![157, 161, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-36, -32, 1], ![380, 59, -32], ![-12160, -2660, 59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-157, -161, 193]], ![![-1, -1, 1], ![28, 27, -32], ![-111, -63, 59]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [1, 54, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [139, 192], [0, 1]]
 g := ![![[54, 1], [162], [59], [131], [107], [14], [139, 1]], ![[0, 192], [162], [59], [131], [107], [14], [85, 192]]]
 h' := ![![[139, 192], [54, 1], [122, 111], [145, 32], [135, 175], [7, 53], [54, 20], [0, 1]], ![[0, 1], [0, 192], [111, 82], [154, 161], [142, 18], [40, 140], [132, 173], [139, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [136]]
 b := ![[], [99, 68]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [1, 54, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-15087, -2860, 596]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-563, -512, 596]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![32, 1, 0]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![193, 0, 0], ![32, 1, 0]] 
 ![![193, 0, 0], ![32, 1, 0], ![134, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![32, 1, 0], ![0, 32, 1], ![380, 95, 32]]]
  hmulB := by decide  
  f := ![![![4065, 127, 0], ![-24511, 0, 0]], ![![672, 21, 0], ![-4052, 0, 0]], ![![2822, 88, 0], ![-17016, 1, 0]]]
  g := ![![![1, 0, 0], ![-32, 193, 0], ![-134, 0, 193]], ![![0, 1, 0], ![-6, 32, 1], ![-36, 95, 32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![-36, -32, 1]] ![![193, 0, 0], ![32, 1, 0]]
  ![![193, 0, 0]] where
 M := ![![![37249, 0, 0], ![6176, 193, 0]], ![![-6948, -6176, 193], ![-772, -965, 0]]]
 hmul := by decide  
 g := ![![![![193, 0, 0]], ![![32, 1, 0]]], ![![![-36, -32, 1]], ![![-4, -5, 0]]]]
 hle2 := by decide  


def PBC193 : ContainsPrimesAboveP 193 ![I193N0, I193N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI193N0
    exact isPrimeI193N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 193 (by decide) (𝕀 ⊙ MulI193N0)


lemma PB194I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB194I3 : PrimesBelowBoundCertificateInterval O 137 193 194 where
  m := 11
  g := ![2, 2, 3, 3, 1, 1, 1, 2, 1, 2, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB194I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1]
    · exact ![I151N0, I151N1, I151N2]
    · exact ![I157N0, I157N1, I157N2]
    · exact ![I163N0]
    · exact ![I167N0]
    · exact ![I173N0]
    · exact ![I179N0, I179N1]
    · exact ![I181N0]
    · exact ![I191N0, I191N1]
    · exact ![I193N0, I193N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC139
    · exact PBC149
    · exact PBC151
    · exact PBC157
    · exact PBC163
    · exact PBC167
    · exact PBC173
    · exact PBC179
    · exact PBC181
    · exact PBC191
    · exact PBC193
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![19321, 139]
    · exact ![22201, 149]
    · exact ![151, 151, 151]
    · exact ![157, 157, 157]
    · exact ![4330747]
    · exact ![4657463]
    · exact ![5177717]
    · exact ![32041, 179]
    · exact ![5929741]
    · exact ![36481, 191]
    · exact ![37249, 193]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
      exact NI139N1
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
      exact NI151N2
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
      exact NI157N1
      exact NI157N2
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
      exact NI179N1
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
  β := ![I139N1, I149N1, I151N0, I151N1, I151N2, I157N0, I157N1, I157N2, I179N1, I191N1, I193N1]
  Il := ![[I139N1], [I149N1], [I151N0, I151N1, I151N2], [I157N0, I157N1, I157N2], [], [], [], [I179N1], [], [I191N1], [I193N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
