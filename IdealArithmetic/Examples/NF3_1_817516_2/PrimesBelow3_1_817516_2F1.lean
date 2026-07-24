
import IdealArithmetic.Examples.NF3_1_817516_2.RI3_1_817516_2
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [2, 2, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 26, 22], [31, 10, 15], [0, 1]]
 g := ![![[2, 2, 12], [32, 25], [30, 25, 21], [27, 1], []], ![[9, 7, 13, 2], [10, 9], [21, 29, 32, 5], [36, 26], [4, 3]], ![[25, 28, 35, 8], [16, 4], [17, 29, 17, 22], [11, 10], [11, 3]]]
 h' := ![![[33, 26, 22], [21, 14, 7], [14, 31, 32], [20, 18, 24], [0, 0, 1], [0, 1]], ![[31, 10, 15], [21, 31, 8], [35, 29, 3], [29, 24, 7], [8, 0, 10], [33, 26, 22]], ![[0, 1], [35, 29, 22], [17, 14, 2], [26, 32, 6], [14, 0, 26], [31, 10, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 16], []]
 b := ![[], [17, 2, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [2, 2, 10, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1662262, -74222, 35224]
  a := ![-3, -4, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-44926, -2006, 952]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-5, -20, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-5, -20, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![36, 21, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-5, -20, 1], ![-233, -71, -142], ![3581, 97, 30]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-36, -21, 41]], ![![-1, -1, 1], ![119, 71, -142], ![61, -13, 30]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [2, 28, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 40], [0, 1]]
 g := ![![[14, 21], [2], [1], [13, 5], [1]], ![[0, 20], [2], [1], [37, 36], [1]]]
 h' := ![![[13, 40], [33, 29], [18, 24], [15, 40], [39, 13], [0, 1]], ![[0, 1], [0, 12], [2, 17], [2, 1], [3, 28], [13, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [23, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [2, 28, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4635, -9299, -1173]
  a := ![8, 6, 19]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1143, 374, -1173]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![19, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![19, 1, 0]] 
 ![![41, 0, 0], ![19, 1, 0], ![11, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![19, 1, 0], ![3, 22, 7], ![-173, -6, 17]]]
  hmulB := by decide  
  f := ![![![-864, -8280, -2639], ![-574, 15457, 0]], ![![-408, -3822, -1218], ![-245, 7134, 0]], ![![-242, -2222, -708], ![-132, 4147, 0]]]
  g := ![![![1, 0, 0], ![-19, 41, 0], ![-11, 0, 41]], ![![0, 1, 0], ![-12, 22, 7], ![-6, -6, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-5, -20, 1]] ![![41, 0, 0], ![19, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![779, 41, 0]], ![![-205, -820, 41], ![-328, -451, -123]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![19, 1, 0]]], ![![![-5, -20, 1]], ![![-8, -11, -3]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![17, 1, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![17, 1, 0]] 
 ![![43, 0, 0], ![17, 1, 0], ![1, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![17, 1, 0], ![3, 20, 7], ![-173, -6, 15]]]
  hmulB := by decide  
  f := ![![![1468, 12139, 4256], ![903, -26144, 0]], ![![584, 4792, 1680], ![345, -10320, 0]], ![![29, 282, 99], ![34, -608, 0]]]
  g := ![![![1, 0, 0], ![-17, 43, 0], ![-1, 0, 43]], ![![0, 1, 0], ![-8, 20, 7], ![-2, -6, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N0)

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := prime_ideal_of_norm_prime hp43.out _ NI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-9, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-9, 1, 0]] 
 ![![43, 0, 0], ![34, 1, 0], ![5, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-9, 1, 0], ![3, -6, 7], ![-173, -6, -11]]]
  hmulB := by decide  
  f := ![![![820, -1706, 1995], ![-172, -12255, 0]], ![![649, -1347, 1575], ![-128, -9675, 0]], ![![101, -199, 232], ![7, -1425, 0]]]
  g := ![![![1, 0, 0], ![-34, 43, 0], ![-5, 0, 43]], ![![-1, 1, 0], ![4, -6, 7], ![2, -6, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![17, 1, 0]] ![![43, 0, 0], ![-9, 1, 0]]
  ![![43, 0, 0], ![-3, 20, 1]] where
 M := ![![![1849, 0, 0], ![-387, 43, 0]], ![![731, 43, 0], ![-150, 11, 7]]]
 hmul := by decide  
 g := ![![![![43, 0, 0], ![0, 0, 0]], ![![-6, -19, -1], ![43, 0, 0]]], ![![![17, 1, 0], ![0, 0, 0]], ![![-3, -3, 0], ![7, 0, 0]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-3, 20, 1]] ![![43, 0, 0], ![-9, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-387, 43, 0]], ![![-129, 860, 43], ![-86, -129, 129]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-9, 1, 0]]], ![![![-3, 20, 1]], ![![-2, -3, 3]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0]] 
 ![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [28, 2, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 42, 18], [29, 4, 29], [0, 1]]
 g := ![![[23, 41, 2], [16, 41, 17], [1, 36, 42], [14, 43, 1], []], ![[32, 31, 11, 21], [46, 36, 35, 6], [35, 20, 43, 3], [27, 38, 10, 6], [28, 42]], ![[46, 16, 37, 41], [36, 44, 45, 41], [5, 0, 31, 41], [4, 9, 42, 20], [17, 42]]]
 h' := ![![[14, 42, 18], [22, 27, 7], [19, 45, 8], [31, 37, 18], [0, 0, 1], [0, 1]], ![[29, 4, 29], [44, 37, 44], [34, 32, 43], [23, 29, 33], [23, 38, 4], [14, 42, 18]], ![[0, 1], [23, 30, 43], [14, 17, 43], [13, 28, 43], [36, 9, 42], [29, 4, 29]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 9], []]
 b := ![[], [33, 16, 23], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [28, 2, 4, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11236755112, -493750134, 154745244]
  a := ![-67, -66, -135]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-239079896, -10505322, 3292452]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![13, 1, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![13, 1, 0]] 
 ![![53, 0, 0], ![13, 1, 0], ![1, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![13, 1, 0], ![3, 16, 7], ![-173, -6, 11]]]
  hmulB := by decide  
  f := ![![![4864, 28191, 12348], ![1749, -93492, 0]], ![![1192, 6904, 3024], ![425, -22896, 0]], ![![80, 531, 233], ![81, -1764, 0]]]
  g := ![![![1, 0, 0], ![-13, 53, 0], ![-1, 0, 53]], ![![0, 1, 0], ![-4, 16, 7], ![-2, -6, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N0 : Nat.card (O ⧸ I53N0) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N0)

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := prime_ideal_of_norm_prime hp53.out _ NI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![17, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![17, 1, 0]] 
 ![![53, 0, 0], ![17, 1, 0], ![20, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![17, 1, 0], ![3, 20, 7], ![-173, -6, 15]]]
  hmulB := by decide  
  f := ![![![1696, 12985, 4550], ![795, -34450, 0]], ![![539, 4155, 1456], ![266, -11024, 0]], ![![640, 4900, 1717], ![300, -13000, 0]]]
  g := ![![![1, 0, 0], ![-17, 53, 0], ![-20, 0, 53]], ![![0, 1, 0], ![-9, 20, 7], ![-7, -6, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1

def I53N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![22, 1, 0]] i)))

def SI53N2: IdealEqSpanCertificate' Table ![![53, 0, 0], ![22, 1, 0]] 
 ![![53, 0, 0], ![22, 1, 0], ![43, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![22, 1, 0], ![3, 25, 7], ![-173, -6, 20]]]
  hmulB := by decide  
  f := ![![![1955, 20477, 5740], ![1219, -43460, 0]], ![![800, 8490, 2380], ![531, -18020, 0]], ![![1577, 16613, 4657], ![1011, -35260, 0]]]
  g := ![![![1, 0, 0], ![-22, 53, 0], ![-43, 0, 53]], ![![0, 1, 0], ![-16, 25, 7], ![-17, -6, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N2 : Nat.card (O ⧸ I53N2) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N2)

lemma isPrimeI53N2 : Ideal.IsPrime I53N2 := prime_ideal_of_norm_prime hp53.out _ NI53N2
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![13, 1, 0]] ![![53, 0, 0], ![17, 1, 0]]
  ![![53, 0, 0], ![-21, -18, 1]] where
 M := ![![![2809, 0, 0], ![901, 53, 0]], ![![689, 53, 0], ![224, 33, 7]]]
 hmul := by decide  
 g := ![![![![53, 0, 0], ![0, 0, 0]], ![![17, 1, 0], ![0, 0, 0]]], ![![![13, 1, 0], ![0, 0, 0]], ![![7, 3, 0], ![7, 0, 0]]]]
 hle2 := by decide  

def MulI53N1 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![-21, -18, 1]] ![![53, 0, 0], ![22, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![1166, 53, 0]], ![![-1113, -954, 53], ![-689, -477, -106]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![22, 1, 0]]], ![![![-21, -18, 1]], ![![-13, -9, -2]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![29, -5, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![29, -5, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![29, 54, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![29, -5, 1], ![-188, 8, -37], ![986, 7, 34]]]
  hmulB := by decide  
  f := ![![![-28, 5, -1], ![59, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-29, -54, 59]], ![![0, -1, 1], ![15, 34, -37], ![0, -31, 34]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [53, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [42, 58], [0, 1]]
 g := ![![[7, 49], [49, 48], [46], [], [42, 1]], ![[0, 10], [0, 11], [46], [], [25, 58]]]
 h' := ![![[42, 58], [58, 52], [40, 44], [0, 20], [16], [0, 1]], ![[0, 1], [0, 7], [0, 15], [14, 39], [16], [42, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [22, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [53, 17, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2209, -9759, -2013]
  a := ![-8, -7, -19]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![952, 1677, -2013]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-22, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-22, 1, 0]] 
 ![![59, 0, 0], ![37, 1, 0], ![25, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-22, 1, 0], ![3, -19, 7], ![-173, -6, -24]]]
  hmulB := by decide  
  f := ![![![-219, 1670, -616], ![118, 5192, 0]], ![![-120, 1043, -385], ![119, 3245, 0]], ![![-79, 707, -261], ![87, 2200, 0]]]
  g := ![![![1, 0, 0], ![-37, 59, 0], ![-25, 0, 59]], ![![-1, 1, 0], ![9, -19, 7], ![11, -6, -24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![29, -5, 1]] ![![59, 0, 0], ![-22, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-1298, 59, 0]], ![![1711, -295, 59], ![-826, 118, -59]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-22, 1, 0]]], ![![![29, -5, 1]], ![![-14, 2, -1]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![24, -10, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![24, -10, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![24, 51, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![24, -10, 1], ![-203, -12, -72], ![1851, 37, 39]]]
  hmulB := by decide  
  f := ![![![-23, 10, -1], ![61, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-24, -51, 61]], ![![0, -1, 1], ![25, 60, -72], ![15, -32, 39]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [29, 9, 1] where
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
 g := ![![[55, 12], [34], [15, 16], [2, 20], [52, 1]], ![[8, 49], [34], [54, 45], [5, 41], [43, 60]]]
 h' := ![![[52, 60], [54, 45], [53, 20], [3, 57], [17, 52], [0, 1]], ![[0, 1], [15, 16], [56, 41], [39, 4], [37, 9], [52, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [2, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [29, 9, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3700, -1427, -266]
  a := ![-3, -4, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![44, 199, -266]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![11, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![11, 1, 0]] 
 ![![61, 0, 0], ![11, 1, 0], ![22, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![11, 1, 0], ![3, 14, 7], ![-173, -6, 9]]]
  hmulB := by decide  
  f := ![![![1863, 9092, 4550], ![488, -39650, 0]], ![![329, 1636, 819], ![123, -7137, 0]], ![![671, 3279, 1641], ![181, -14300, 0]]]
  g := ![![![1, 0, 0], ![-11, 61, 0], ![-22, 0, 61]], ![![0, 1, 0], ![-5, 14, 7], ![-5, -6, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![24, -10, 1]] ![![61, 0, 0], ![11, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![671, 61, 0]], ![![1464, -610, 61], ![61, -122, -61]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![11, 1, 0]]], ![![![24, -10, 1]], ![![1, -2, -1]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![20, -22, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![20, -22, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![20, 45, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![20, -22, 1], ![-239, -52, -156], ![3927, 109, 59]]]
  hmulB := by decide  
  f := ![![![-19, 22, -1], ![67, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-20, -45, 67]], ![![0, -1, 1], ![43, 104, -156], ![41, -38, 59]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [59, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [41, 66], [0, 1]]
 g := ![![[47, 25], [33, 9], [26], [23], [6], [1]], ![[0, 42], [0, 58], [26], [23], [6], [1]]]
 h' := ![![[41, 66], [63, 5], [11, 3], [65, 48], [45, 31], [8, 41], [0, 1]], ![[0, 1], [0, 62], [0, 64], [23, 19], [43, 36], [14, 26], [41, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [24, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [59, 26, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-60055, -1978, 2776]
  a := ![4, 23, 9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1725, -1894, 2776]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![22, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![22, 1, 0]] 
 ![![67, 0, 0], ![22, 1, 0], ![8, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![22, 1, 0], ![3, 25, 7], ![-173, -6, 20]]]
  hmulB := by decide  
  f := ![![![319, 3197, 896], ![201, -8576, 0]], ![![104, 1049, 294], ![68, -2814, 0]], ![![22, 381, 107], ![73, -1024, 0]]]
  g := ![![![1, 0, 0], ![-22, 67, 0], ![-8, 0, 67]], ![![0, 1, 0], ![-9, 25, 7], ![-3, -6, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![20, -22, 1]] ![![67, 0, 0], ![22, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![1474, 67, 0]], ![![1340, -1474, 67], ![201, -536, -134]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![22, 1, 0]]], ![![![20, -22, 1]], ![![3, -8, -2]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![24, 1, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![24, 1, 0]] 
 ![![71, 0, 0], ![24, 1, 0], ![60, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![24, 1, 0], ![3, 27, 7], ![-173, -6, 22]]]
  hmulB := by decide  
  f := ![![![13, 323, 84], ![71, -852, 0]], ![![-12, 107, 28], ![72, -284, 0]], ![![12, 273, 71], ![57, -720, 0]]]
  g := ![![![1, 0, 0], ![-24, 71, 0], ![-60, 0, 71]], ![![0, 1, 0], ![-15, 27, 7], ![-19, -6, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N0 : Nat.card (O ⧸ I71N0) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N0)

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := prime_ideal_of_norm_prime hp71.out _ NI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-17, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-17, 1, 0]] 
 ![![71, 0, 0], ![54, 1, 0], ![7, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-17, 1, 0], ![3, -14, 7], ![-173, -6, -19]]]
  hmulB := by decide  
  f := ![![![4686, -23430, 11725], ![-1420, -118925, 0]], ![![3565, -17807, 8911], ![-1064, -90383, 0]], ![![462, -2310, 1156], ![-140, -11725, 0]]]
  g := ![![![1, 0, 0], ![-54, 71, 0], ![-7, 0, 71]], ![![-1, 1, 0], ![10, -14, 7], ![4, -6, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-8, 1, 0]] i)))

def SI71N2: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-8, 1, 0]] 
 ![![71, 0, 0], ![63, 1, 0], ![15, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-8, 1, 0], ![3, -5, 7], ![-173, -6, -10]]]
  hmulB := by decide  
  f := ![![![7701, -13006, 18228], ![-994, -184884, 0]], ![![6827, -11537, 16170], ![-922, -164010, 0]], ![![1629, -2748, 3851], ![-192, -39060, 0]]]
  g := ![![![1, 0, 0], ![-63, 71, 0], ![-15, 0, 71]], ![![-1, 1, 0], ![3, -5, 7], ![5, -6, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![24, 1, 0]] ![![71, 0, 0], ![-17, 1, 0]]
  ![![71, 0, 0], ![3, -29, 1]] where
 M := ![![![5041, 0, 0], ![-1207, 71, 0]], ![![1704, 71, 0], ![-405, 10, 7]]]
 hmul := by decide  
 g := ![![![![68, 29, -1], ![71, 0, 0]], ![![-17, 1, 0], ![0, 0, 0]]], ![![![21, 30, -1], ![71, 0, 0]], ![![-6, 3, 0], ![7, 0, 0]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![3, -29, 1]] ![![71, 0, 0], ![-8, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-568, 71, 0]], ![![213, -2059, 71], ![-284, 142, -213]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-8, 1, 0]]], ![![![3, -29, 1]], ![![-4, 2, -3]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![5, 20, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![5, 20, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![5, 20, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![5, 20, 1], ![-113, 59, 138], ![-3339, -143, -40]]]
  hmulB := by decide  
  f := ![![![-4, -20, -1], ![73, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-5, -20, 73]], ![![0, 0, 1], ![-11, -37, 138], ![-43, 9, -40]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [15, 59, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 72], [0, 1]]
 g := ![![[38, 24], [3], [71], [16, 71], [50], [1]], ![[9, 49], [3], [71], [61, 2], [50], [1]]]
 h' := ![![[14, 72], [22, 43], [33, 52], [52, 12], [59, 61], [58, 14], [0, 1]], ![[0, 1], [40, 30], [31, 21], [1, 61], [37, 12], [35, 59], [14, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [57, 44]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [15, 59, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6485, -2019, -893]
  a := ![-4, -1, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![150, 217, -893]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![8, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![8, 1, 0]] 
 ![![73, 0, 0], ![8, 1, 0], ![40, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![8, 1, 0], ![3, 11, 7], ![-173, -6, 6]]]
  hmulB := by decide  
  f := ![![![4713, 17589, 11200], ![803, -116800, 0]], ![![509, 1923, 1225], ![147, -12775, 0]], ![![2584, 9638, 6137], ![426, -64000, 0]]]
  g := ![![![1, 0, 0], ![-8, 73, 0], ![-40, 0, 73]], ![![0, 1, 0], ![-5, 11, 7], ![-5, -6, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![5, 20, 1]] ![![73, 0, 0], ![8, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![584, 73, 0]], ![![365, 1460, 73], ![-73, 219, 146]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![8, 1, 0]]], ![![![5, 20, 1]], ![![-1, 3, 2]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0]] 
 ![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [53, 74, 50, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [75, 8, 15], [33, 70, 64], [0, 1]]
 g := ![![[12, 54, 9], [22, 38, 16], [65, 9, 21], [45, 49, 55], [29, 1], []], ![[30, 57, 70, 37], [25, 41, 68, 53], [36, 19, 49, 7], [9, 21, 61, 24], [35, 2], [50, 67]], ![[11, 17, 76, 11], [51, 9, 68, 21], [41, 35, 14, 44], [69, 75, 16, 31], [1, 64], [1, 67]]]
 h' := ![![[75, 8, 15], [19, 5, 3], [31, 73, 75], [64, 30, 69], [43, 13, 56], [0, 0, 1], [0, 1]], ![[33, 70, 64], [76, 57, 48], [5, 61, 25], [56, 78, 66], [59, 0, 7], [52, 32, 70], [75, 8, 15]], ![[0, 1], [53, 17, 28], [34, 24, 58], [16, 50, 23], [28, 66, 16], [9, 47, 8], [33, 70, 64]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28, 17], []]
 b := ![[], [35, 54, 41], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [53, 74, 50, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![12116783, 282030, -229495]
  a := ![6, 7, 14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![153377, 3570, -2905]
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



lemma PB256I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB256I1 : PrimesBelowBoundCertificateInterval O 31 79 256 where
  m := 11
  g := ![1, 2, 3, 1, 3, 2, 2, 2, 3, 2, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB256I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1, I43N1]
    · exact ![I47N0]
    · exact ![I53N0, I53N1, I53N2]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1, I71N2]
    · exact ![I73N0, I73N1]
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
    · exact ![1681, 41]
    · exact ![43, 43, 43]
    · exact ![103823]
    · exact ![53, 53, 53]
    · exact ![3481, 59]
    · exact ![3721, 61]
    · exact ![4489, 67]
    · exact ![71, 71, 71]
    · exact ![5329, 73]
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
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
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
      exact NI61N1
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
      exact NI71N2
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
  β := ![I41N1, I43N0, I43N1, I53N0, I53N1, I53N2, I59N1, I61N1, I67N1, I71N0, I71N1, I71N2, I73N1]
  Il := ![[], [I41N1], [I43N0, I43N1, I43N1], [], [I53N0, I53N1, I53N2], [I59N1], [I61N1], [I67N1], [I71N0, I71N1, I71N2], [I73N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
