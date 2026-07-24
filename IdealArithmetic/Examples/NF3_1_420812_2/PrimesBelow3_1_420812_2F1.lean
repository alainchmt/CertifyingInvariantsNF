
import IdealArithmetic.Examples.NF3_1_420812_2.RI3_1_420812_2
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [35, 8, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 3, 34], [16, 33, 3], [0, 1]]
 g := ![![[29, 31, 12], [1, 11], [10, 5, 27], [0, 1], []], ![[27, 26, 7, 36], [21, 36], [14, 17, 25, 7], [27, 16], [19, 9]], ![[19, 2, 31, 25], [8, 30], [1, 27, 5, 10], [11, 9], [13, 9]]]
 h' := ![![[21, 3, 34], [32, 26, 7], [20, 4, 14], [0, 2, 29], [0, 0, 1], [0, 1]], ![[16, 33, 3], [9, 22, 5], [2, 11, 6], [21, 33, 26], [35, 29, 33], [21, 3, 34]], ![[0, 1], [17, 26, 25], [36, 22, 17], [33, 2, 19], [23, 8, 3], [16, 33, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21, 29], []]
 b := ![[], [32, 34, 22], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [35, 8, 0, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5069, -27676, -9472]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-137, -748, -256]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![18, 3, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![18, 3, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![18, 3, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![18, 3, 1], ![3, -20, 7], ![-19, -133, -17]]]
  hmulB := by decide  
  f := ![![![-17, -3, -1], ![41, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-18, -3, 41]], ![![0, 0, 1], ![-3, -1, 7], ![7, -2, -17]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [27, 33, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 40], [0, 1]]
 g := ![![[24, 23], [36], [18], [39, 23], [1]], ![[3, 18], [36], [18], [18, 18], [1]]]
 h' := ![![[8, 40], [10, 33], [11, 35], [13, 10], [14, 8], [0, 1]], ![[0, 1], [28, 8], [4, 6], [11, 31], [37, 33], [8, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [11, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [27, 33, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-374, 211, -777]
  a := ![2, -2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![332, 62, -777]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-7, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-7, 1, 0]] 
 ![![41, 0, 0], ![34, 1, 0], ![17, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-7, 1, 0], ![1, -7, 2], ![0, -38, -6]]]
  hmulB := by decide  
  f := ![![![1324, -9789, 2800], ![-451, -57400, 0]], ![![1098, -8111, 2320], ![-368, -47560, 0]], ![![550, -4059, 1161], ![-181, -23800, 0]]]
  g := ![![![1, 0, 0], ![-34, 41, 0], ![-17, 0, 41]], ![![-1, 1, 0], ![5, -7, 2], ![34, -38, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![18, 3, 1]] ![![41, 0, 0], ![-7, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-287, 41, 0]], ![![738, 123, 41], ![-123, -41, 0]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-7, 1, 0]]], ![![![18, 3, 1]], ![![-3, -1, 0]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![7, 16, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![7, 16, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![7, 16, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![7, 16, 1], ![16, -31, 33], ![-19, -627, -15]]]
  hmulB := by decide  
  f := ![![![-6, -16, -1], ![43, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-7, -16, 43]], ![![0, 0, 1], ![-5, -13, 33], ![2, -9, -15]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [10, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 42], [0, 1]]
 g := ![![[35, 13], [31, 41], [10], [33, 36], [1]], ![[0, 30], [0, 2], [10], [32, 7], [1]]]
 h' := ![![[37, 42], [34, 20], [10, 16], [14, 15], [33, 37], [0, 1]], ![[0, 1], [0, 23], [0, 27], [10, 28], [26, 6], [37, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [23, 22]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [10, 6, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-78918, -77872, -157474]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![23800, 56784, -157474]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![10, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![10, 1, 0]] 
 ![![43, 0, 0], ![10, 1, 0], ![15, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![10, 1, 0], ![1, 10, 2], ![0, -38, 11]]]
  hmulB := by decide  
  f := ![![![-346, -3767, -754], ![-129, 16211, 0]], ![![-87, -870, -174], ![1, 3741, 0]], ![![-120, -1314, -263], ![-48, 5655, 0]]]
  g := ![![![1, 0, 0], ![-10, 43, 0], ![-15, 0, 43]], ![![0, 1, 0], ![-3, 10, 2], ![5, -38, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![7, 16, 1]] ![![43, 0, 0], ![10, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![430, 43, 0]], ![![301, 688, 43], ![86, 129, 43]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![10, 1, 0]]], ![![![7, 16, 1]], ![![2, 3, 1]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![27, 19, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![27, 19, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![27, 19, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![27, 19, 1], ![19, -11, 39], ![-19, -741, 8]]]
  hmulB := by decide  
  f := ![![![-26, -19, -1], ![47, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-27, -19, 47]], ![![0, 0, 1], ![-22, -16, 39], ![-5, -19, 8]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [38, 45, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 46], [0, 1]]
 g := ![![[42, 12], [45, 42], [36, 7], [44, 4], [1]], ![[19, 35], [35, 5], [3, 40], [5, 43], [1]]]
 h' := ![![[2, 46], [29, 23], [42, 18], [20, 17], [9, 2], [0, 1]], ![[0, 1], [28, 24], [31, 29], [7, 30], [13, 45], [2, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [40, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [38, 45, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-522, -54, -1163]
  a := ![-2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![657, 469, -1163]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![8, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![8, 1, 0]] 
 ![![47, 0, 0], ![8, 1, 0], ![39, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![8, 1, 0], ![1, 8, 2], ![0, -38, 9]]]
  hmulB := by decide  
  f := ![![![129, 1150, 288], ![94, -6768, 0]], ![![16, 191, 48], ![48, -1128, 0]], ![![113, 955, 239], ![43, -5616, 0]]]
  g := ![![![1, 0, 0], ![-8, 47, 0], ![-39, 0, 47]], ![![0, 1, 0], ![-3, 8, 2], ![-1, -38, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![27, 19, 1]] ![![47, 0, 0], ![8, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![376, 47, 0]], ![![1269, 893, 47], ![235, 141, 47]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![8, 1, 0]]], ![![![27, 19, 1]], ![![5, 3, 1]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![30, -5, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![30, -5, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![30, 48, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![30, -5, 1], ![-5, -8, -9], ![-19, 171, -13]]]
  hmulB := by decide  
  f := ![![![-29, 5, -1], ![53, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-30, -48, 53]], ![![0, -1, 1], ![5, 8, -9], ![7, 15, -13]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [49, 45, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 52], [0, 1]]
 g := ![![[2, 13], [24], [44, 16], [13], [8, 1]], ![[0, 40], [24], [13, 37], [13], [16, 52]]]
 h' := ![![[8, 52], [14, 38], [17, 36], [16, 4], [32, 15], [0, 1]], ![[0, 1], [0, 15], [40, 17], [48, 49], [46, 38], [8, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45]]
 b := ![[], [16, 49]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [49, 45, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-70, -271, -232]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![130, 205, -232]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![9, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![9, 1, 0]] 
 ![![53, 0, 0], ![9, 1, 0], ![13, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![9, 1, 0], ![1, 9, 2], ![0, -38, 10]]]
  hmulB := by decide  
  f := ![![![100, 971, 216], ![53, -5724, 0]], ![![9, 161, 36], ![54, -954, 0]], ![![23, 238, 53], ![22, -1404, 0]]]
  g := ![![![1, 0, 0], ![-9, 53, 0], ![-13, 0, 53]], ![![0, 1, 0], ![-2, 9, 2], ![4, -38, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![30, -5, 1]] ![![53, 0, 0], ![9, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![477, 53, 0]], ![![1590, -265, 53], ![265, -53, 0]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![9, 1, 0]]], ![![![30, -5, 1]], ![![5, -1, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-29, 1, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-29, 1, 0]] 
 ![![59, 0, 0], ![30, 1, 0], ![52, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-29, 1, 0], ![1, -29, 2], ![0, -38, -28]]]
  hmulB := by decide  
  f := ![![![-21, 2318, -160], ![118, 4720, 0]], ![![-10, 1159, -80], ![60, 2360, 0]], ![![-19, 2043, -141], ![103, 4160, 0]]]
  g := ![![![1, 0, 0], ![-30, 59, 0], ![-52, 0, 59]], ![![-1, 1, 0], ![13, -29, 2], ![44, -38, -28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N0 : Nat.card (O ⧸ I59N0) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N0)

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := prime_ideal_of_norm_prime hp59.out _ NI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-17, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-17, 1, 0]] 
 ![![59, 0, 0], ![42, 1, 0], ![33, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-17, 1, 0], ![1, -17, 2], ![0, -38, -16]]]
  hmulB := by decide  
  f := ![![![2349, -46828, 5512], ![-1416, -162604, 0]], ![![1673, -33320, 3922], ![-1002, -115699, 0]], ![![1315, -26192, 3083], ![-788, -90948, 0]]]
  g := ![![![1, 0, 0], ![-42, 59, 0], ![-33, 0, 59]], ![![-1, 1, 0], ![11, -17, 2], ![36, -38, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-14, 1, 0]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-14, 1, 0]] 
 ![![59, 0, 0], ![45, 1, 0], ![50, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-14, 1, 0], ![1, -14, 2], ![0, -38, -13]]]
  hmulB := by decide  
  f := ![![![-496, 7933, -1134], ![295, 33453, 0]], ![![-375, 6044, -864], ![237, 25488, 0]], ![![-422, 6723, -961], ![243, 28350, 0]]]
  g := ![![![1, 0, 0], ![-45, 59, 0], ![-50, 0, 59]], ![![-1, 1, 0], ![9, -14, 2], ![40, -38, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-29, 1, 0]] ![![59, 0, 0], ![-17, 1, 0]]
  ![![59, 0, 0], ![11, -23, 1]] where
 M := ![![![3481, 0, 0], ![-1003, 59, 0]], ![![-1711, 59, 0], ![494, -46, 2]]]
 hmul := by decide  
 g := ![![![![48, 23, -1], ![59, 0, 0]], ![![-17, 1, 0], ![0, 0, 0]]], ![![![-29, 1, 0], ![0, 0, 0]], ![![8, 0, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![11, -23, 1]] ![![59, 0, 0], ![-14, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-826, 59, 0]], ![![649, -1357, 59], ![-177, 295, -59]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-14, 1, 0]]], ![![![11, -23, 1]], ![![-3, 5, -1]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![16, 1, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![16, 1, 0]] 
 ![![61, 0, 0], ![16, 1, 0], ![25, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![16, 1, 0], ![1, 16, 2], ![0, -38, 17]]]
  hmulB := by decide  
  f := ![![![-1979, -36270, -4536], ![-1098, 138348, 0]], ![![-530, -9500, -1188], ![-243, 36234, 0]], ![![-815, -14865, -1859], ![-435, 56700, 0]]]
  g := ![![![1, 0, 0], ![-16, 61, 0], ![-25, 0, 61]], ![![0, 1, 0], ![-5, 16, 2], ![3, -38, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N0 : Nat.card (O ⧸ I61N0) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N0)

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := prime_ideal_of_norm_prime hp61.out _ NI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-14, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-14, 1, 0]] 
 ![![61, 0, 0], ![47, 1, 0], ![55, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-14, 1, 0], ![1, -14, 2], ![0, -38, -13]]]
  hmulB := by decide  
  f := ![![![-605, 9459, -1352], ![305, 41236, 0]], ![![-463, 7276, -1040], ![245, 31720, 0]], ![![-537, 8528, -1219], ![312, 37180, 0]]]
  g := ![![![1, 0, 0], ![-47, 61, 0], ![-55, 0, 61]], ![![-1, 1, 0], ![9, -14, 2], ![41, -38, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-3, 1, 0]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-3, 1, 0]] 
 ![![61, 0, 0], ![58, 1, 0], ![57, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-3, 1, 0], ![1, -3, 2], ![0, -38, -2]]]
  hmulB := by decide  
  f := ![![![-156, 479, -320], ![61, 9760, 0]], ![![-148, 455, -304], ![62, 9272, 0]], ![![-147, 448, -299], ![32, 9120, 0]]]
  g := ![![![1, 0, 0], ![-58, 61, 0], ![-57, 0, 61]], ![![-1, 1, 0], ![1, -3, 2], ![38, -38, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![16, 1, 0]] ![![61, 0, 0], ![-14, 1, 0]]
  ![![61, 0, 0], ![41, 1, 1]] where
 M := ![![![3721, 0, 0], ![-854, 61, 0]], ![![976, 61, 0], ![-223, 2, 2]]]
 hmul := by decide  
 g := ![![![![20, -1, -1], ![61, 0, 0]], ![![-14, 1, 0], ![0, 0, 0]]], ![![![-25, 0, -1], ![61, 0, 0]], ![![-5, 0, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![41, 1, 1]] ![![61, 0, 0], ![-3, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-183, 61, 0]], ![![2501, 61, 61], ![-122, 0, 0]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-3, 1, 0]]], ![![![41, 1, 1]], ![![-2, 0, 0]]]]
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


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [60, 14, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 61, 6], [44, 5, 61], [0, 1]]
 g := ![![[3, 2, 6], [61, 63, 24], [65, 37], [38, 33], [65, 1], []], ![[3, 16, 66, 25], [3, 35, 47, 64], [63, 29], [18, 6], [10, 25], [57, 36]], ![[44, 38, 64, 13], [3, 23, 21, 51], [66, 64], [8, 55], [0, 36], [2, 36]]]
 h' := ![![[21, 61, 6], [25, 8, 26], [35, 64, 15], [60, 59, 29], [53, 35, 57], [0, 0, 1], [0, 1]], ![[44, 5, 61], [57, 41, 44], [43, 41, 57], [65, 21, 30], [26, 65, 26], [36, 6, 5], [21, 61, 6]], ![[0, 1], [23, 18, 64], [8, 29, 62], [45, 54, 8], [49, 34, 51], [7, 61, 61], [44, 5, 61]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59, 1], []]
 b := ![[], [58, 25, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [60, 14, 2, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-112091, 96748, -226929]
  a := ![2, 19, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1673, 1444, -3387]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![27, 1, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![27, 1, 0]] 
 ![![71, 0, 0], ![27, 1, 0], ![62, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![27, 1, 0], ![1, 27, 2], ![0, -38, 28]]]
  hmulB := by decide  
  f := ![![![-1294, -45885, -3400], ![-1065, 120700, 0]], ![![-484, -17436, -1292], ![-425, 45866, 0]], ![![-1114, -40068, -2969], ![-972, 105400, 0]]]
  g := ![![![1, 0, 0], ![-27, 71, 0], ![-62, 0, 71]], ![![0, 1, 0], ![-12, 27, 2], ![-10, -38, 28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N0 : Nat.card (O ⧸ I71N0) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N0)

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := prime_ideal_of_norm_prime hp71.out _ NI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-16, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-16, 1, 0]] 
 ![![71, 0, 0], ![55, 1, 0], ![50, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-16, 1, 0], ![1, -16, 2], ![0, -38, -15]]]
  hmulB := by decide  
  f := ![![![-1899, 33715, -4216], ![923, 149668, 0]], ![![-1471, 26102, -3264], ![711, 115872, 0]], ![![-1338, 23743, -2969], ![647, 105400, 0]]]
  g := ![![![1, 0, 0], ![-55, 71, 0], ![-50, 0, 71]], ![![-1, 1, 0], ![11, -16, 2], ![40, -38, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-12, 1, 0]] i)))

def SI71N2: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-12, 1, 0]] 
 ![![71, 0, 0], ![59, 1, 0], ![35, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-12, 1, 0], ![1, -12, 2], ![0, -38, -11]]]
  hmulB := by decide  
  f := ![![![3632, -46003, 7670], ![-1207, -272285, 0]], ![![3019, -38218, 6372], ![-993, -226206, 0]], ![![1796, -22678, 3781], ![-562, -134225, 0]]]
  g := ![![![1, 0, 0], ![-59, 71, 0], ![-35, 0, 71]], ![![-1, 1, 0], ![9, -12, 2], ![37, -38, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![27, 1, 0]] ![![71, 0, 0], ![-16, 1, 0]]
  ![![71, 0, 0], ![33, -30, 1]] where
 M := ![![![5041, 0, 0], ![-1136, 71, 0]], ![![1917, 71, 0], ![-431, 11, 2]]]
 hmul := by decide  
 g := ![![![![38, 30, -1], ![71, 0, 0]], ![![-16, 1, 0], ![0, 0, 0]]], ![![![-6, 31, -1], ![71, 0, 0]], ![![-7, 1, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![33, -30, 1]] ![![71, 0, 0], ![-12, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-852, 71, 0]], ![![2343, -2130, 71], ![-426, 355, -71]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-12, 1, 0]]], ![![![33, -30, 1]], ![![-6, 5, -1]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-8, 21, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-8, 21, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![65, 21, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-8, 21, 1], ![21, -46, 43], ![-19, -817, -25]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-65, -21, 73]], ![![-1, 0, 1], ![-38, -13, 43], ![22, -4, -25]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [10, 50, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 72], [0, 1]]
 g := ![![[5, 55], [2], [61], [37, 72], [18], [1]], ![[29, 18], [2], [61], [14, 1], [18], [1]]]
 h' := ![![[23, 72], [54, 37], [72, 41], [68, 34], [66, 27], [63, 23], [0, 1]], ![[0, 1], [29, 36], [66, 32], [47, 39], [30, 46], [8, 50], [23, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40]]
 b := ![[], [62, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [10, 50, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-248, 651, -480]
  a := ![-2, 3, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![424, 147, -480]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![30, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![30, 1, 0]] 
 ![![73, 0, 0], ![30, 1, 0], ![25, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![30, 1, 0], ![1, 30, 2], ![0, -38, 31]]]
  hmulB := by decide  
  f := ![![![-2373, -99089, -6608], ![-2263, 241192, 0]], ![![-967, -40697, -2714], ![-948, 99061, 0]], ![![-825, -33935, -2263], ![-745, 82600, 0]]]
  g := ![![![1, 0, 0], ![-30, 73, 0], ![-25, 0, 73]], ![![0, 1, 0], ![-13, 30, 2], ![5, -38, 31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-8, 21, 1]] ![![73, 0, 0], ![30, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![2190, 73, 0]], ![![-584, 1533, 73], ![-219, 584, 73]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![30, 1, 0]]], ![![![-8, 21, 1]], ![![-3, 8, 1]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![18, 1, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![18, 1, 0]] 
 ![![79, 0, 0], ![18, 1, 0], ![36, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![18, 1, 0], ![1, 18, 2], ![0, -38, 19]]]
  hmulB := by decide  
  f := ![![![-403, -7918, -880], ![-158, 34760, 0]], ![![-100, -1800, -200], ![1, 7900, 0]], ![![-198, -3609, -401], ![-9, 15840, 0]]]
  g := ![![![1, 0, 0], ![-18, 79, 0], ![-36, 0, 79]], ![![0, 1, 0], ![-5, 18, 2], ![0, -38, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N0 : Nat.card (O ⧸ I79N0) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N0)

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := prime_ideal_of_norm_prime hp79.out _ NI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![27, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![27, 1, 0]] 
 ![![79, 0, 0], ![27, 1, 0], ![31, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![27, 1, 0], ![1, 27, 2], ![0, -38, 28]]]
  hmulB := by decide  
  f := ![![![-561, -18814, -1394], ![-395, 55063, 0]], ![![-211, -6425, -476], ![-78, 18802, 0]], ![![-228, -7383, -547], ![-132, 21607, 0]]]
  g := ![![![1, 0, 0], ![-27, 79, 0], ![-31, 0, 79]], ![![0, 1, 0], ![-10, 27, 2], ![2, -38, 28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1

def I79N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![33, 1, 0]] i)))

def SI79N2: IdealEqSpanCertificate' Table ![![79, 0, 0], ![33, 1, 0]] 
 ![![79, 0, 0], ![33, 1, 0], ![9, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![33, 1, 0], ![1, 33, 2], ![0, -38, 34]]]
  hmulB := by decide  
  f := ![![![538, 25337, 1536], ![553, -60672, 0]], ![![221, 10557, 640], ![238, -25280, 0]], ![![45, 2886, 175], ![102, -6912, 0]]]
  g := ![![![1, 0, 0], ![-33, 79, 0], ![-9, 0, 79]], ![![0, 1, 0], ![-14, 33, 2], ![12, -38, 34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N2 : Nat.card (O ⧸ I79N2) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N2)

lemma isPrimeI79N2 : Ideal.IsPrime I79N2 := prime_ideal_of_norm_prime hp79.out _ NI79N2
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![18, 1, 0]] ![![79, 0, 0], ![27, 1, 0]]
  ![![79, 0, 0], ![46, -17, 1]] where
 M := ![![![6241, 0, 0], ![2133, 79, 0]], ![![1422, 79, 0], ![487, 45, 2]]]
 hmul := by decide  
 g := ![![![![33, 17, -1], ![79, 0, 0]], ![![-19, 18, -1], ![79, 0, 0]]], ![![![-28, 18, -1], ![79, 0, 0]], ![![-41, 18, -1], ![81, 0, 0]]]]
 hle2 := by decide  

def MulI79N1 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![46, -17, 1]] ![![79, 0, 0], ![33, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![2607, 79, 0]], ![![3634, -1343, 79], ![1501, -553, 0]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![33, 1, 0]]], ![![![46, -17, 1]], ![![19, -7, 0]]]]
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


lemma PB184I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB184I1 : PrimesBelowBoundCertificateInterval O 31 79 184 where
  m := 11
  g := ![1, 2, 2, 2, 2, 3, 3, 1, 3, 2, 3]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB184I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1, I59N2]
    · exact ![I61N0, I61N1, I61N2]
    · exact ![I67N0]
    · exact ![I71N0, I71N1, I71N2]
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
    · exact ![50653]
    · exact ![1681, 41]
    · exact ![1849, 43]
    · exact ![2209, 47]
    · exact ![2809, 53]
    · exact ![59, 59, 59]
    · exact ![61, 61, 61]
    · exact ![300763]
    · exact ![71, 71, 71]
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
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
      exact NI79N2
  β := ![I41N1, I43N1, I47N1, I53N1, I59N0, I59N1, I59N2, I61N0, I61N1, I61N2, I71N0, I71N1, I71N2, I73N1, I79N0, I79N1, I79N2]
  Il := ![[], [I41N1], [I43N1], [I47N1], [I53N1], [I59N0, I59N1, I59N2], [I61N0, I61N1, I61N2], [], [I71N0, I71N1, I71N2], [I73N1], [I79N0, I79N1, I79N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
