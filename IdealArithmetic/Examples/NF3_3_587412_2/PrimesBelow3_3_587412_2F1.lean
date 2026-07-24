
import IdealArithmetic.Examples.NF3_3_587412_2.RI3_3_587412_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![12, 1, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![12, 1, 0]] 
 ![![37, 0, 0], ![12, 1, 0], ![4, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![12, 1, 0], ![0, 12, 1], ![1162, 210, 12]]]
  hmulB := by decide  
  f := ![![![169, 14, 0], ![-518, 0, 0]], ![![60, 5, 0], ![-184, 0, 0]], ![![4, 0, 0], ![-12, 1, 0]]]
  g := ![![![1, 0, 0], ![-12, 37, 0], ![-4, 0, 37]], ![![0, 1, 0], ![-4, 12, 1], ![-38, 210, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![13, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![13, 1, 0]] 
 ![![37, 0, 0], ![13, 1, 0], ![16, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![13, 1, 0], ![0, 13, 1], ![1162, 210, 13]]]
  hmulB := by decide  
  f := ![![![157, 12, 0], ![-444, 0, 0]], ![![39, 3, 0], ![-110, 0, 0]], ![![70, 5, 0], ![-198, 1, 0]]]
  g := ![![![1, 0, 0], ![-13, 37, 0], ![-16, 0, 37]], ![![0, 1, 0], ![-5, 13, 1], ![-48, 210, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![12, 1, 0]] ![![37, 0, 0], ![12, 1, 0]]
  ![![37, 0, 0], ![-152, -13, 1]] where
 M := ![![![1369, 0, 0], ![444, 37, 0]], ![![444, 37, 0], ![144, 24, 1]]]
 hmul := by decide  
 g := ![![![![37, 0, 0], ![0, 0, 0]], ![![12, 1, 0], ![0, 0, 0]]], ![![![12, 1, 0], ![0, 0, 0]], ![![8, 1, 0], ![1, 0, 0]]]]
 hle2 := by decide  
def MulI37N1 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![-152, -13, 1]] ![![37, 0, 0], ![13, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![481, 37, 0]], ![![-5624, -481, 37], ![-814, -111, 0]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![13, 1, 0]]], ![![![-152, -13, 1]], ![![-22, -3, 0]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N0, I37N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N0
    exact isPrimeI37N1
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


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [17, 19, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 15, 7], [6, 25, 34], [0, 1]]
 g := ![![[13, 28, 33], [29, 31], [5, 33], [40, 31, 1], []], ![[24, 17, 16, 11], [26, 5], [26, 36], [25, 32, 28, 29], [7, 8]], ![[31, 0, 6, 22], [38, 23], [37, 5], [31, 21, 0, 24], [21, 8]]]
 h' := ![![[25, 15, 7], [0, 10, 22], [40, 30, 20], [17, 25, 19], [0, 0, 1], [0, 1]], ![[6, 25, 34], [25, 31, 5], [4, 25, 13], [6, 2, 35], [14, 30, 25], [25, 15, 7]], ![[0, 1], [9, 0, 14], [32, 27, 8], [13, 14, 28], [7, 11, 15], [6, 25, 34]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 30], []]
 b := ![[], [14, 0, 25], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [17, 19, 10, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2060209, -608235, -46125]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-50249, -14835, -1125]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-158, -3, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-158, -3, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![14, 40, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-158, -3, 1], ![1162, 52, -3], ![-3486, 532, 52]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![4, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-14, -40, 43]], ![![-4, -1, 1], ![28, 4, -3], ![-98, -36, 52]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [41, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 42], [0, 1]]
 g := ![![[32, 21], [2, 4], [17], [14, 11], [1]], ![[0, 22], [0, 39], [17], [30, 32], [1]]]
 h' := ![![[21, 42], [4, 8], [1, 2], [28, 19], [2, 21], [0, 1]], ![[0, 1], [0, 35], [0, 41], [40, 24], [13, 22], [21, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36]]
 b := ![[], [26, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [41, 22, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-13924, 7898, 1954]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-960, -1634, 1954]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![3, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![3, 1, 0]] 
 ![![43, 0, 0], ![3, 1, 0], ![34, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![3, 1, 0], ![0, 3, 1], ![1162, 210, 3]]]
  hmulB := by decide  
  f := ![![![76, 25, 0], ![-1075, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![58, 19, 0], ![-820, 1, 0]]]
  g := ![![![1, 0, 0], ![-3, 43, 0], ![-34, 0, 43]], ![![0, 1, 0], ![-1, 3, 1], ![10, 210, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-158, -3, 1]] ![![43, 0, 0], ![3, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![129, 43, 0]], ![![-6794, -129, 43], ![688, 43, 0]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![3, 1, 0]]], ![![![-158, -3, 1]], ![![16, 1, 0]]]]
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


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [41, 13, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 6, 12], [7, 40, 35], [0, 1]]
 g := ![![[30, 12, 42], [44, 4, 9], [24, 20, 21], [35, 46, 1], []], ![[10, 3, 35, 2], [23, 35, 26, 18], [14, 20, 24, 21], [34, 22, 26, 24], [0, 3]], ![[20, 39, 0, 43], [7, 20, 36, 31], [9, 2, 4, 30], [3, 43, 40, 38], [24, 3]]]
 h' := ![![[39, 6, 12], [29, 25, 18], [3, 10, 3], [22, 9, 31], [0, 0, 1], [0, 1]], ![[7, 40, 35], [41, 15, 33], [21, 14, 5], [7, 33, 32], [17, 16, 40], [39, 6, 12]], ![[0, 1], [12, 7, 43], [41, 23, 39], [5, 5, 31], [5, 31, 6], [7, 40, 35]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 45], []]
 b := ![[], [38, 20, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [41, 13, 1, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-431977, -488565, -93718]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-9191, -10395, -1994]
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


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [16, 29, 38, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 52, 35], [10, 0, 18], [0, 1]]
 g := ![![[3, 25, 42], [27, 4], [27, 22, 6], [14, 13], [1]], ![[26, 20, 26, 22], [3, 44], [27, 35, 22, 21], [41, 11], [46, 10, 5, 51]], ![[11, 2, 8, 18], [41, 6], [14, 50, 22, 18], [40, 49], [46, 42, 30, 2]]]
 h' := ![![[5, 52, 35], [3, 28, 28], [45, 48, 51], [32, 49, 35], [37, 24, 15], [0, 1]], ![[10, 0, 18], [45, 3, 26], [27, 52, 37], [22, 3, 19], [25, 21, 45], [5, 52, 35]], ![[0, 1], [22, 22, 52], [25, 6, 18], [50, 1, 52], [52, 8, 46], [10, 0, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20, 34], []]
 b := ![[], [21, 38, 49], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [16, 29, 38, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-30152654, -11619402, -1084009]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-568918, -219234, -20453]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-115, -6, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-115, -6, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![3, 53, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-115, -6, 1], ![1162, 95, -6], ![-6972, -98, 95]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-3, -53, 59]], ![![-2, -1, 1], ![20, 7, -6], ![-123, -87, 95]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [30, 36, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [23, 58], [0, 1]]
 g := ![![[13, 1], [49, 20], [1], [39, 21], [23, 1]], ![[36, 58], [37, 39], [1], [50, 38], [46, 58]]]
 h' := ![![[23, 58], [5, 58], [11, 43], [10, 1], [18, 27], [0, 1]], ![[0, 1], [41, 1], [56, 16], [33, 58], [49, 32], [23, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [9, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [30, 36, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2354, 1546, 175]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![31, -131, 175]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![6, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![6, 1, 0]] 
 ![![59, 0, 0], ![6, 1, 0], ![23, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![6, 1, 0], ![0, 6, 1], ![1162, 210, 6]]]
  hmulB := by decide  
  f := ![![![49, 8, 0], ![-472, 0, 0]], ![![-6, -1, 0], ![60, 0, 0]], ![![13, 2, 0], ![-124, 1, 0]]]
  g := ![![![1, 0, 0], ![-6, 59, 0], ![-23, 0, 59]], ![![0, 1, 0], ![-1, 6, 1], ![-4, 210, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-115, -6, 1]] ![![59, 0, 0], ![6, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![354, 59, 0]], ![![-6785, -354, 59], ![472, 59, 0]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![6, 1, 0]]], ![![![-115, -6, 1]], ![![8, 1, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-150, -11, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-150, -11, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![33, 50, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-150, -11, 1], ![1162, 60, -11], ![-12782, -1148, 60]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![3, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-33, -50, 61]], ![![-3, -1, 1], ![25, 10, -11], ![-242, -68, 60]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [34, 39, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 60], [0, 1]]
 g := ![![[46, 9], [58], [19, 47], [44, 41], [22, 1]], ![[0, 52], [58], [16, 14], [31, 20], [44, 60]]]
 h' := ![![[22, 60], [56, 3], [25, 27], [29, 13], [45, 23], [0, 1]], ![[0, 1], [0, 58], [9, 34], [10, 48], [2, 38], [22, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [53, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [34, 39, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![44230, 9921, 612]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![394, -339, 612]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![11, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![11, 1, 0]] 
 ![![61, 0, 0], ![11, 1, 0], ![1, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![11, 1, 0], ![0, 11, 1], ![1162, 210, 11]]]
  hmulB := by decide  
  f := ![![![375, 34, 0], ![-2074, 0, 0]], ![![55, 5, 0], ![-304, 0, 0]], ![![-9, -1, 0], ![50, 1, 0]]]
  g := ![![![1, 0, 0], ![-11, 61, 0], ![-1, 0, 61]], ![![0, 1, 0], ![-2, 11, 1], ![-19, 210, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-150, -11, 1]] ![![61, 0, 0], ![11, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![671, 61, 0]], ![![-9150, -671, 61], ![-488, -61, 0]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![11, 1, 0]]], ![![![-150, -11, 1]], ![![-8, -1, 0]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0]] 
 ![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [18, 45, 21, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [52, 37, 4], [61, 29, 63], [0, 1]]
 g := ![![[12, 63, 16], [45, 50, 26], [66, 17], [46, 36], [46, 1], []], ![[1, 65, 21, 47], [62, 15, 42, 22], [24, 4], [64, 21], [27, 37], [27, 16]], ![[55, 37, 5, 44], [48, 48, 5, 51], [21, 19], [12, 60], [61, 29], [35, 16]]]
 h' := ![![[52, 37, 4], [61, 59, 63], [6, 9, 48], [16, 21, 34], [43, 56, 61], [0, 0, 1], [0, 1]], ![[61, 29, 63], [19, 39, 53], [6, 65, 21], [6, 40, 65], [32, 62, 50], [7, 0, 29], [52, 37, 4]], ![[0, 1], [6, 36, 18], [49, 60, 65], [62, 6, 35], [55, 16, 23], [9, 0, 37], [61, 29, 63]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 43], []]
 b := ![[], [26, 34, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [18, 45, 21, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![751807, -118590, -35376]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![11221, -1770, -528]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15, 2, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![15, 2, 0]] 
 ![![71, 0, 0], ![43, 1, 0], ![68, 0, 1]] where
  M :=![![![15, 2, 0], ![0, 15, 2], ![2324, 420, 15]]]
  hmulB := by decide  
  f := ![![![-615, -30, 4]], ![![-307, -15, 2]], ![![-1080, -52, 7]]]
  g := ![![![-1, 2, 0], ![-11, 15, 2], ![-236, 420, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N0 : Nat.card (O ⧸ I71N0) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N0)

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := prime_ideal_of_norm_prime hp71.out _ NI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 2, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![17, 2, 0]] 
 ![![71, 0, 0], ![44, 1, 0], ![52, 0, 1]] where
  M :=![![![17, 2, 0], ![0, 17, 2], ![2324, 420, 17]]]
  hmulB := by decide  
  f := ![![![551, 34, -4]], ![![276, 17, -2]], ![![960, 60, -7]]]
  g := ![![![-1, 2, 0], ![-12, 17, 2], ![-240, 420, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 3, 0]] i)))

def SI71N2: IdealEqSpanCertificate' Table ![![23, 3, 0]] 
 ![![71, 0, 0], ![55, 1, 0], ![28, 0, 1]] where
  M :=![![![23, 3, 0], ![0, 23, 3], ![3486, 630, 23]]]
  hmulB := by decide  
  f := ![![![-1361, -69, 9]], ![![-907, -46, 6]], ![![-1666, -84, 11]]]
  g := ![![![-2, 3, 0], ![-19, 23, 3], ![-448, 630, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![15, 2, 0]] ![![17, 2, 0]]
  ![![255, 64, 4]] where
 M := ![![![255, 64, 4]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![255, 64, 4]] ![![23, 3, 0]]
  ![![71, 0, 0]] where
 M := ![![![19809, 4757, 284]]]
 hmul := by decide  
 g := ![![![![279, 67, 4]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![15, 1, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![15, 1, 0]] 
 ![![73, 0, 0], ![15, 1, 0], ![67, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![15, 1, 0], ![0, 15, 1], ![1162, 210, 15]]]
  hmulB := by decide  
  f := ![![![436, 29, 0], ![-2117, 0, 0]], ![![90, 6, 0], ![-437, 0, 0]], ![![424, 28, 0], ![-2059, 1, 0]]]
  g := ![![![1, 0, 0], ![-15, 73, 0], ![-67, 0, 73]], ![![0, 1, 0], ![-4, 15, 1], ![-41, 210, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N0 : Nat.card (O ⧸ I73N0) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N0)

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := prime_ideal_of_norm_prime hp73.out _ NI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![16, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![16, 1, 0]] 
 ![![73, 0, 0], ![16, 1, 0], ![36, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![16, 1, 0], ![0, 16, 1], ![1162, 210, 16]]]
  hmulB := by decide  
  f := ![![![417, 26, 0], ![-1898, 0, 0]], ![![80, 5, 0], ![-364, 0, 0]], ![![196, 12, 0], ![-892, 1, 0]]]
  g := ![![![1, 0, 0], ![-16, 73, 0], ![-36, 0, 73]], ![![0, 1, 0], ![-4, 16, 1], ![-38, 210, 16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1

def I73N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-31, 1, 0]] i)))

def SI73N2: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-31, 1, 0]] 
 ![![73, 0, 0], ![42, 1, 0], ![61, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-31, 1, 0], ![0, -31, 1], ![1162, 210, -31]]]
  hmulB := by decide  
  f := ![![![1458, -47, 0], ![3431, 0, 0]], ![![838, -27, 0], ![1972, 0, 0]], ![![1254, -40, 0], ![2951, 1, 0]]]
  g := ![![![1, 0, 0], ![-42, 73, 0], ![-61, 0, 73]], ![![-1, 1, 0], ![17, -31, 1], ![-79, 210, -31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N2 : Nat.card (O ⧸ I73N2) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N2)

lemma isPrimeI73N2 : Ideal.IsPrime I73N2 := prime_ideal_of_norm_prime hp73.out _ NI73N2
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![15, 1, 0]] ![![73, 0, 0], ![16, 1, 0]]
  ![![73, 0, 0], ![-125, -42, 1]] where
 M := ![![![5329, 0, 0], ![1168, 73, 0]], ![![1095, 73, 0], ![240, 31, 1]]]
 hmul := by decide  
 g := ![![![![73, 0, 0], ![0, 0, 0]], ![![16, 1, 0], ![0, 0, 0]]], ![![![15, 1, 0], ![0, 0, 0]], ![![5, 1, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI73N1 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-125, -42, 1]] ![![73, 0, 0], ![-31, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-2263, 73, 0]], ![![-9125, -3066, 73], ![5037, 1387, -73]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-31, 1, 0]]], ![![![-125, -42, 1]], ![![69, 19, -1]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-106, -5, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-106, -5, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![52, 74, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-106, -5, 1], ![1162, 104, -5], ![-5810, 112, 104]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-52, -74, 79]], ![![-2, -1, 1], ![18, 6, -5], ![-142, -96, 104]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [12, 74, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 78], [0, 1]]
 g := ![![[72, 50], [19, 44], [35, 50], [66, 25], [25], [1]], ![[6, 29], [2, 35], [48, 29], [33, 54], [25], [1]]]
 h' := ![![[5, 78], [9, 34], [54, 53], [77, 34], [2, 5], [67, 5], [0, 1]], ![[0, 1], [21, 45], [3, 26], [10, 45], [27, 74], [13, 74], [5, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62]]
 b := ![[], [41, 31]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [12, 74, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4660, 5562, 989]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-592, -856, 989]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![5, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![5, 1, 0]] 
 ![![79, 0, 0], ![5, 1, 0], ![54, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![5, 1, 0], ![0, 5, 1], ![1162, 210, 5]]]
  hmulB := by decide  
  f := ![![![71, 14, 0], ![-1106, 0, 0]], ![![-5, -1, 0], ![80, 0, 0]], ![![46, 9, 0], ![-716, 1, 0]]]
  g := ![![![1, 0, 0], ![-5, 79, 0], ![-54, 0, 79]], ![![0, 1, 0], ![-1, 5, 1], ![-2, 210, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-106, -5, 1]] ![![79, 0, 0], ![5, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![395, 79, 0]], ![![-8374, -395, 79], ![632, 79, 0]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![5, 1, 0]]], ![![![-106, -5, 1]], ![![8, 1, 0]]]]
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


lemma PB171I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB171I1 : PrimesBelowBoundCertificateInterval O 31 79 171 where
  m := 11
  g := ![3, 1, 2, 1, 1, 2, 2, 1, 3, 3, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB171I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N0, I37N1]
    · exact ![I41N0]
    · exact ![I43N0, I43N1]
    · exact ![I47N0]
    · exact ![I53N0]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1]
    · exact ![I67N0]
    · exact ![I71N0, I71N1, I71N2]
    · exact ![I73N0, I73N1, I73N2]
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
    · exact ![1849, 43]
    · exact ![103823]
    · exact ![148877]
    · exact ![3481, 59]
    · exact ![3721, 61]
    · exact ![300763]
    · exact ![71, 71, 71]
    · exact ![73, 73, 73]
    · exact ![6241, 79]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N0
      exact NI37N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
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
      exact NI79N1
  β := ![I37N0, I37N1, I43N1, I59N1, I61N1, I71N0, I71N1, I71N2, I73N0, I73N1, I73N2, I79N1]
  Il := ![[I37N0, I37N0, I37N1], [], [I43N1], [], [], [I59N1], [I61N1], [], [I71N0, I71N1, I71N2], [I73N0, I73N1, I73N2], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
