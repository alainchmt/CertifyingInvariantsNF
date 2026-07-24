
import IdealArithmetic.Examples.NF3_1_399916_3.RI3_1_399916_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![10, 2, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![10, 2, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![10, 2, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![10, 2, 1], ![124, 10, 5], ![305, 61, 12]]]
  hmulB := by decide  
  f := ![![![-9, -2, -1], ![37, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-10, -2, 37]], ![![0, 0, 1], ![2, 0, 5], ![5, 1, 12]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [8, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [26, 36], [0, 1]]
 g := ![![[6, 34], [26], [33, 27], [10], [1]], ![[2, 3], [26], [32, 10], [10], [1]]]
 h' := ![![[26, 36], [2, 21], [32, 10], [21, 29], [29, 26], [0, 1]], ![[0, 1], [30, 16], [33, 27], [35, 8], [2, 11], [26, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [19, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [8, 11, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![731, 235, -12]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![23, 7, -12]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-5, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-5, 1, 0]] 
 ![![37, 0, 0], ![32, 1, 0], ![25, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-5, 1, 0], ![1, -5, 2], ![122, 0, -4]]]
  hmulB := by decide  
  f := ![![![-231, 1208, -484], ![74, 8954, 0]], ![![-198, 1043, -418], ![75, 7733, 0]], ![![-155, 816, -327], ![58, 6050, 0]]]
  g := ![![![1, 0, 0], ![-32, 37, 0], ![-25, 0, 37]], ![![-1, 1, 0], ![3, -5, 2], ![6, 0, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![10, 2, 1]] ![![37, 0, 0], ![-5, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-185, 37, 0]], ![![370, 74, 37], ![74, 0, 0]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-5, 1, 0]]], ![![![10, 2, 1]], ![![2, 0, 0]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0]] 
 ![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [4, 36, 37, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 24, 6], [32, 16, 35], [0, 1]]
 g := ![![[7, 33, 40], [5, 1], [31, 37], [21, 4, 1], []], ![[40, 34, 27, 11], [7, 33], [36, 4], [6, 21, 26, 19], [22, 36]], ![[4, 3, 12, 3], [34, 31], [30, 31], [38, 11, 0, 29], [34, 36]]]
 h' := ![![[13, 24, 6], [30, 18, 9], [3, 20, 40], [39, 7, 18], [0, 0, 1], [0, 1]], ![[32, 16, 35], [9, 2, 6], [18, 13, 22], [30, 5, 2], [40, 16, 16], [13, 24, 6]], ![[0, 1], [29, 21, 26], [1, 8, 20], [11, 29, 21], [27, 25, 24], [32, 16, 35]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13, 19], []]
 b := ![[], [15, 1, 31], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [4, 36, 37, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![887527, 63345, -2542]
  a := ![2, -2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![21647, 1545, -62]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![12, 16, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![12, 16, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![12, 16, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![12, 16, 1], ![138, 12, 33], ![2013, 61, 28]]]
  hmulB := by decide  
  f := ![![![-11, -16, -1], ![43, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-12, -16, 43]], ![![0, 0, 1], ![-6, -12, 33], ![39, -9, 28]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [4, 34, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 42], [0, 1]]
 g := ![![[30, 11], [15, 31], [10], [12, 38], [1]], ![[0, 32], [36, 12], [10], [10, 5], [1]]]
 h' := ![![[9, 42], [26, 21], [28, 26], [38, 15], [39, 9], [0, 1]], ![[0, 1], [0, 22], [4, 17], [1, 28], [34, 34], [9, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [18, 39]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [4, 34, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![251632, 265620, 6206]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4120, 3868, 6206]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![10, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![10, 1, 0]] 
 ![![43, 0, 0], ![10, 1, 0], ![15, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![10, 1, 0], ![1, 10, 2], ![122, 0, 11]]]
  hmulB := by decide  
  f := ![![![-346, -3767, -754], ![-129, 16211, 0]], ![![-87, -870, -174], ![1, 3741, 0]], ![![-120, -1314, -263], ![-48, 5655, 0]]]
  g := ![![![1, 0, 0], ![-10, 43, 0], ![-15, 0, 43]], ![![0, 1, 0], ![-3, 10, 2], ![-1, 0, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![12, 16, 1]] ![![43, 0, 0], ![10, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![430, 43, 0]], ![![516, 688, 43], ![258, 172, 43]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![10, 1, 0]]], ![![![12, 16, 1]], ![![6, 4, 1]]]]
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


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [28, 9, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 17, 23], [22, 29, 24], [0, 1]]
 g := ![![[6, 4, 27], [4, 25, 36], [42, 23, 21], [16, 42, 1], []], ![[9, 37, 29, 11], [44, 1, 42, 23], [39, 14, 14, 15], [39, 12, 27, 26], [17, 12]], ![[0, 5, 35, 34], [41, 29, 34, 36], [29, 41, 24, 32], [24, 46, 17, 27], [16, 12]]]
 h' := ![![[20, 17, 23], [29, 17, 11], [46, 26, 41], [22, 43, 31], [0, 0, 1], [0, 1]], ![[22, 29, 24], [3, 40, 5], [35, 1, 1], [30, 25, 8], [18, 3, 29], [20, 17, 23]], ![[0, 1], [0, 37, 31], [26, 20, 5], [16, 26, 8], [36, 44, 17], [22, 29, 24]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30, 40], []]
 b := ![[], [45, 12, 33], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [28, 9, 5, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-927545, 1222, -6110]
  a := ![-2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-19735, 26, -130]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-6, -18, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-6, -18, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![47, 35, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-6, -18, 1], ![104, -6, -35], ![-2135, 61, -24]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-47, -35, 53]], ![![-1, -1, 1], ![33, 23, -35], ![-19, 17, -24]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [6, 33, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [20, 52], [0, 1]]
 g := ![![[32, 9], [52], [22, 42], [52], [20, 1]], ![[0, 44], [52], [14, 11], [52], [40, 52]]]
 h' := ![![[20, 52], [46, 3], [27, 23], [43, 25], [39, 23], [0, 1]], ![[0, 1], [0, 50], [10, 30], [13, 28], [22, 30], [20, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31]]
 b := ![[], [4, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [6, 33, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![707, 213, -56]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![63, 41, -56]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-18, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-18, 1, 0]] 
 ![![53, 0, 0], ![35, 1, 0], ![24, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-18, 1, 0], ![1, -18, 2], ![122, 0, -17]]]
  hmulB := by decide  
  f := ![![![279, -6296, 700], ![-212, -18550, 0]], ![![196, -4156, 462], ![-105, -12243, 0]], ![![144, -2852, 317], ![-44, -8400, 0]]]
  g := ![![![1, 0, 0], ![-35, 53, 0], ![-24, 0, 53]], ![![-1, 1, 0], ![11, -18, 2], ![10, 0, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![-6, -18, 1]] ![![53, 0, 0], ![-18, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-954, 53, 0]], ![![-318, -954, 53], ![212, 318, -53]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-18, 1, 0]]], ![![![-6, -18, 1]], ![![4, 6, -1]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![20, -3, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![20, -3, 0]] 
 ![![59, 0, 0], ![13, 1, 0], ![34, 0, 1]] where
  M :=![![![20, -3, 0], ![-3, 20, -6], ![-366, 0, 17]]]
  hmulB := by decide  
  f := ![![![340, 51, 18]], ![![113, 17, 6]], ![![320, 48, 17]]]
  g := ![![![1, -3, 0], ![-1, 20, -6], ![-16, 0, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N0 : Nat.card (O ⧸ I59N0) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N0)

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := prime_ideal_of_norm_prime hp59.out _ NI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![17, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![17, 1, 0]] 
 ![![59, 0, 0], ![17, 1, 0], ![33, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![17, 1, 0], ![1, 17, 2], ![122, 0, 18]]]
  hmulB := by decide  
  f := ![![![26, 713, 84], ![59, -2478, 0]], ![![-5, 203, 24], ![60, -708, 0]], ![![18, 399, 47], ![21, -1386, 0]]]
  g := ![![![1, 0, 0], ![-17, 59, 0], ![-33, 0, 59]], ![![0, 1, 0], ![-6, 17, 2], ![-8, 0, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![28, 1, 0]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![59, 0, 0], ![28, 1, 0]] 
 ![![59, 0, 0], ![28, 1, 0], ![51, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![28, 1, 0], ![1, 28, 2], ![122, 0, 29]]]
  hmulB := by decide  
  f := ![![![539, 24460, 1748], ![708, -51566, 0]], ![![246, 11586, 828], ![355, -24426, 0]], ![![455, 21143, 1511], ![635, -44574, 0]]]
  g := ![![![1, 0, 0], ![-28, 59, 0], ![-51, 0, 59]], ![![0, 1, 0], ![-15, 28, 2], ![-23, 0, 29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![20, -3, 0]] ![![59, 0, 0], ![17, 1, 0]]
  ![![59, 0, 0], ![-7, 15, 1]] where
 M := ![![![1180, -177, 0], ![337, -31, -6]]]
 hmul := by decide  
 g := ![![![![20, -3, 0], ![0, 0, 0]], ![![12, -14, -1], ![53, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-7, 15, 1]] ![![59, 0, 0], ![28, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![1652, 59, 0]], ![![-413, 885, 59], ![-59, 413, 59]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![28, 1, 0]]], ![![![-7, 15, 1]], ![![-1, 7, 1]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![1, 1, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![1, 1, 0]] 
 ![![61, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![1, 1, 0], ![1, 1, 2], ![122, 0, 2]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![61, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-1, -1, -1], ![30, 31, 0]]]
  g := ![![![1, 0, 0], ![-1, 61, 0], ![0, 0, 61]], ![![0, 1, 0], ![0, 1, 2], ![2, 0, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N0 : Nat.card (O ⧸ I61N0) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N0)

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := prime_ideal_of_norm_prime hp61.out _ NI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-1, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-1, 1, 0]] 
 ![![61, 0, 0], ![60, 1, 0], ![0, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-1, 1, 0], ![1, -1, 2], ![122, 0, 0]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]], ![![0, 0, -1], ![31, 31, 0]]]
  g := ![![![1, 0, 0], ![-60, 61, 0], ![0, 0, 61]], ![![-1, 1, 0], ![1, -1, 2], ![2, 0, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![1, 1, 0]] ![![61, 0, 0], ![-1, 1, 0]]
  ![![61, 0, 0], ![0, 0, 1]] where
 M := ![![![3721, 0, 0], ![-61, 61, 0]], ![![61, 61, 0], ![0, 0, 2]]]
 hmul := by decide  
 g := ![![![![19, 0, 0], ![-21, 21, 0]], ![![-1, 1, 0], ![0, 0, 0]]], ![![![1, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![0, 0, 1]] ![![61, 0, 0], ![-1, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-61, 61, 0]], ![![0, 0, 61], ![122, 0, 0]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-1, 1, 0]]], ![![![0, 0, 1]], ![![2, 0, 0]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1, I61N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
    exact isPrimeI61N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0 ⊙ MulI61N1)
instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-982, 21, 39]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![-982, 21, 39]] 
 ![![67, 0, 0], ![0, 67, 0], ![59, 16, 1]] where
  M :=![![![-982, 21, 39], ![4779, -982, 81], ![4941, 2379, -961]]]
  hmulB := by decide  
  f := ![![![-11209, -1686, -597]], ![![-74520, -11209, -3969]], ![![-31280, -4705, -1666]]]
  g := ![![![-49, -9, 39], ![0, -34, 81], ![920, 265, -961]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [55, 25, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [42, 66], [0, 1]]
 g := ![![[37, 39], [27, 24], [64], [54], [22], [1]], ![[0, 28], [30, 43], [64], [54], [22], [1]]]
 h' := ![![[42, 66], [56, 21], [26, 52], [14, 59], [6, 56], [12, 42], [0, 1]], ![[0, 1], [0, 46], [66, 15], [13, 8], [13, 11], [34, 25], [42, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [14, 44]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [55, 25, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![14927, 1100, 923]
  a := ![2, 19, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-590, -204, 923]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11209, -1686, -597]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![-11209, -1686, -597]] 
 ![![67, 0, 0], ![34, 1, 0], ![59, 0, 1]] where
  M :=![![![-11209, -1686, -597], ![-74520, -11209, -3969], ![-242109, -36417, -12895]]]
  hmulB := by decide  
  f := ![![![-982, 21, 39]], ![![-427, -4, 21]], ![![-791, 54, 20]]]
  g := ![![![1214, -1686, -597], ![8071, -11209, -3969], ![26222, -36417, -12895]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![-982, 21, 39]] ![![-11209, -1686, -597]]
  ![![67, 0, 0]] where
 M := ![![![67, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0]] 
 ![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [14, 57, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [58, 6, 36], [10, 64, 35], [0, 1]]
 g := ![![[6, 26, 43], [60, 8, 8], [24, 56, 60], [26, 32], [68, 1], []], ![[23, 50, 13, 20], [45, 15, 20, 2], [33, 12, 29, 50], [19, 8], [63, 49], [23, 18]], ![[55, 35, 59, 61], [69, 34, 67, 42], [17, 36, 62, 68], [65, 8], [1, 36], [24, 18]]]
 h' := ![![[58, 6, 36], [12, 24, 55], [19, 23, 47], [51, 40, 42], [42, 15, 23], [0, 0, 1], [0, 1]], ![[10, 64, 35], [18, 29, 53], [55, 1, 2], [63, 36, 10], [20, 29, 24], [60, 56, 64], [58, 6, 36]], ![[0, 1], [52, 18, 34], [20, 47, 22], [53, 66, 19], [18, 27, 24], [48, 15, 6], [10, 64, 35]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59, 22], []]
 b := ![[], [58, 48, 27], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [14, 57, 3, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-194469, -6390, 6390]
  a := ![-2, 3, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2739, -90, 90]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-14, 23, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-14, 23, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![59, 23, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-14, 23, 1], ![145, -14, 47], ![2867, 61, 9]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-59, -23, 73]], ![![-1, 0, 1], ![-36, -15, 47], ![32, -2, 9]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [17, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [68, 72], [0, 1]]
 g := ![![[69, 48], [69], [19], [46, 54], [25], [1]], ![[48, 25], [69], [19], [68, 19], [25], [1]]]
 h' := ![![[68, 72], [49, 62], [45, 54], [21, 47], [10, 45], [56, 68], [0, 1]], ![[0, 1], [31, 11], [67, 19], [5, 26], [4, 28], [8, 5], [68, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [68]]
 b := ![[], [12, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [17, 5, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1984, 985, 46]
  a := ![2, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10, -1, 46]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![26, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![26, 1, 0]] 
 ![![73, 0, 0], ![26, 1, 0], ![64, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![26, 1, 0], ![1, 26, 2], ![122, 0, 27]]]
  hmulB := by decide  
  f := ![![![-1438, -47539, -3658], ![-1095, 133517, 0]], ![![-521, -16921, -1302], ![-364, 47523, 0]], ![![-1260, -41678, -3207], ![-962, 117056, 0]]]
  g := ![![![1, 0, 0], ![-26, 73, 0], ![-64, 0, 73]], ![![0, 1, 0], ![-11, 26, 2], ![-22, 0, 27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-14, 23, 1]] ![![73, 0, 0], ![26, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![1898, 73, 0]], ![![-1022, 1679, 73], ![-219, 584, 73]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![26, 1, 0]]], ![![![-14, 23, 1]], ![![-3, 8, 1]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-723, 112, -1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![-723, 112, -1]] 
 ![![79, 0, 0], ![0, 79, 0], ![12, 46, 1]] where
  M :=![![![-723, 112, -1], ![-10, -723, 223], ![13603, -61, -611]]]
  hmulB := by decide  
  f := ![![![5764, 867, 307]], ![![38321, 5764, 2041]], ![![24765, 3725, 1319]]]
  g := ![![![-9, 2, -1], ![-34, -139, 223], ![265, 355, -611]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [72, 36, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [43, 78], [0, 1]]
 g := ![![[40, 45], [30, 18], [12, 62], [50, 9], [32], [1]], ![[0, 34], [14, 61], [71, 17], [42, 70], [32], [1]]]
 h' := ![![[43, 78], [52, 19], [5, 52], [34, 33], [36, 3], [7, 43], [0, 1]], ![[0, 1], [0, 60], [29, 27], [31, 46], [7, 76], [39, 36], [43, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [31, 50]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [72, 36, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1442, 1525, -130]
  a := ![-5, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![38, 95, -130]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5764, 867, 307]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![5764, 867, 307]] 
 ![![79, 0, 0], ![65, 1, 0], ![21, 0, 1]] where
  M :=![![![5764, 867, 307], ![38321, 5764, 2041], ![124501, 18727, 6631]]]
  hmulB := by decide  
  f := ![![![-723, 112, -1]], ![![-595, 83, 2]], ![![-20, 29, -8]]]
  g := ![![![-722, 867, 307], ![-4800, 5764, 2041], ![-15595, 18727, 6631]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![-723, 112, -1]] ![![5764, 867, 307]]
  ![![79, 0, 0]] where
 M := ![![![79, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


lemma PB179I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB179I1 : PrimesBelowBoundCertificateInterval O 31 79 179 where
  m := 11
  g := ![2, 1, 2, 1, 2, 3, 3, 2, 1, 2, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB179I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0]
    · exact ![I43N0, I43N1]
    · exact ![I47N0]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1, I59N2]
    · exact ![I61N0, I61N1, I61N1]
    · exact ![I67N0, I67N1]
    · exact ![I71N0]
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
    · exact ![1369, 37]
    · exact ![68921]
    · exact ![1849, 43]
    · exact ![103823]
    · exact ![2809, 53]
    · exact ![59, 59, 59]
    · exact ![61, 61, 61]
    · exact ![4489, 67]
    · exact ![357911]
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
      exact NI61N1
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I37N1, I43N1, I53N1, I59N0, I59N1, I59N2, I61N0, I61N1, I67N1, I73N1, I79N1]
  Il := ![[I37N1], [], [I43N1], [], [I53N1], [I59N0, I59N1, I59N2], [I61N0, I61N1, I61N1], [I67N1], [], [I73N1], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
