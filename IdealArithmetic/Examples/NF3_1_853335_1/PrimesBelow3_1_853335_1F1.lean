
import IdealArithmetic.Examples.NF3_1_853335_1.RI3_1_853335_1
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [33, 36, 26, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 18, 3], [36, 18, 34], [0, 1]]
 g := ![![[3, 34, 34], [18, 27], [12, 33, 10], [11, 1], []], ![[12, 5, 0, 30], [16, 30], [16, 33, 17, 28], [3, 28], [22, 9]], ![[3, 32, 4, 33], [4, 7], [26, 12, 8, 36], [21, 28], [28, 9]]]
 h' := ![![[12, 18, 3], [8, 6, 21], [11, 8, 8], [7, 15, 11], [0, 0, 1], [0, 1]], ![[36, 18, 34], [31, 1, 26], [2, 31, 20], [1, 36, 21], [10, 9, 18], [12, 18, 3]], ![[0, 1], [7, 30, 27], [19, 35, 9], [14, 23, 5], [2, 28, 18], [36, 18, 34]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33, 29], []]
 b := ![[], [8, 35, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [33, 36, 26, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-602064, -18537, -11100]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-16272, -501, -300]
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


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [5, 2, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 14, 14], [12, 26, 27], [0, 1]]
 g := ![![[29, 33, 16], [40, 23], [26, 33], [16, 31, 1], []], ![[25, 11, 17, 14], [21, 2], [11, 23], [5, 5, 38, 34], [31, 32]], ![[11, 6, 37, 19], [24, 40], [15, 32], [1, 11, 19, 3], [18, 32]]]
 h' := ![![[19, 14, 14], [14, 19, 4], [38, 19, 33], [2, 18, 19], [0, 0, 1], [0, 1]], ![[12, 26, 27], [10, 30, 1], [22, 0, 17], [35, 33, 8], [1, 23, 26], [19, 14, 14]], ![[0, 1], [7, 33, 36], [39, 22, 32], [14, 31, 14], [13, 18, 14], [12, 26, 27]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31, 35], []]
 b := ![[], [7, 0, 18], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [5, 2, 10, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![698312, 64411, -18983]
  a := ![3, -3, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![17032, 1571, -463]
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


def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![8, 1, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![8, 1, 0]] 
 ![![43, 0, 0], ![8, 1, 0], ![33, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![8, 1, 0], ![6, 5, 12], ![180, 4, 11]]]
  hmulB := by decide  
  f := ![![![3583, 3087, 7452], ![774, -26703, 0]], ![![658, 571, 1380], ![173, -4945, 0]], ![![2749, 2369, 5719], ![598, -20493, 0]]]
  g := ![![![1, 0, 0], ![-8, 43, 0], ![-33, 0, 43]], ![![0, 1, 0], ![-10, 5, 12], ![-5, 4, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N0)

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := prime_ideal_of_norm_prime hp43.out _ NI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-16, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-16, 1, 0]] 
 ![![43, 0, 0], ![27, 1, 0], ![11, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-16, 1, 0], ![6, -19, 12], ![180, 4, -13]]]
  hmulB := by decide  
  f := ![![![1409, -5154, 3264], ![-602, -11696, 0]], ![![877, -3221, 2040], ![-386, -7310, 0]], ![![369, -1319, 835], ![-131, -2992, 0]]]
  g := ![![![1, 0, 0], ![-27, 43, 0], ![-11, 0, 43]], ![![-1, 1, 0], ![9, -19, 12], ![5, 4, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![8, 1, 0]] ![![43, 0, 0], ![8, 1, 0]]
  ![![43, 0, 0], ![13, 19, 1]] where
 M := ![![![1849, 0, 0], ![344, 43, 0]], ![![344, 43, 0], ![70, 13, 12]]]
 hmul := by decide  
 g := ![![![![30, -19, -1], ![43, 0, 0]], ![![-5, -18, -1], ![43, 0, 0]]], ![![![-5, -18, -1], ![43, 0, 0]], ![![-2, -5, 0], ![12, 0, 0]]]]
 hle2 := by decide  
def MulI43N1 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![13, 19, 1]] ![![43, 0, 0], ![-16, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-688, 43, 0]], ![![559, 817, 43], ![86, -344, 215]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-16, 1, 0]]], ![![![13, 19, 1]], ![![2, -8, 5]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N0, I43N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N0
    exact isPrimeI43N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0 ⊙ MulI43N1)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-26, -15, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-26, -15, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![21, 32, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-26, -15, 1], ![90, 23, -177], ![-2608, -44, -66]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-21, -32, 47]], ![![-1, -1, 1], ![81, 121, -177], ![-26, 44, -66]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [38, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [32, 46], [0, 1]]
 g := ![![[14, 37], [20, 8], [11, 25], [21, 37], [1]], ![[23, 10], [41, 39], [12, 22], [30, 10], [1]]]
 h' := ![![[32, 46], [39, 32], [5, 14], [1, 5], [9, 32], [0, 1]], ![[0, 1], [29, 15], [30, 33], [20, 42], [46, 15], [32, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36]]
 b := ![[], [41, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [38, 15, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![380286, 69050, 28986]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4860, -18266, 28986]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-11, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-11, 1, 0]] 
 ![![47, 0, 0], ![36, 1, 0], ![19, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-11, 1, 0], ![6, -14, 12], ![180, 4, -8]]]
  hmulB := by decide  
  f := ![![![3067, -7598, 6528], ![-846, -25568, 0]], ![![2343, -5810, 4992], ![-657, -19552, 0]], ![![1245, -3072, 2639], ![-320, -10336, 0]]]
  g := ![![![1, 0, 0], ![-36, 47, 0], ![-19, 0, 47]], ![![-1, 1, 0], ![6, -14, 12], ![4, 4, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![-26, -15, 1]] ![![47, 0, 0], ![-11, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![-517, 47, 0]], ![![-1222, -705, 47], ![376, 188, -188]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![-11, 1, 0]]], ![![![-26, -15, 1]], ![![8, 4, -4]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![15, 9, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![15, 9, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![15, 9, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![15, 9, 1], ![234, -8, 111], ![1712, 52, 47]]]
  hmulB := by decide  
  f := ![![![-14, -9, -1], ![53, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-15, -9, 53]], ![![0, 0, 1], ![-27, -19, 111], ![19, -7, 47]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [35, 52, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 52], [0, 1]]
 g := ![![[3, 29], [17], [39, 13], [43], [1, 1]], ![[32, 24], [17], [52, 40], [43], [2, 52]]]
 h' := ![![[1, 52], [51, 33], [13, 21], [38, 38], [18, 19], [0, 1]], ![[0, 1], [31, 20], [34, 32], [23, 15], [37, 34], [1, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [8, 37]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [35, 52, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2371, 1185, -45]
  a := ![-4, 3, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-32, 30, -45]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-5, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-5, 1, 0]] 
 ![![53, 0, 0], ![48, 1, 0], ![6, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-5, 1, 0], ![6, -8, 12], ![180, 4, -2]]]
  hmulB := by decide  
  f := ![![![2123, -2852, 4284], ![-212, -18921, 0]], ![![1919, -2580, 3876], ![-211, -17119, 0]], ![![241, -323, 485], ![-17, -2142, 0]]]
  g := ![![![1, 0, 0], ![-48, 53, 0], ![-6, 0, 53]], ![![-1, 1, 0], ![6, -8, 12], ![0, 4, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![15, 9, 1]] ![![53, 0, 0], ![-5, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-265, 53, 0]], ![![795, 477, 53], ![159, -53, 106]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-5, 1, 0]]], ![![![15, 9, 1]], ![![3, -1, 2]]]]
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


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [19, 19, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 54, 5], [46, 4, 54], [0, 1]]
 g := ![![[43, 36, 5], [11, 12, 51], [21, 27], [34, 29, 16], [1]], ![[56, 24, 17, 53], [42, 53, 52, 16], [20, 25], [4, 36, 52, 9], [4, 51, 10, 7]], ![[21, 44, 48, 33], [4, 8, 47, 18], [26, 28], [11, 34, 28, 14], [27, 25, 33, 52]]]
 h' := ![![[9, 54, 5], [27, 33, 8], [23, 31, 13], [3, 49, 26], [40, 40, 55], [0, 1]], ![[46, 4, 54], [54, 2, 20], [55, 50, 30], [9, 47, 54], [4, 41, 7], [9, 54, 5]], ![[0, 1], [46, 24, 31], [53, 37, 16], [55, 22, 38], [4, 37, 56], [46, 4, 54]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56, 58], []]
 b := ![[], [13, 4, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [19, 19, 4, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-627701, -29972, -15222]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10639, -508, -258]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-23, -21, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-23, -21, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![38, 40, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-23, -21, 1], ![54, 44, -249], ![-3688, -68, -81]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-38, -40, 61]], ![![-1, -1, 1], ![156, 164, -249], ![-10, 52, -81]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [31, 56, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 60], [0, 1]]
 g := ![![[51, 34], [58], [16, 13], [27, 36], [5, 1]], ![[38, 27], [58], [20, 48], [24, 25], [10, 60]]]
 h' := ![![[5, 60], [35, 41], [53, 27], [17, 47], [28, 55], [0, 1]], ![[0, 1], [57, 20], [5, 34], [8, 14], [59, 6], [5, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [40, 45]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [31, 56, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![156381, 29137, 13299]
  a := ![22, -1, 43]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5721, -8243, 13299]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![5, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![5, 1, 0]] 
 ![![61, 0, 0], ![5, 1, 0], ![20, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![5, 1, 0], ![6, 2, 12], ![180, 4, 8]]]
  hmulB := by decide  
  f := ![![![13719, 4586, 27636], ![1220, -140483, 0]], ![![1118, 374, 2256], ![123, -11468, 0]], ![![4495, 1503, 9061], ![437, -46060, 0]]]
  g := ![![![1, 0, 0], ![-5, 61, 0], ![-20, 0, 61]], ![![0, 1, 0], ![-4, 2, 12], ![0, 4, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-23, -21, 1]] ![![61, 0, 0], ![5, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![305, 61, 0]], ![![-1403, -1281, 61], ![-61, -61, -244]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![5, 1, 0]]], ![![![-23, -21, 1]], ![![-1, -1, -4]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![17, 24, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![17, 24, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![17, 24, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![17, 24, 1], ![324, -51, 291], ![4412, 112, 94]]]
  hmulB := by decide  
  f := ![![![-16, -24, -1], ![67, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-17, -24, 67]], ![![0, 0, 1], ![-69, -105, 291], ![42, -32, 94]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [27, 41, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [26, 66], [0, 1]]
 g := ![![[4, 47], [25, 35], [15], [22], [6], [1]], ![[20, 20], [64, 32], [15], [22], [6], [1]]]
 h' := ![![[26, 66], [62, 28], [16, 54], [32, 45], [31, 25], [40, 26], [0, 1]], ![[0, 1], [53, 39], [13, 13], [63, 22], [11, 42], [46, 41], [26, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [5, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [27, 41, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![485, 62, 64]
  a := ![0, 1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-9, -22, 64]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-23, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-23, 1, 0]] 
 ![![67, 0, 0], ![44, 1, 0], ![40, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-23, 1, 0], ![6, -26, 12], ![180, 4, -20]]]
  hmulB := by decide  
  f := ![![![10602, -52351, 24192], ![-4355, -135072, 0]], ![![6950, -34355, 15876], ![-2880, -88641, 0]], ![![6322, -31254, 14443], ![-2622, -80640, 0]]]
  g := ![![![1, 0, 0], ![-44, 67, 0], ![-40, 0, 67]], ![![-1, 1, 0], ![10, -26, 12], ![12, 4, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![17, 24, 1]] ![![67, 0, 0], ![-23, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-1541, 67, 0]], ![![1139, 1608, 67], ![-67, -603, 268]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-23, 1, 0]]], ![![![17, 24, 1]], ![![-1, -9, 4]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1835, 78, 34]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-1835, 78, 34]] 
 ![![71, 0, 0], ![0, 71, 0], ![40, 19, 1]] where
  M :=![![![-1835, 78, 34], ![6588, -1933, 1038], ![17168, 856, -1431]]]
  hmulB := by decide  
  f := ![![![-26445, -1982, -2066]], ![![-383772, -28763, -29982]], ![![-125300, -9391, -9789]]]
  g := ![![![-45, -8, 34], ![-492, -305, 1038], ![1048, 395, -1431]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [45, 32, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 70], [0, 1]]
 g := ![![[37, 30], [48, 37], [32, 1], [9], [30], [1]], ![[0, 41], [0, 34], [0, 70], [9], [30], [1]]]
 h' := ![![[39, 70], [41, 39], [51, 26], [39, 70], [36, 3], [26, 39], [0, 1]], ![[0, 1], [0, 32], [0, 45], [0, 1], [11, 68], [56, 32], [39, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36]]
 b := ![[], [4, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [45, 32, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2254, 1344, 848]
  a := ![5, -2, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-446, -208, 848]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-26445, -1982, -2066]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![-26445, -1982, -2066]] 
 ![![71, 0, 0], ![53, 1, 0], ![40, 0, 1]] where
  M :=![![![-26445, -1982, -2066], ![-383772, -28763, -29982], ![-546832, -40984, -42721]]]
  hmulB := by decide  
  f := ![![![-1835, 78, 34]], ![![-1277, 31, 40]], ![![-792, 56, -1]]]
  g := ![![![2271, -1982, -2066], ![32957, -28763, -29982], ![46960, -40984, -42721]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-1835, 78, 34]] ![![-26445, -1982, -2066]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![7, 1, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![7, 1, 0]] 
 ![![73, 0, 0], ![7, 1, 0], ![59, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![7, 1, 0], ![6, 4, 12], ![180, 4, 10]]]
  hmulB := by decide  
  f := ![![![8730, 5867, 17640], ![949, -107310, 0]], ![![826, 558, 1680], ![147, -10220, 0]], ![![7057, 4742, 14257], ![754, -86730, 0]]]
  g := ![![![1, 0, 0], ![-7, 73, 0], ![-59, 0, 73]], ![![0, 1, 0], ![-10, 4, 12], ![-6, 4, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N0 : Nat.card (O ⧸ I73N0) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N0)

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := prime_ideal_of_norm_prime hp73.out _ NI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![24, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![24, 1, 0]] 
 ![![73, 0, 0], ![24, 1, 0], ![68, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![24, 1, 0], ![6, 21, 12], ![180, 4, 27]]]
  hmulB := by decide  
  f := ![![![5581, 22020, 12600], ![2190, -76650, 0]], ![![1830, 7235, 4140], ![731, -25185, 0]], ![![5204, 20512, 11737], ![2024, -71400, 0]]]
  g := ![![![1, 0, 0], ![-24, 73, 0], ![-68, 0, 73]], ![![0, 1, 0], ![-18, 21, 12], ![-24, 4, 27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1

def I73N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-31, 1, 0]] i)))

def SI73N2: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-31, 1, 0]] 
 ![![73, 0, 0], ![42, 1, 0], ![10, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-31, 1, 0], ![6, -34, 12], ![180, 4, -28]]]
  hmulB := by decide  
  f := ![![![13585, -93744, 33120], ![-7008, -201480, 0]], ![![7818, -53903, 19044], ![-4014, -115851, 0]], ![![1872, -12842, 4537], ![-934, -27600, 0]]]
  g := ![![![1, 0, 0], ![-42, 73, 0], ![-10, 0, 73]], ![![-1, 1, 0], ![18, -34, 12], ![4, 4, -28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N2 : Nat.card (O ⧸ I73N2) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N2)

lemma isPrimeI73N2 : Ideal.IsPrime I73N2 := prime_ideal_of_norm_prime hp73.out _ NI73N2
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![7, 1, 0]] ![![73, 0, 0], ![24, 1, 0]]
  ![![73, 0, 0], ![-22, -22, 1]] where
 M := ![![![5329, 0, 0], ![1752, 73, 0]], ![![511, 73, 0], ![174, 28, 12]]]
 hmul := by decide  
 g := ![![![![73, 0, 0], ![0, 0, 0]], ![![24, 1, 0], ![0, 0, 0]]], ![![![7, 1, 0], ![0, 0, 0]], ![![6, 4, 0], ![12, 0, 0]]]]
 hle2 := by decide  

def MulI73N1 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-22, -22, 1]] ![![73, 0, 0], ![-31, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-2263, 73, 0]], ![![-1606, -1606, 73], ![730, 730, -292]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-31, 1, 0]]], ![![![-22, -22, 1]], ![![10, 10, -4]]]]
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


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [50, 53, 60, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 51, 48], [18, 27, 31], [0, 1]]
 g := ![![[30, 44, 5], [52, 29, 4], [65, 53, 31], [60, 37, 64], [19, 1], []], ![[71, 58, 61, 41], [65, 74, 17, 35], [12, 60, 32, 34], [57, 51, 74, 37], [73, 18], [8, 13]], ![[32, 27, 41, 62], [32, 28, 26, 49], [57, 56, 68, 65], [20, 56, 3, 64], [43, 73], [25, 13]]]
 h' := ![![[1, 51, 48], [7, 23, 59], [68, 71, 77], [2, 30, 49], [77, 49, 71], [0, 0, 1], [0, 1]], ![[18, 27, 31], [31, 73, 11], [68, 35, 36], [73, 38, 77], [0, 5, 3], [75, 55, 27], [1, 51, 48]], ![[0, 1], [60, 62, 9], [38, 52, 45], [40, 11, 32], [72, 25, 5], [22, 24, 51], [18, 27, 31]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 76], []]
 b := ![[], [49, 64, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [50, 53, 60, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-312840, 0, -12640]
  a := ![-5, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3960, 0, -160]
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
  g := ![1, 1, 3, 2, 2, 1, 2, 2, 2, 3, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB262I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0]
    · exact ![I43N0, I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1]
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
    · exact ![50653]
    · exact ![68921]
    · exact ![43, 43, 43]
    · exact ![2209, 47]
    · exact ![2809, 53]
    · exact ![205379]
    · exact ![3721, 61]
    · exact ![4489, 67]
    · exact ![5041, 71]
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
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
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
      exact NI73N1
      exact NI73N2
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
  β := ![I43N0, I43N1, I47N1, I53N1, I61N1, I67N1, I71N1, I73N0, I73N1, I73N2]
  Il := ![[], [], [I43N0, I43N0, I43N1], [I47N1], [I53N1], [], [I61N1], [I67N1], [I71N1], [I73N0, I73N1, I73N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
