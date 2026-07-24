
import IdealArithmetic.Examples.NF3_1_662796_4.RI3_1_662796_4
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-78, 6, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-78, 6, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![33, 6, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-78, 6, 1], ![494, 36, 6], ![2964, 1178, 36]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![3, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-33, -6, 37]], ![![-3, 0, 1], ![8, 0, 6], ![48, 26, 36]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [36, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [36, 36], [0, 1]]
 g := ![![[36, 36], [9], [16, 9], [1], [1]], ![[0, 1], [9], [7, 28], [1], [1]]]
 h' := ![![[36, 36], [6, 6], [16, 34], [2, 34], [1, 36], [0, 1]], ![[0, 1], [0, 31], [19, 3], [5, 3], [2, 1], [36, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [22, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [36, 1, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1024, 721, 114]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-74, 1, 114]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-6, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-6, 1, 0]] 
 ![![37, 0, 0], ![31, 1, 0], ![1, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-6, 1, 0], ![0, -6, 1], ![494, 114, -6]]]
  hmulB := by decide  
  f := ![![![199, -33, 0], ![1221, 0, 0]], ![![169, -28, 0], ![1037, 0, 0]], ![![7, -1, 0], ![43, 1, 0]]]
  g := ![![![1, 0, 0], ![-31, 37, 0], ![-1, 0, 37]], ![![-1, 1, 0], ![5, -6, 1], ![-82, 114, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![-78, 6, 1]] ![![37, 0, 0], ![-6, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-222, 37, 0]], ![![-2886, 222, 37], ![962, 0, 0]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-6, 1, 0]]], ![![![-78, 6, 1]], ![![26, 0, 0]]]]
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


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [22, 10, 16, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 16, 6], [7, 24, 35], [0, 1]]
 g := ![![[29, 35, 23], [30, 9], [31, 20], [0, 25, 1], []], ![[37, 18, 1, 26], [], [3, 21], [26, 11, 20, 12], [26, 36]], ![[31, 8, 26, 24], [27, 9], [40, 32], [7, 21, 8, 22], [38, 36]]]
 h' := ![![[18, 16, 6], [16, 3, 33], [15, 29, 3], [0, 24, 15], [0, 0, 1], [0, 1]], ![[7, 24, 35], [4, 2, 31], [39, 20], [33, 9, 12], [39, 16, 24], [18, 16, 6]], ![[0, 1], [19, 36, 18], [30, 33, 38], [7, 8, 14], [33, 25, 16], [7, 24, 35]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 5], []]
 b := ![[], [22, 11, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [22, 10, 16, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3466919, 2396204, 341653]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![84559, 58444, 8333]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0]] 
 ![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [5, 22, 33, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 7, 34], [34, 35, 9], [0, 1]]
 g := ![![[22, 42, 36], [39, 40, 41], [12, 16], [35, 10, 1], []], ![[29, 7, 17, 5], [20, 10, 28, 29], [31, 41], [15, 3, 29, 26], [39, 38]], ![[15, 20, 28, 38], [31, 8, 1, 25], [41, 15], [40, 8, 38, 11], [21, 38]]]
 h' := ![![[19, 7, 34], [20, 38, 6], [35, 18, 16], [40, 40, 39], [0, 0, 1], [0, 1]], ![[34, 35, 9], [18, 3, 40], [23, 41, 11], [7, 11, 16], [37, 35, 35], [19, 7, 34]], ![[0, 1], [7, 2, 40], [5, 27, 16], [34, 35, 31], [19, 8, 7], [34, 35, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 12], []]
 b := ![[], [42, 31, 30], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [5, 22, 33, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-45881, -109220, -38227]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1067, -2540, -889]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-97, -8, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-97, -8, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![44, 39, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-97, -8, 1], ![494, 17, -8], ![-3952, -418, 17]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![3, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-44, -39, 47]], ![![-3, -1, 1], ![18, 7, -8], ![-100, -23, 17]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [43, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [35, 46], [0, 1]]
 g := ![![[44, 8], [13, 32], [19, 8], [9, 3], [1]], ![[42, 39], [5, 15], [17, 39], [20, 44], [1]]]
 h' := ![![[35, 46], [5, 14], [29, 19], [36, 14], [4, 35], [0, 1]], ![[0, 1], [25, 33], [36, 28], [9, 33], [7, 12], [35, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [34, 37]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [43, 12, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2908, 3776, 985]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-984, -737, 985]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![8, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![8, 1, 0]] 
 ![![47, 0, 0], ![8, 1, 0], ![30, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![8, 1, 0], ![0, 8, 1], ![494, 114, 8]]]
  hmulB := by decide  
  f := ![![![33, 4, 0], ![-188, 0, 0]], ![![-8, -1, 0], ![48, 0, 0]], ![![18, 2, 0], ![-102, 1, 0]]]
  g := ![![![1, 0, 0], ![-8, 47, 0], ![-30, 0, 47]], ![![0, 1, 0], ![-2, 8, 1], ![-14, 114, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![-97, -8, 1]] ![![47, 0, 0], ![8, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![376, 47, 0]], ![![-4559, -376, 47], ![-282, -47, 0]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![8, 1, 0]]], ![![![-97, -8, 1]], ![![-6, -1, 0]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-55, 18, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-55, 18, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![51, 18, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-55, 18, 1], ![494, 59, 18], ![8892, 2546, 59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-51, -18, 53]], ![![-2, 0, 1], ![-8, -5, 18], ![111, 28, 59]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [38, 45, 1] where
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
 g := ![![[50, 7], [4], [15, 38], [40], [8, 1]], ![[0, 46], [4], [1, 15], [40], [16, 52]]]
 h' := ![![[8, 52], [17, 31], [13, 2], [1, 41], [14, 26], [0, 1]], ![[0, 1], [0, 22], [29, 51], [11, 12], [10, 27], [8, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41]]
 b := ![[], [24, 47]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [38, 45, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1026, 677, 70]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-48, -11, 70]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-18, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-18, 1, 0]] 
 ![![53, 0, 0], ![35, 1, 0], ![47, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-18, 1, 0], ![0, -18, 1], ![494, 114, -18]]]
  hmulB := by decide  
  f := ![![![91, -5, 0], ![265, 0, 0]], ![![73, -4, 0], ![213, 0, 0]], ![![97, -5, 0], ![283, 1, 0]]]
  g := ![![![1, 0, 0], ![-35, 53, 0], ![-47, 0, 53]], ![![-1, 1, 0], ![11, -18, 1], ![-50, 114, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![-55, 18, 1]] ![![53, 0, 0], ![-18, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-954, 53, 0]], ![![-2915, 954, 53], ![1484, -265, 0]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-18, 1, 0]]], ![![![-55, 18, 1]], ![![28, -5, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-73, -10, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-73, -10, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![45, 49, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-73, -10, 1], ![494, 41, -10], ![-4940, -646, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-45, -49, 59]], ![![-2, -1, 1], ![16, 9, -10], ![-115, -45, 41]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [58, 34, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [25, 58], [0, 1]]
 g := ![![[25, 46], [53, 26], [25], [39, 57], [25, 1]], ![[54, 13], [54, 33], [25], [48, 2], [50, 58]]]
 h' := ![![[25, 58], [53, 20], [12, 12], [39, 5], [25, 36], [0, 1]], ![[0, 1], [22, 39], [17, 47], [46, 54], [40, 23], [25, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [43, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [58, 34, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![18865, 5510, 511]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-70, -331, 511]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![10, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![10, 1, 0]] 
 ![![59, 0, 0], ![10, 1, 0], ![18, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![10, 1, 0], ![0, 10, 1], ![494, 114, 10]]]
  hmulB := by decide  
  f := ![![![41, 4, 0], ![-236, 0, 0]], ![![-10, -1, 0], ![60, 0, 0]], ![![2, 0, 0], ![-10, 1, 0]]]
  g := ![![![1, 0, 0], ![-10, 59, 0], ![-18, 0, 59]], ![![0, 1, 0], ![-2, 10, 1], ![-14, 114, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-73, -10, 1]] ![![59, 0, 0], ![10, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![590, 59, 0]], ![![-4307, -590, 59], ![-236, -59, 0]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![10, 1, 0]]], ![![![-73, -10, 1]], ![![-4, -1, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-92, -12, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-92, -12, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![30, 49, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-92, -12, 1], ![494, 22, -12], ![-5928, -874, 22]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-30, -49, 61]], ![![-2, -1, 1], ![14, 10, -12], ![-108, -32, 22]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [17, 50, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 60], [0, 1]]
 g := ![![[46, 48], [57], [45, 41], [48, 19], [11, 1]], ![[25, 13], [57], [8, 20], [13, 42], [22, 60]]]
 h' := ![![[11, 60], [59, 29], [28, 22], [38, 38], [57, 43], [0, 1]], ![[0, 1], [12, 32], [26, 39], [29, 23], [42, 18], [11, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31]]
 b := ![[], [52, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [17, 50, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2996, -46, 75]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-86, -61, 75]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![12, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![12, 1, 0]] 
 ![![61, 0, 0], ![12, 1, 0], ![39, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![12, 1, 0], ![0, 12, 1], ![494, 114, 12]]]
  hmulB := by decide  
  f := ![![![433, 36, 0], ![-2196, 0, 0]], ![![84, 7, 0], ![-426, 0, 0]], ![![267, 22, 0], ![-1354, 1, 0]]]
  g := ![![![1, 0, 0], ![-12, 61, 0], ![-39, 0, 61]], ![![0, 1, 0], ![-3, 12, 1], ![-22, 114, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-92, -12, 1]] ![![61, 0, 0], ![12, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![732, 61, 0]], ![![-5612, -732, 61], ![-610, -122, 0]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![12, 1, 0]]], ![![![-92, -12, 1]], ![![-10, -2, 0]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![32, 1, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![32, 1, 0]] 
 ![![67, 0, 0], ![32, 1, 0], ![48, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![32, 1, 0], ![0, 32, 1], ![494, 114, 32]]]
  hmulB := by decide  
  f := ![![![641, 20, 0], ![-1340, 0, 0]], ![![288, 9, 0], ![-602, 0, 0]], ![![464, 14, 0], ![-970, 1, 0]]]
  g := ![![![1, 0, 0], ![-32, 67, 0], ![-48, 0, 67]], ![![0, 1, 0], ![-16, 32, 1], ![-70, 114, 32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N0 : Nat.card (O ⧸ I67N0) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N0)

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := prime_ideal_of_norm_prime hp67.out _ NI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-20, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-20, 1, 0]] 
 ![![67, 0, 0], ![47, 1, 0], ![2, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-20, 1, 0], ![0, -20, 1], ![494, 114, -20]]]
  hmulB := by decide  
  f := ![![![1261, -63, 0], ![4221, 0, 0]], ![![881, -44, 0], ![2949, 0, 0]], ![![46, -2, 0], ![154, 1, 0]]]
  g := ![![![1, 0, 0], ![-47, 67, 0], ![-2, 0, 67]], ![![-1, 1, 0], ![14, -20, 1], ![-72, 114, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1

def I67N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-12, 1, 0]] i)))

def SI67N2: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-12, 1, 0]] 
 ![![67, 0, 0], ![55, 1, 0], ![57, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-12, 1, 0], ![0, -12, 1], ![494, 114, -12]]]
  hmulB := by decide  
  f := ![![![409, -34, 0], ![2278, 0, 0]], ![![349, -29, 0], ![1944, 0, 0]], ![![363, -30, 0], ![2022, 1, 0]]]
  g := ![![![1, 0, 0], ![-55, 67, 0], ![-57, 0, 67]], ![![-1, 1, 0], ![9, -12, 1], ![-76, 114, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N2 : Nat.card (O ⧸ I67N2) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N2)

lemma isPrimeI67N2 : Ideal.IsPrime I67N2 := prime_ideal_of_norm_prime hp67.out _ NI67N2
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![32, 1, 0]] ![![67, 0, 0], ![-20, 1, 0]]
  ![![67, 0, 0], ![-104, 12, 1]] where
 M := ![![![4489, 0, 0], ![-1340, 67, 0]], ![![2144, 67, 0], ![-640, 12, 1]]]
 hmul := by decide  
 g := ![![![![67, 0, 0], ![0, 0, 0]], ![![84, -11, -1], ![67, 0, 0]]], ![![![32, 1, 0], ![0, 0, 0]], ![![96, -12, -1], ![68, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![-104, 12, 1]] ![![67, 0, 0], ![-12, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-804, 67, 0]], ![![-6968, 804, 67], ![1742, -134, 0]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-12, 1, 0]]], ![![![-104, 12, 1]], ![![26, -2, 0]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1, I67N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
    exact isPrimeI67N2
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


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [54, 58, 41, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 33, 29], [24, 37, 42], [0, 1]]
 g := ![![[63, 19, 15], [30, 9, 36], [14, 48, 49], [43, 29], [30, 1], []], ![[13, 3, 4, 29], [45, 9, 2, 43], [7, 40, 45, 32], [35, 4], [26, 20], [22, 60]], ![[40, 61, 70, 22], [52, 14, 47, 46], [53, 67, 18, 13], [8, 64], [0, 24], [9, 60]]]
 h' := ![![[6, 33, 29], [13, 32, 21], [25, 36, 65], [48, 61, 64], [13, 52, 61], [0, 0, 1], [0, 1]], ![[24, 37, 42], [11, 20, 1], [53, 64, 41], [29, 39, 19], [59, 32, 2], [55, 69, 37], [6, 33, 29]], ![[0, 1], [44, 19, 49], [65, 42, 36], [30, 42, 59], [6, 58, 8], [19, 2, 33], [24, 37, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 27], []]
 b := ![[], [63, 28, 26], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [54, 58, 41, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2709644, 1159856, 129433]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![38164, 16336, 1823]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-65, 7, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-65, 7, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![8, 7, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-65, 7, 1], ![494, 49, 7], ![3458, 1292, 49]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-8, -7, 73]], ![![-1, 0, 1], ![6, 0, 7], ![42, 13, 49]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [43, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [67, 72], [0, 1]]
 g := ![![[29, 32], [23], [27], [52, 64], [36], [1]], ![[56, 41], [23], [27], [33, 9], [36], [1]]]
 h' := ![![[67, 72], [69, 18], [6, 13], [27, 10], [9, 8], [30, 67], [0, 1]], ![[0, 1], [34, 55], [1, 60], [40, 63], [34, 65], [66, 6], [67, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58]]
 b := ![[], [14, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [43, 6, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-19701, -2684, 576]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-333, -92, 576]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-7, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-7, 1, 0]] 
 ![![73, 0, 0], ![66, 1, 0], ![24, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-7, 1, 0], ![0, -7, 1], ![494, 114, -7]]]
  hmulB := by decide  
  f := ![![![176, -25, 0], ![1825, 0, 0]], ![![162, -23, 0], ![1680, 0, 0]], ![![64, -9, 0], ![664, 1, 0]]]
  g := ![![![1, 0, 0], ![-66, 73, 0], ![-24, 0, 73]], ![![-1, 1, 0], ![6, -7, 1], ![-94, 114, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-65, 7, 1]] ![![73, 0, 0], ![-7, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-511, 73, 0]], ![![-4745, 511, 73], ![949, 0, 0]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-7, 1, 0]]], ![![![-65, 7, 1]], ![![13, 0, 0]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-92, -38, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-92, -38, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![66, 41, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-92, -38, 1], ![494, 22, -38], ![-18772, -3838, 22]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-66, -41, 79]], ![![-2, -1, 1], ![38, 20, -38], ![-256, -60, 22]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [1, 43, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [36, 78], [0, 1]]
 g := ![![[43, 1], [43, 1], [43, 1], [36, 44], [32], [1]], ![[0, 78], [0, 78], [0, 78], [40, 35], [32], [1]]]
 h' := ![![[36, 78], [36, 78], [36, 78], [43, 1], [48, 53], [78, 36], [0, 1]], ![[0, 1], [0, 1], [0, 1], [0, 78], [60, 26], [31, 43], [36, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45]]
 b := ![[], [69, 62]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [1, 43, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-259, 197, 184]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-157, -93, 184]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![38, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![38, 1, 0]] 
 ![![79, 0, 0], ![38, 1, 0], ![57, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![38, 1, 0], ![0, 38, 1], ![494, 114, 38]]]
  hmulB := by decide  
  f := ![![![913, 24, 0], ![-1896, 0, 0]], ![![418, 11, 0], ![-868, 0, 0]], ![![627, 16, 0], ![-1302, 1, 0]]]
  g := ![![![1, 0, 0], ![-38, 79, 0], ![-57, 0, 79]], ![![0, 1, 0], ![-19, 38, 1], ![-76, 114, 38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-92, -38, 1]] ![![79, 0, 0], ![38, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![3002, 79, 0]], ![![-7268, -3002, 79], ![-3002, -1422, 0]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![38, 1, 0]]], ![![![-92, -38, 1]], ![![-38, -18, 0]]]]
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


lemma PB231I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB231I1 : PrimesBelowBoundCertificateInterval O 31 79 231 where
  m := 11
  g := ![2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB231I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0]
    · exact ![I43N0]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1, I67N2]
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
    · exact ![79507]
    · exact ![2209, 47]
    · exact ![2809, 53]
    · exact ![3481, 59]
    · exact ![3721, 61]
    · exact ![67, 67, 67]
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
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
      exact NI67N2
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
  β := ![I37N1, I47N1, I53N1, I59N1, I61N1, I67N0, I67N1, I67N2, I73N1, I79N1]
  Il := ![[I37N1], [], [], [I47N1], [I53N1], [I59N1], [I61N1], [I67N0, I67N1, I67N2], [], [I73N1], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
