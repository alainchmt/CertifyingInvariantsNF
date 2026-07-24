
import IdealArithmetic.Examples.NF3_3_109384_1.RI3_3_109384_1
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [11, 8, 30, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 12, 30], [5, 24, 7], [0, 1]]
 g := ![![[20, 27, 16], [13, 27], [0, 20, 16], [7, 1], []], ![[31, 28, 1, 3], [10, 26], [19, 34, 26, 3], [29, 21], [27, 12]], ![[18, 27, 16, 30], [1, 28], [14, 0, 0, 3], [31, 33], [13, 12]]]
 h' := ![![[2, 12, 30], [5, 6, 33], [0, 11, 29], [34, 7, 4], [0, 0, 1], [0, 1]], ![[5, 24, 7], [5, 14, 10], [35, 16, 27], [23, 31, 10], [3, 33, 24], [2, 12, 30]], ![[0, 1], [26, 17, 31], [0, 10, 18], [4, 36, 23], [30, 4, 12], [5, 24, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21, 25], []]
 b := ![[], [33, 4, 30], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [11, 8, 30, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6253, -2590, -2368]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![169, -70, -64]
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


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [28, 29, 33, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [29, 17, 12], [20, 23, 29], [0, 1]]
 g := ![![[18, 21, 9], [19, 16], [11, 31], [35, 8, 1], []], ![[2, 13, 12, 30], [24, 18], [10, 2], [29, 9, 22, 34], [2, 21]], ![[11, 38, 38, 24], [31, 36], [7, 9], [18, 31, 35, 17], [26, 21]]]
 h' := ![![[29, 17, 12], [26, 29, 38], [36, 12, 4], [4, 32, 20], [0, 0, 1], [0, 1]], ![[20, 23, 29], [29, 6, 33], [39, 6, 31], [27, 5, 24], [6, 12, 23], [29, 17, 12]], ![[0, 1], [32, 6, 11], [30, 23, 6], [29, 4, 38], [0, 29, 17], [20, 23, 29]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29, 17], []]
 b := ![[], [30, 37, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [28, 29, 33, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![183311, -164369, 102541]
  a := ![2, -2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4471, -4009, 2501]
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


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [40, 12, 11, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [35, 7, 16], [40, 35, 27], [0, 1]]
 g := ![![[26, 16, 35], [22, 28, 13], [41, 35], [23, 32, 1], []], ![[3, 17, 1, 11], [19, 7, 33, 15], [2, 1], [16, 1, 29, 35], [31, 41]], ![[6, 24, 32, 32], [23, 40, 15, 7], [29, 14], [14, 17, 38, 33], [20, 41]]]
 h' := ![![[35, 7, 16], [23, 15, 32], [25, 14, 23], [26, 35, 11], [0, 0, 1], [0, 1]], ![[40, 35, 27], [25, 34, 27], [41, 8, 40], [11, 15, 42], [28, 26, 35], [35, 7, 16]], ![[0, 1], [36, 37, 27], [22, 21, 23], [35, 36, 33], [26, 17, 7], [40, 35, 27]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22, 26], []]
 b := ![[], [40, 21, 36], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [40, 12, 11, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-36570468, 114931432, -196283046]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-850476, 2672824, -4564722]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-20, 5, 2]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-20, 5, 2]] 
 ![![47, 0, 0], ![0, 47, 0], ![37, 26, 1]] where
  M :=![![![-20, 5, 2], ![-73, 30, 12], ![-209, 111, 35]]]
  hmulB := by decide  
  f := ![![![-6, 1, 0]], ![![1, -6, 2]], ![![-5, -2, 1]]]
  g := ![![![-2, -1, 2], ![-11, -6, 12], ![-32, -17, 35]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [25, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 46], [0, 1]]
 g := ![![[36, 32], [26, 25], [43, 34], [7, 2], [1]], ![[0, 15], [39, 22], [40, 13], [40, 45], [1]]]
 h' := ![![[40, 46], [8, 28], [6, 5], [13, 9], [22, 40], [0, 1]], ![[0, 1], [0, 19], [18, 42], [44, 38], [24, 7], [40, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [37, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [25, 7, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![231, -422, 602]
  a := ![-2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-469, -342, 602]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-6, 1, 0]] 
 ![![47, 0, 0], ![41, 1, 0], ![6, 0, 1]] where
  M :=![![![-6, 1, 0], ![1, -6, 2], ![-39, 25, -5]]]
  hmulB := by decide  
  f := ![![![-20, 5, 2]], ![![-19, 5, 2]], ![![-7, 3, 1]]]
  g := ![![![-1, 1, 0], ![5, -6, 2], ![-22, 25, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-20, 5, 2]] ![![-6, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![47, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![169, -118, 28]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![169, -118, 28]] 
 ![![53, 0, 0], ![0, 53, 0], ![42, 45, 1]] where
  M :=![![![169, -118, 28], ![-1210, 869, -208], ![4406, -3146, 751]]]
  hmulB := by decide  
  f := ![![![33, -10, -4]], ![![146, -67, -24]], ![![158, -69, -25]]]
  g := ![![![-19, -26, 28], ![142, 193, -208], ![-512, -697, 751]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [32, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 52], [0, 1]]
 g := ![![[], [44], [], [17], [0, 1]], ![[], [44], [], [17], [0, 52]]]
 h' := ![![[0, 52], [23], [0, 37], [39], [0, 21], [0, 1]], ![[0, 1], [23], [0, 16], [39], [0, 32], [0, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [0, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [32, 0, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-150, 74, 110]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-90, -92, 110]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![33, -10, -4]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![33, -10, -4]] 
 ![![53, 0, 0], ![15, 1, 0], ![47, 0, 1]] where
  M :=![![![33, -10, -4], ![146, -67, -24], ![418, -222, -77]]]
  hmulB := by decide  
  f := ![![![169, -118, 28]], ![![25, -17, 4]], ![![233, -164, 39]]]
  g := ![![![7, -10, -4], ![43, -67, -24], ![139, -222, -77]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![169, -118, 28]] ![![33, -10, -4]]
  ![![53, 0, 0]] where
 M := ![![![53, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [34, 57, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [42, 11, 31], [15, 47, 28], [0, 1]]
 g := ![![[30, 35, 9], [56, 43, 25], [54, 48], [3, 43, 4], [1]], ![[52, 4, 21, 37], [55, 57, 9, 32], [19, 35], [7, 27, 30, 2], [24, 36, 38, 55]], ![[11, 55, 30, 51], [7, 20, 41, 46], [7, 41], [25, 44, 43, 36], [34, 8, 29, 4]]]
 h' := ![![[42, 11, 31], [43, 58, 3], [13, 27, 5], [16, 54, 44], [25, 2, 57], [0, 1]], ![[15, 47, 28], [26, 18, 51], [48, 11, 10], [35, 36, 25], [53, 42, 27], [42, 11, 31]], ![[0, 1], [27, 42, 5], [23, 21, 44], [5, 28, 49], [36, 15, 34], [15, 47, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42, 40], []]
 b := ![[], [18, 44, 52], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [34, 57, 2, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1114628, 635666, 210276]
  a := ![2, 19, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-18892, 10774, 3564]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, -28, -10]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![53, -28, -10]] 
 ![![61, 0, 0], ![0, 61, 0], ![13, 15, 1]] where
  M :=![![![53, -28, -10], ![362, -197, -66], ![1162, -630, -225]]]
  hmulB := by decide  
  f := ![![![45, 0, -2]], ![![78, -5, -2]], ![![29, -1, -1]]]
  g := ![![![3, 2, -10], ![20, 13, -66], ![67, 45, -225]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [16, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [37, 60], [0, 1]]
 g := ![![[32, 42], [20], [4, 34], [54, 60], [37, 1]], ![[0, 19], [20], [42, 27], [17, 1], [13, 60]]]
 h' := ![![[37, 60], [55, 15], [58, 9], [51, 20], [18, 11], [0, 1]], ![[0, 1], [0, 46], [25, 52], [59, 41], [59, 50], [37, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [60, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [16, 24, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![620, -453, 165]
  a := ![-2, 3, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-25, -48, 165]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-45, 0, 2]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![-45, 0, 2]] 
 ![![61, 0, 0], ![30, 1, 0], ![8, 0, 1]] where
  M :=![![![-45, 0, 2], ![-78, 5, 2], ![-14, -14, 5]]]
  hmulB := by decide  
  f := ![![![-53, 28, 10]], ![![-32, 17, 6]], ![![-26, 14, 5]]]
  g := ![![![-1, 0, 2], ![-4, 5, 2], ![6, -14, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![53, -28, -10]] ![![-45, 0, 2]]
  ![![61, 0, 0]] where
 M := ![![![-61, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, -86, 16]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![223, -86, 16]] 
 ![![67, 0, 0], ![18, 1, 0], ![6, 0, 1]] where
  M :=![![![223, -86, 16], ![-710, 623, -156], ![3242, -2262, 537]]]
  hmulB := by decide  
  f := ![![![18321, -9990, -3448]], ![![6780, -3697, -1276]], ![![7816, -4262, -1471]]]
  g := ![![![25, -86, 16], ![-164, 623, -156], ![608, -2262, 537]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N0 : Nat.card (O ⧸ I67N0) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N0)

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := prime_ideal_of_norm_prime hp67.out _ NI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, -42, 10]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![59, -42, 10]] 
 ![![67, 0, 0], ![57, 1, 0], ![51, 0, 1]] where
  M :=![![![59, -42, 10], ![-432, 309, -74], ![1568, -1120, 267]]]
  hmulB := by decide  
  f := ![![![377, -14, -18]], ![![331, -13, -16]], ![![297, -14, -15]]]
  g := ![![![29, -42, 10], ![-213, 309, -74], ![773, -1120, 267]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1

def I67N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![20, 17, -6]] i)))

def SI67N2: IdealEqSpanCertificate' Table ![![20, 17, -6]] 
 ![![67, 0, 0], ![58, 1, 0], ![27, 0, 1]] where
  M :=![![![20, 17, -6], ![251, -130, 28], ![-621, 467, -113]]]
  hmulB := by decide  
  f := ![![![-1614, 881, 304]], ![![-1561, 852, 294]], ![![-1195, 652, 225]]]
  g := ![![![-12, 17, -6], ![105, -130, 28], ![-368, 467, -113]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N2 : Nat.card (O ⧸ I67N2) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N2)

lemma isPrimeI67N2 : Ideal.IsPrime I67N2 := prime_ideal_of_norm_prime hp67.out _ NI67N2
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![223, -86, 16]] ![![59, -42, 10]]
  ![![75397, -53860, 12866]] where
 M := ![![![75397, -53860, 12866]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![75397, -53860, 12866]] ![![20, 17, -6]]
  ![![67, 0, 0]] where
 M := ![![![-20000706, 14291971, -3414320]]]
 hmul := by decide  
 g := ![![![![-298518, 213313, -50960]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![543, -296, -102]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![543, -296, -102]] 
 ![![71, 0, 0], ![0, 71, 0], ![26, 21, 1]] where
  M :=![![![543, -296, -102], ![3682, -2007, -694], ![12258, -6686, -2303]]]
  hmulB := by decide  
  f := ![![![253, -4, -10]], ![![386, 3, -18]], ![![210, -1, -9]]]
  g := ![![![45, 26, -102], ![306, 177, -694], ![1016, 587, -2303]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [65, 55, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 70], [0, 1]]
 g := ![![[50, 58], [51, 8], [37, 38], [3], [43], [1]], ![[55, 13], [37, 63], [6, 33], [3], [43], [1]]]
 h' := ![![[16, 70], [22, 22], [9, 47], [47, 40], [10, 28], [6, 16], [0, 1]], ![[0, 1], [19, 49], [51, 24], [48, 31], [32, 43], [49, 55], [16, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [67, 36]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [65, 55, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-244, 147, 646]
  a := ![2, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-240, -189, 646]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![253, -4, -10]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![253, -4, -10]] 
 ![![71, 0, 0], ![28, 1, 0], ![70, 0, 1]] where
  M :=![![![253, -4, -10], ![386, 3, -18], ![226, -30, -1]]]
  hmulB := by decide  
  f := ![![![543, -296, -102]], ![![266, -145, -50]], ![![708, -386, -133]]]
  g := ![![![15, -4, -10], ![22, 3, -18], ![16, -30, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![543, -296, -102]] ![![253, -4, -10]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![52, -29, -8]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![52, -29, -8]] 
 ![![73, 0, 0], ![0, 73, 0], ![30, 31, 1]] where
  M :=![![![52, -29, -8], ![283, -148, -66], ![1187, -669, -177]]]
  hmulB := by decide  
  f := ![![![246, -3, -10]], ![![387, -4, -16]], ![![268, -3, -11]]]
  g := ![![![4, 3, -8], ![31, 26, -66], ![89, 66, -177]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [9, 49, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 72], [0, 1]]
 g := ![![[46, 65], [50], [9], [26, 67], [65], [1]], ![[0, 8], [50], [9], [28, 6], [65], [1]]]
 h' := ![![[24, 72], [65, 49], [71, 14], [58, 70], [7, 33], [64, 24], [0, 1]], ![[0, 1], [0, 24], [42, 59], [59, 3], [69, 40], [56, 49], [24, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20]]
 b := ![[], [26, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [9, 49, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-386, -175, 430]
  a := ![-5, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-182, -185, 430]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![246, -3, -10]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![246, -3, -10]] 
 ![![73, 0, 0], ![10, 1, 0], ![60, 0, 1]] where
  M :=![![![246, -3, -10], ![387, -4, -16], ![187, -5, -7]]]
  hmulB := by decide  
  f := ![![![52, -29, -8]], ![![11, -6, -2]], ![![59, -33, -9]]]
  g := ![![![12, -3, -10], ![19, -4, -16], ![9, -5, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![52, -29, -8]] ![![246, -3, -10]]
  ![![73, 0, 0]] where
 M := ![![![73, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


lemma PB74I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 73 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 73 (by omega)

def PB74I1 : PrimesBelowBoundCertificateInterval O 31 73 74 where
  m := 10
  g := ![1, 1, 1, 2, 2, 1, 2, 3, 2, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73]
  hP := PB74I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0]
    · exact ![I43N0]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1, I67N2]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![50653]
    · exact ![68921]
    · exact ![79507]
    · exact ![2209, 47]
    · exact ![2809, 53]
    · exact ![205379]
    · exact ![3721, 61]
    · exact ![67, 67, 67]
    · exact ![5041, 71]
    · exact ![5329, 73]
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
      exact NI67N2
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
  β := ![I47N1, I53N1, I61N1, I67N0, I67N1, I67N2, I71N1, I73N1]
  Il := ![[], [], [], [I47N1], [I53N1], [], [I61N1], [I67N0, I67N1, I67N2], [I71N1], [I73N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
