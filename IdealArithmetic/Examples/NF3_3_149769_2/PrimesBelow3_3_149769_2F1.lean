
import IdealArithmetic.Examples.NF3_3_149769_2.RI3_3_149769_2
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [22, 35, 36, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 11, 8], [30, 25, 29], [0, 1]]
 g := ![![[3, 25, 34], [17, 36], [27, 0, 9], [1, 1], []], ![[6, 32], [11, 11], [9, 5, 32, 6], [25, 33], [18, 27]], ![[13, 27, 15, 24], [16, 30], [20, 14, 22, 6], [15, 10], [34, 27]]]
 h' := ![![[8, 11, 8], [0, 13, 21], [35, 20, 6], [15, 17, 3], [0, 0, 1], [0, 1]], ![[30, 25, 29], [14, 2], [16, 0, 14], [6, 3, 26], [1, 25, 25], [8, 11, 8]], ![[0, 1], [30, 22, 16], [30, 17, 17], [19, 17, 8], [4, 12, 11], [30, 25, 29]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29, 4], []]
 b := ![[], [36, 16, 18], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [22, 35, 36, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-489103, -166574, -14060]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-13219, -4502, -380]
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


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [12, 2, 8, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 39, 2], [40, 1, 39], [0, 1]]
 g := ![![[4, 13, 33], [3, 25], [], [21, 33, 1], []], ![[23, 12, 25, 1], [36, 31], [5, 20], [9, 32, 17, 2], [1, 4]], ![[35, 39, 3, 5], [18, 20], [25, 20], [19, 17, 39, 33], [5, 4]]]
 h' := ![![[34, 39, 2], [30, 24, 22], [36, 8, 5], [35, 13], [0, 0, 1], [0, 1]], ![[40, 1, 39], [20, 1, 29], [1, 38, 21], [26, 15, 26], [37, 19, 1], [34, 39, 2]], ![[0, 1], [20, 16, 31], [20, 36, 15], [22, 13, 15], [23, 22, 39], [40, 1, 39]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 20], []]
 b := ![[], [8, 0, 31], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [12, 2, 8, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4504998, 3031909, 429557]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![109878, 73949, 10477]
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


def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![0, 1, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![0, 1, 0]] 
 ![![43, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![0, 1, 0], ![0, 0, 1], ![559, 129, 0]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, 0], ![0, 1, 0]]]
  g := ![![![1, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![0, 1, 0], ![0, 0, 1], ![13, 129, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N0)

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := prime_ideal_of_norm_prime hp43.out _ NI43N0
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![0, 1, 0]] ![![43, 0, 0], ![0, 1, 0]]
  ![![43, 0, 0], ![-86, 0, 1]] where
 M := ![![![1849, 0, 0], ![0, 43, 0]], ![![0, 43, 0], ![0, 0, 1]]]
 hmul := by decide  
 g := ![![![![-9, -4, 0], ![0, 4, 0]], ![![0, 1, 0], ![0, 0, 0]]], ![![![0, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  
def MulI43N1 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-86, 0, 1]] ![![43, 0, 0], ![0, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![0, 43, 0]], ![![-3698, 0, 43], ![559, 43, 0]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![0, 1, 0]]], ![![![-86, 0, 1]], ![![13, 1, 0]]]]
 hle2 := by decide  

def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N0, I43N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N0
    exact isPrimeI43N0
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


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [41, 4, 27, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 40, 2], [40, 6, 45], [0, 1]]
 g := ![![[28, 37, 18], [19, 22, 1], [20, 34, 9], [20, 20, 1], []], ![[21, 23, 1, 34], [39, 16, 25, 34], [32, 3, 41, 27], [23, 32, 14, 25], [5, 4]], ![[28, 41, 24, 38], [25, 31, 22, 26], [45, 24, 3, 41], [32, 2, 17, 43], [9, 4]]]
 h' := ![![[27, 40, 2], [20, 27, 21], [26, 1, 1], [26, 40, 44], [0, 0, 1], [0, 1]], ![[40, 6, 45], [3, 41, 39], [13, 42, 8], [4, 43, 15], [7, 2, 6], [27, 40, 2]], ![[0, 1], [20, 26, 34], [28, 4, 38], [1, 11, 35], [9, 45, 40], [40, 6, 45]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29, 4], []]
 b := ![[], [3, 41, 45], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [41, 4, 27, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-62886, -136676, -45637]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1338, -2908, -971]
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


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [22, 9, 29, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [38, 17, 39], [39, 35, 14], [0, 1]]
 g := ![![[32, 37, 15], [27, 6], [23, 51, 25], [36, 46], [1]], ![[10, 18, 12, 8], [22, 10], [28, 8, 29, 27], [28, 38], [50, 23, 2, 12]], ![[52, 39, 0, 35], [48, 7], [49, 44, 5, 33], [32, 24], [41, 16, 46, 41]]]
 h' := ![![[38, 17, 39], [35, 46, 42], [24, 43, 35], [10, 14, 5], [31, 44, 24], [0, 1]], ![[39, 35, 14], [8, 7, 31], [11, 41, 40], [19, 41, 32], [30, 25, 12], [38, 17, 39]], ![[0, 1], [10, 0, 33], [35, 22, 31], [0, 51, 16], [11, 37, 17], [39, 35, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19, 32], []]
 b := ![[], [49, 47, 25], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [22, 9, 29, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6596698, -3313295, -398401]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-124466, -62515, -7517]
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


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [32, 26, 22, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 25, 31], [18, 33, 28], [0, 1]]
 g := ![![[16, 42, 1], [47, 53, 26], [31, 5], [53, 54, 12], [1]], ![[54, 30, 47, 18], [12, 56, 39, 34], [54, 21], [56, 35, 20, 6], [12, 7, 6, 55]], ![[20, 15, 18, 3], [16, 14, 52, 3], [16, 7], [17, 52, 49, 49], [37, 29, 2, 4]]]
 h' := ![![[19, 25, 31], [30, 32, 1], [0, 58, 12], [15, 42, 8], [27, 33, 37], [0, 1]], ![[18, 33, 28], [6, 12, 22], [8, 18, 11], [5, 56, 32], [44, 48, 2], [19, 25, 31]], ![[0, 1], [18, 15, 36], [6, 42, 36], [20, 20, 19], [46, 37, 20], [18, 33, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34, 54], []]
 b := ![[], [8, 17, 23], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [32, 26, 22, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-504745, -178003, -15871]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-8555, -3017, -269]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0]] 
 ![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [28, 33, 44, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [43, 18, 17], [35, 42, 44], [0, 1]]
 g := ![![[5, 32, 25], [23, 16], [56, 3, 12], [25, 9, 45], [1]], ![[27, 15, 27, 11], [38, 19], [9, 15, 41, 29], [34, 60, 23, 50], [26, 46, 2, 33]], ![[22, 15, 53, 32], [27, 13], [36, 47, 9, 33], [24, 58, 10, 55], [5, 19, 46, 28]]]
 h' := ![![[43, 18, 17], [46, 21, 56], [18, 7, 4], [32, 12, 45], [33, 28, 17], [0, 1]], ![[35, 42, 44], [20, 16, 25], [13, 13, 43], [3, 58, 20], [28, 39, 31], [43, 18, 17]], ![[0, 1], [46, 24, 41], [58, 41, 14], [52, 52, 57], [35, 55, 13], [35, 42, 44]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 2], []]
 b := ![[], [57, 27, 25], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [28, 33, 44, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9255469, 2841990, 211365]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![151729, 46590, 3465]
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


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [32, 59, 60, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [59, 35, 40], [15, 31, 27], [0, 1]]
 g := ![![[17, 0, 40], [29, 26, 26], [12, 6], [19, 33], [7, 1], []], ![[56, 17, 58, 25], [25, 41, 8, 56], [23, 24], [6, 65], [59, 23], [64, 59]], ![[12, 5, 13, 48], [44, 13, 39, 42], [33, 6], [66, 29], [45, 19], [10, 59]]]
 h' := ![![[59, 35, 40], [10, 50, 24], [28, 57, 48], [55, 2, 26], [44, 24, 57], [0, 0, 1], [0, 1]], ![[15, 31, 27], [33, 42, 64], [16, 53, 16], [45, 51, 15], [61, 33, 47], [26, 7, 31], [59, 35, 40]], ![[0, 1], [21, 42, 46], [8, 24, 3], [27, 14, 26], [14, 10, 30], [39, 60, 35], [15, 31, 27]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56, 29], []]
 b := ![[], [48, 63, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [32, 59, 60, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![160465, -18492, -7169]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2395, -276, -107]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0]] 
 ![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [42, 33, 52, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 7, 66], [15, 63, 5], [0, 1]]
 g := ![![[54, 46, 12], [7, 36, 15], [37, 56, 49], [64, 19], [19, 1], []], ![[38, 49, 59, 17], [46, 61, 22, 55], [54, 24, 51, 35], [38, 50], [68, 64], [50, 25]], ![[39, 33, 32, 12], [60, 34, 41, 4], [26, 24, 68, 60], [57, 43], [33, 49], [40, 25]]]
 h' := ![![[4, 7, 66], [61, 25, 56], [8, 60, 21], [15, 27, 64], [54, 41, 44], [0, 0, 1], [0, 1]], ![[15, 63, 5], [39, 4, 66], [7, 63, 29], [14, 24, 63], [41, 36, 11], [46, 54, 63], [4, 7, 66]], ![[0, 1], [38, 42, 20], [31, 19, 21], [26, 20, 15], [52, 65, 16], [36, 17, 7], [15, 63, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33, 21], []]
 b := ![[], [62, 0, 61], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [42, 33, 52, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3482053, 1500088, 167560]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![49043, 21128, 2360]
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


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [46, 1, 62, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 59, 59], [9, 13, 14], [0, 1]]
 g := ![![[19, 23, 1], [6, 18], [12, 19], [59, 34, 19], [11, 1], []], ![[65, 71, 15, 17], [35, 3], [29, 71], [70, 60, 12, 13], [61, 23], [66, 50]], ![[48, 55, 64, 53], [70, 38], [71, 57], [43, 27, 11, 5], [40, 50], [38, 50]]]
 h' := ![![[2, 59, 59], [48, 6, 1], [55, 1, 50], [60, 8, 47], [5, 16, 47], [0, 0, 1], [0, 1]], ![[9, 13, 14], [21, 49, 2], [5, 66, 52], [68, 7, 61], [29, 41, 22], [34, 60, 13], [2, 59, 59]], ![[0, 1], [41, 18, 70], [7, 6, 44], [39, 58, 38], [56, 16, 4], [12, 13, 59], [9, 13, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60, 41], []]
 b := ![[], [44, 14, 29], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [46, 1, 62, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8232648, -838186, 185858]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-112776, -11482, 2546]
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


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [76, 45, 19, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [71, 34, 54], [68, 44, 25], [0, 1]]
 g := ![![[50, 73, 50], [57, 52, 55], [28, 62, 8], [42], [60, 1], []], ![[48, 41, 42, 68], [3, 13, 30, 68], [30, 38, 55, 39], [48, 66, 54, 3], [29, 40], [13, 72]], ![[43, 28, 58, 1], [50, 23, 16, 31], [20, 40, 62, 62], [11, 16, 38, 76], [67, 50], [42, 72]]]
 h' := ![![[71, 34, 54], [13, 65, 34], [5, 29, 23], [47, 16, 61], [22, 68], [0, 0, 1], [0, 1]], ![[68, 44, 25], [72, 3, 29], [9, 53, 50], [40, 72, 72], [31, 21, 38], [24, 35, 44], [71, 34, 54]], ![[0, 1], [33, 11, 16], [74, 76, 6], [7, 70, 25], [64, 69, 41], [10, 44, 34], [68, 44, 25]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 59], []]
 b := ![[], [47, 8, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [76, 45, 19, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![36814, 112259, 23937]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![466, 1421, 303]
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



lemma PB87I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB87I1 : PrimesBelowBoundCertificateInterval O 31 79 87 where
  m := 11
  g := ![1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB87I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0]
    · exact ![I43N0, I43N0, I43N0]
    · exact ![I47N0]
    · exact ![I53N0]
    · exact ![I59N0]
    · exact ![I61N0]
    · exact ![I67N0]
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
    · exact ![50653]
    · exact ![68921]
    · exact ![43, 43, 43]
    · exact ![103823]
    · exact ![148877]
    · exact ![205379]
    · exact ![226981]
    · exact ![300763]
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
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N0
      exact NI43N0
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
    · dsimp ; intro j
      fin_cases j
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
  β := ![I43N0]
  Il := ![[], [], [I43N0, I43N0, I43N0], [], [], [], [], [], [], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
