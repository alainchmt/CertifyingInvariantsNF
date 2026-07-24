
import IdealArithmetic.Examples.NF3_3_97825_1.RI3_3_97825_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-28, -5, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![-28, -5, 1]] 
 ![![37, 0, 0], ![21, 1, 0], ![3, 0, 1]] where
  M :=![![![-28, -5, 1], ![145, 27, -5], ![-725, -130, 27]]]
  hmulB := by decide  
  f := ![![![-79, -5, 2]], ![![-37, -2, 1]], ![![-26, 0, 1]]]
  g := ![![![2, -5, 1], ![-11, 27, -5], ![52, -130, 27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, -2, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-7, -2, 0]] 
 ![![37, 0, 0], ![22, 1, 0], ![34, 0, 1]] where
  M :=![![![-7, -2, 0], ![0, -7, -2], ![-290, -110, -7]]]
  hmulB := by decide  
  f := ![![![-171, -14, 4]], ![![-86, -7, 2]], ![![-212, -18, 5]]]
  g := ![![![1, -2, 0], ![6, -7, -2], ![64, -110, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-177, -13, 4]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![-177, -13, 4]] 
 ![![37, 0, 0], ![31, 1, 0], ![1, 0, 1]] where
  M :=![![![-177, -13, 4], ![580, 43, -13], ![-1885, -135, 43]]]
  hmulB := by decide  
  f := ![![![94, 19, -3]], ![![67, 14, -2]], ![![77, 17, -2]]]
  g := ![![![6, -13, 4], ![-20, 43, -13], ![61, -135, 43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![-28, -5, 1]] ![![-7, -2, 0]]
  ![![-94, -19, 3]] where
 M := ![![![-94, -19, 3]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![-94, -19, 3]] ![![-177, -13, 4]]
  ![![37, 0, 0]] where
 M := ![![![-37, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [34, 34, 28, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 33, 39], [16, 7, 2], [0, 1]]
 g := ![![[23], [21, 39], [24, 23], [12, 13, 1], []], ![[19, 3, 33, 21], [3, 5], [30, 8], [26, 30, 37, 25], [2, 4]], ![[27, 29, 19, 20], [17, 4], [28, 1], [37, 31, 31, 5], [39, 4]]]
 h' := ![![[38, 33, 39], [6, 33], [8, 4, 11], [2, 11, 8], [0, 0, 1], [0, 1]], ![[16, 7, 2], [30, 23, 16], [3, 15, 28], [30, 17, 34], [23, 8, 7], [38, 33, 39]], ![[0, 1], [1, 26, 25], [28, 22, 2], [23, 13, 40], [37, 33, 33], [16, 7, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 23], []]
 b := ![[], [17, 22, 32], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [34, 34, 28, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-36941, -18409, -2091]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-901, -449, -51]
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


def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 1, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![2, 1, 0]] 
 ![![43, 0, 0], ![2, 1, 0], ![39, 0, 1]] where
  M :=![![![2, 1, 0], ![0, 2, 1], ![145, 55, 2]]]
  hmulB := by decide  
  f := ![![![-51, -2, 1]], ![![1, 0, 0]], ![![-53, -1, 1]]]
  g := ![![![0, 1, 0], ![-1, 2, 1], ![-1, 55, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N0)

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := prime_ideal_of_norm_prime hp43.out _ NI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 3, -1]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![47, 3, -1]] 
 ![![43, 0, 0], ![39, 1, 0], ![27, 0, 1]] where
  M :=![![![47, 3, -1], ![-145, -8, 3], ![435, 20, -8]]]
  hmulB := by decide  
  f := ![![![4, 4, 1]], ![![7, 5, 1]], ![![16, 11, 2]]]
  g := ![![![-1, 3, -1], ![2, -8, 3], ![-3, 20, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![2, 1, 0]] ![![2, 1, 0]]
  ![![4, 4, 1]] where
 M := ![![![4, 4, 1]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI43N1 : IdealMulLeCertificate' Table 
  ![![4, 4, 1]] ![![47, 3, -1]]
  ![![43, 0, 0]] where
 M := ![![![43, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0]] 
 ![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [16, 6, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 5, 19], [23, 41, 28], [0, 1]]
 g := ![![[28, 34, 24], [25, 15, 14], [9], [45, 45, 1], []], ![[21, 19, 11, 33], [36, 46, 37, 30], [3, 42, 3, 20], [5, 9, 30, 26], [32, 32]], ![[20, 43, 42, 9], [35, 21, 17, 16], [2, 28, 26, 27], [28, 3, 20, 42], [23, 32]]]
 h' := ![![[22, 5, 19], [23, 42, 20], [44, 30, 25], [32, 44], [0, 0, 1], [0, 1]], ![[23, 41, 28], [11, 24, 20], [4, 35, 44], [13, 32, 37], [19, 33, 41], [22, 5, 19]], ![[0, 1], [26, 28, 7], [12, 29, 25], [10, 18, 10], [20, 14, 5], [23, 41, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38, 32], []]
 b := ![[], [13, 11, 28], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [16, 6, 2, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![137616, 271425, 75341]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2928, 5775, 1603]
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


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [20, 40, 37, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [28, 0, 49], [41, 52, 4], [0, 1]]
 g := ![![[41, 6, 36], [39, 7], [20, 48, 1], [7, 44], [1]], ![[24, 2, 33, 44], [26, 42], [22, 33, 30, 7], [35, 13], [23, 28, 36, 42]], ![[16, 46, 4, 28], [27, 9], [43, 19, 45, 7], [50, 1], [44, 37, 22, 11]]]
 h' := ![![[28, 0, 49], [8, 32, 6], [24, 14, 22], [48, 16, 1], [33, 13, 16], [0, 1]], ![[41, 52, 4], [10, 28, 25], [0, 32, 28], [29, 40, 41], [27, 4, 38], [28, 0, 49]], ![[0, 1], [37, 46, 22], [10, 7, 3], [22, 50, 11], [42, 36, 52], [41, 52, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38, 13], []]
 b := ![[], [24, 13, 43], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [20, 40, 37, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-65137, -5088, -19027]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1229, -96, -359]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-24, -4, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-24, -4, 1]] 
 ![![59, 0, 0], ![19, 1, 0], ![52, 0, 1]] where
  M :=![![![-24, -4, 1], ![145, 31, -4], ![-580, -75, 31]]]
  hmulB := by decide  
  f := ![![![-661, -49, 15]], ![![-176, -13, 4]], ![![-703, -52, 16]]]
  g := ![![![0, -4, 1], ![-4, 31, -4], ![-13, -75, 31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N0 : Nat.card (O ⧸ I59N0) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N0)

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := prime_ideal_of_norm_prime hp59.out _ NI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![161, 15, -4]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![161, 15, -4]] 
 ![![59, 0, 0], ![45, 1, 0], ![40, 0, 1]] where
  M :=![![![161, 15, -4], ![-580, -59, 15], ![2175, 245, -59]]]
  hmulB := by decide  
  f := ![![![194, 95, 11]], ![![175, 86, 10]], ![![365, 180, 21]]]
  g := ![![![-6, 15, -4], ![25, -59, 15], ![-110, 245, -59]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 10, -2]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![59, 10, -2]] 
 ![![59, 0, 0], ![54, 1, 0], ![34, 0, 1]] where
  M :=![![![59, 10, -2], ![-290, -51, 10], ![1450, 260, -51]]]
  hmulB := by decide  
  f := ![![![1, -10, -2]], ![![-4, -11, -2]], ![![-24, -20, -3]]]
  g := ![![![-7, 10, -2], ![36, -51, 10], ![-184, 260, -51]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-24, -4, 1]] ![![161, 15, -4]]
  ![![631, 121, -23]] where
 M := ![![![631, 121, -23]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![631, 121, -23]] ![![59, 10, -2]]
  ![![59, 0, 0]] where
 M := ![![![-31211, -5841, 1121]]]
 hmul := by decide  
 g := ![![![![-529, -99, 19]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 10, -3]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![131, 10, -3]] 
 ![![61, 0, 0], ![28, 1, 0], ![9, 0, 1]] where
  M :=![![![131, 10, -3], ![-435, -34, 10], ![1450, 115, -34]]]
  hmulB := by decide  
  f := ![![![6, -5, -2]], ![![-2, -4, -1]], ![![-11, -10, -2]]]
  g := ![![![-2, 10, -3], ![7, -34, 10], ![-24, 115, -34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N0 : Nat.card (O ⧸ I61N0) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N0)

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := prime_ideal_of_norm_prime hp61.out _ NI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-216, -17, 5]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![-216, -17, 5]] 
 ![![61, 0, 0], ![43, 1, 0], ![42, 0, 1]] where
  M :=![![![-216, -17, 5], ![725, 59, -17], ![-2465, -210, 59]]]
  hmulB := by decide  
  f := ![![![89, 47, 6]], ![![77, 40, 5]], ![![173, 89, 11]]]
  g := ![![![5, -17, 5], ![-18, 59, -17], ![67, -210, 59]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 15, -3]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![89, 15, -3]] 
 ![![61, 0, 0], ![51, 1, 0], ![22, 0, 1]] where
  M :=![![![89, 15, -3], ![-435, -76, 15], ![2175, 390, -76]]]
  hmulB := by decide  
  f := ![![![74, 30, 3]], ![![69, 29, 3]], ![![98, 45, 5]]]
  g := ![![![-10, 15, -3], ![51, -76, 15], ![-263, 390, -76]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![131, 10, -3]] ![![-216, -17, 5]]
  ![![-13651, -1007, 308]] where
 M := ![![![-13651, -1007, 308]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![-13651, -1007, 308]] ![![89, 15, -3]]
  ![![61, 0, 0]] where
 M := ![![![-106994, -8113, 2440]]]
 hmul := by decide  
 g := ![![![![-1754, -133, 40]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-64, 33, -3]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![-64, 33, -3]] 
 ![![67, 0, 0], ![0, 67, 0], ![66, 56, 1]] where
  M :=![![![-64, 33, -3], ![-435, -229, 33], ![4785, 1380, -229]]]
  hmulB := by decide  
  f := ![![![-103, -51, -6]], ![![-870, -433, -51]], ![![-939, -467, -55]]]
  g := ![![![2, 3, -3], ![-39, -31, 33], ![297, 212, -229]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [19, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [46, 66], [0, 1]]
 g := ![![[54, 60], [36, 40], [1], [39], [39], [1]], ![[0, 7], [0, 27], [1], [39], [39], [1]]]
 h' := ![![[46, 66], [53, 44], [35, 24], [11, 66], [22, 46], [48, 46], [0, 1]], ![[0, 1], [0, 23], [0, 43], [32, 1], [61, 21], [20, 21], [46, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49]]
 b := ![[], [6, 58]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [19, 21, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-829, 998, 427]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-433, -342, 427]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-103, -51, -6]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![-103, -51, -6]] 
 ![![67, 0, 0], ![11, 1, 0], ![13, 0, 1]] where
  M :=![![![-103, -51, -6], ![-870, -433, -51], ![-7395, -3675, -433]]]
  hmulB := by decide  
  f := ![![![-64, 33, -3]], ![![-17, 2, 0]], ![![59, 27, -4]]]
  g := ![![![8, -51, -6], ![68, -433, -51], ![577, -3675, -433]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![-64, 33, -3]] ![![-103, -51, -6]]
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


lemma PB70I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 69 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 69 (by omega)

def PB70I1 : PrimesBelowBoundCertificateInterval O 31 69 70 where
  m := 8
  g := ![3, 1, 3, 1, 1, 3, 3, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67]
  hP := PB70I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0]
    · exact ![I43N0, I43N0, I43N1]
    · exact ![I47N0]
    · exact ![I53N0]
    · exact ![I59N0, I59N1, I59N2]
    · exact ![I61N0, I61N1, I61N2]
    · exact ![I67N0, I67N1]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![37, 37, 37]
    · exact ![68921]
    · exact ![43, 43, 43]
    · exact ![103823]
    · exact ![148877]
    · exact ![59, 59, 59]
    · exact ![61, 61, 61]
    · exact ![4489, 67]
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
      exact NI59N2
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
      exact NI61N2
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
  β := ![I37N0, I37N1, I37N2, I43N0, I43N1, I59N0, I59N1, I59N2, I61N0, I61N1, I61N2, I67N1]
  Il := ![[I37N0, I37N1, I37N2], [], [I43N0, I43N0, I43N1], [], [], [I59N0, I59N1, I59N2], [I61N0, I61N1, I61N2], [I67N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
