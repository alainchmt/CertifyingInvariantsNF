
import IdealArithmetic.Examples.NF3_3_114433_1.RI3_3_114433_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-84, -83, 15]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![-84, -83, 15]] 
 ![![37, 0, 0], ![0, 37, 0], ![24, 29, 1]] where
  M :=![![![-84, -83, 15], ![255, 396, -68], ![-1156, -1921, 328]]]
  hmulB := by decide  
  f := ![![![20, 43, 8]], ![![136, 276, 51]], ![![143, 292, 54]]]
  g := ![![![-12, -14, 15], ![51, 64, -68], ![-244, -309, 328]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [15, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 36], [0, 1]]
 g := ![![[9, 3], [27], [31, 36], [21], [1]], ![[11, 34], [27], [18, 1], [21], [1]]]
 h' := ![![[13, 36], [36, 15], [16, 8], [21, 31], [22, 13], [0, 1]], ![[0, 1], [9, 22], [9, 29], [17, 6], [6, 24], [13, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [12, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [15, 24, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![66, 89, 12]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-6, -7, 12]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-20, -43, -8]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-20, -43, -8]] 
 ![![37, 0, 0], ![7, 1, 0], ![25, 0, 1]] where
  M :=![![![-20, -43, -8], ![-136, -276, -51], ![-867, -1768, -327]]]
  hmulB := by decide  
  f := ![![![84, 83, -15]], ![![9, 5, -1]], ![![88, 108, -19]]]
  g := ![![![13, -43, -8], ![83, -276, -51], ![532, -1768, -327]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![-84, -83, 15]] ![![-20, -43, -8]]
  ![![37, 0, 0]] where
 M := ![![![-37, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [35, 0, 15, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [26, 1, 33], [0, 39, 8], [0, 1]]
 g := ![![[18, 18, 8], [0, 31], [33, 8], [20, 26, 1], []], ![[10, 14, 29, 5], [24, 18], [9, 16], [27, 29, 4, 9], [8, 23]], ![[0, 14, 16, 32], [17, 18], [40, 39], [35, 22, 36, 8], [33, 23]]]
 h' := ![![[26, 1, 33], [4, 37, 34], [2, 14, 21], [38, 33, 34], [0, 0, 1], [0, 1]], ![[0, 39, 8], [39, 19, 5], [31, 27, 10], [10, 15, 37], [27, 26, 39], [26, 1, 33]], ![[0, 1], [12, 26, 2], [19, 0, 10], [5, 34, 11], [34, 15, 1], [0, 39, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14, 15], []]
 b := ![[], [8, 35, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [35, 0, 15, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7257, 30299, 31324]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![177, 739, 764]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 1, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![3, 1, 0]] 
 ![![43, 0, 0], ![3, 1, 0], ![34, 0, 1]] where
  M :=![![![3, 1, 0], ![0, 3, 1], ![17, 32, 4]]]
  hmulB := by decide  
  f := ![![![20, 4, -1]], ![![1, 0, 0]], ![![17, 5, -1]]]
  g := ![![![0, 1, 0], ![-1, 3, 1], ![-5, 32, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N0)

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := prime_ideal_of_norm_prime hp43.out _ NI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2, -5, -1]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-2, -5, -1]] 
 ![![43, 0, 0], ![12, 1, 0], ![28, 0, 1]] where
  M :=![![![-2, -5, -1], ![-17, -34, -6], ![-102, -209, -40]]]
  hmulB := by decide  
  f := ![![![106, 9, -4]], ![![28, 2, -1]], ![![71, 8, -3]]]
  g := ![![![2, -5, -1], ![13, -34, -6], ![82, -209, -40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1

def I43N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-41, 0, 1]] i)))

def SI43N2: IdealEqSpanCertificate' Table ![![-41, 0, 1]] 
 ![![43, 0, 0], ![27, 1, 0], ![2, 0, 1]] where
  M :=![![![-41, 0, 1], ![17, -9, 1], ![17, 49, -8]]]
  hmulB := by decide  
  f := ![![![23, 49, 9]], ![![18, 38, 7]], ![![24, 49, 9]]]
  g := ![![![-1, 0, 1], ![6, -9, 1], ![-30, 49, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N2 : Nat.card (O ⧸ I43N2) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N2)

lemma isPrimeI43N2 : Ideal.IsPrime I43N2 := prime_ideal_of_norm_prime hp43.out _ NI43N2
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![3, 1, 0]] ![![-2, -5, -1]]
  ![![-23, -49, -9]] where
 M := ![![![-23, -49, -9]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![-23, -49, -9]] ![![-41, 0, 1]]
  ![![43, 0, 0]] where
 M := ![![![-43, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1, I43N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
    exact isPrimeI43N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0 ⊙ MulI43N1)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![746, 37, -24]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![746, 37, -24]] 
 ![![47, 0, 0], ![0, 47, 0], ![12, 20, 1]] where
  M :=![![![746, 37, -24], ![-408, -22, 13], ![221, 8, -9]]]
  hmulB := by decide  
  f := ![![![2, 3, -1]], ![![-17, -30, 2]], ![![-6, -11, 0]]]
  g := ![![![22, 11, -24], ![-12, -6, 13], ![7, 4, -9]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [38, 7, 1] where
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
 g := ![![[41, 36], [16, 1], [30, 4], [1, 2], [1]], ![[24, 11], [9, 46], [2, 43], [34, 45], [1]]]
 h' := ![![[40, 46], [3, 41], [35, 1], [9, 45], [9, 40], [0, 1]], ![[0, 1], [45, 6], [28, 46], [23, 2], [11, 7], [40, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37]]
 b := ![[], [6, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [38, 7, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3669, -136, 153]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![39, -68, 153]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 3, -1]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![2, 3, -1]] 
 ![![47, 0, 0], ![26, 1, 0], ![29, 0, 1]] where
  M :=![![![2, 3, -1], ![-17, -30, 2], ![34, 47, -28]]]
  hmulB := by decide  
  f := ![![![746, 37, -24]], ![![404, 20, -13]], ![![465, 23, -15]]]
  g := ![![![-1, 3, -1], ![15, -30, 2], ![-8, 47, -28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![746, 37, -24]] ![![2, 3, -1]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![91, 5, -3]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![91, 5, -3]] 
 ![![53, 0, 0], ![26, 1, 0], ![13, 0, 1]] where
  M :=![![![91, 5, -3], ![-51, -5, 2], ![34, 13, -3]]]
  hmulB := by decide  
  f := ![![![-11, -24, -5]], ![![-7, -15, -3]], ![![-12, -25, -5]]]
  g := ![![![0, 5, -3], ![1, -5, 2], ![-5, 13, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N0 : Nat.card (O ⧸ I53N0) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N0)

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := prime_ideal_of_norm_prime hp53.out _ NI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-22, -3, 1]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-22, -3, 1]] 
 ![![53, 0, 0], ![33, 1, 0], ![24, 0, 1]] where
  M :=![![![-22, -3, 1], ![17, 10, -2], ![-34, -47, 8]]]
  hmulB := by decide  
  f := ![![![-14, -23, -4]], ![![-10, -17, -3]], ![![-15, -28, -5]]]
  g := ![![![1, -3, 1], ![-5, 10, -2], ![25, -47, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1

def I53N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, 1, 0]] i)))

def SI53N2: IdealEqSpanCertificate' Table ![![-7, 1, 0]] 
 ![![53, 0, 0], ![46, 1, 0], ![4, 0, 1]] where
  M :=![![![-7, 1, 0], ![0, -7, 1], ![17, 32, -6]]]
  hmulB := by decide  
  f := ![![![-10, -6, -1]], ![![-9, -6, -1]], ![![-3, -5, -1]]]
  g := ![![![-1, 1, 0], ![6, -7, 1], ![-27, 32, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N2 : Nat.card (O ⧸ I53N2) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N2)

lemma isPrimeI53N2 : Ideal.IsPrime I53N2 := prime_ideal_of_norm_prime hp53.out _ NI53N2
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![91, 5, -3]] ![![-22, -3, 1]]
  ![![-1815, -82, 57]] where
 M := ![![![-1815, -82, 57]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI53N1 : IdealMulLeCertificate' Table 
  ![![-1815, -82, 57]] ![![-7, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![13674, 583, -424]]]
 hmul := by decide  
 g := ![![![![258, 11, -8]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-15, -22, -4]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-15, -22, -4]] 
 ![![59, 0, 0], ![0, 59, 0], ![48, 35, 1]] where
  M :=![![![-15, -22, -4], ![-68, -143, -26], ![-442, -900, -169]]]
  hmulB := by decide  
  f := ![![![-13, 2, 0]], ![![0, -13, 2]], ![![-10, -5, 1]]]
  g := ![![![3, 2, -4], ![20, 13, -26], ![130, 85, -169]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [42, 57, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 58], [0, 1]]
 g := ![![[14, 16], [1, 19], [4], [9, 28], [2, 1]], ![[46, 43], [39, 40], [4], [6, 31], [4, 58]]]
 h' := ![![[2, 58], [17, 55], [54, 45], [35, 57], [34, 21], [0, 1]], ![[0, 1], [9, 4], [26, 14], [31, 2], [17, 38], [2, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36]]
 b := ![[], [41, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [42, 57, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![151, 308, 115]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-91, -63, 115]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13, 2, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![-13, 2, 0]] 
 ![![59, 0, 0], ![23, 1, 0], ![2, 0, 1]] where
  M :=![![![-13, 2, 0], ![0, -13, 2], ![34, 64, -11]]]
  hmulB := by decide  
  f := ![![![-15, -22, -4]], ![![-7, -11, -2]], ![![-8, -16, -3]]]
  g := ![![![-1, 2, 0], ![5, -13, 2], ![-24, 64, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-15, -22, -4]] ![![-13, 2, 0]]
  ![![59, 0, 0]] where
 M := ![![![59, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0]] 
 ![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [23, 21, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [32, 9, 32], [24, 51, 29], [0, 1]]
 g := ![![[49, 27, 19], [16, 13], [18, 16, 1], [26, 24, 25], [1]], ![[55, 19, 37, 44], [28, 46], [4, 3, 48, 21], [13, 9, 4, 33], [32, 31, 21, 11]], ![[20, 18, 14, 40], [53, 12], [13, 52, 12, 6], [36, 49, 42, 24], [1, 36, 18, 50]]]
 h' := ![![[32, 9, 32], [45, 0, 18], [13, 8, 47], [12, 41, 1], [38, 40, 56], [0, 1]], ![[24, 51, 29], [31, 6, 3], [2, 47, 30], [49, 44, 21], [7, 33, 49], [32, 9, 32]], ![[0, 1], [58, 55, 40], [39, 6, 45], [58, 37, 39], [15, 49, 17], [24, 51, 29]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23, 33], []]
 b := ![[], [14, 53, 39], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [23, 21, 5, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2867, -6039, -1342]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-47, -99, -22]
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


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [62, 25, 47, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 25, 57], [63, 41, 10], [0, 1]]
 g := ![![[45, 50, 26], [61, 2, 10], [20, 10], [38, 59], [20, 1], []], ![[14, 10, 41, 46], [44, 55, 38, 18], [4, 23], [55, 40], [58, 6], [26, 33]], ![[61, 23, 45, 60], [0, 31, 22, 9], [52, 40], [2, 9], [66, 22], [6, 33]]]
 h' := ![![[24, 25, 57], [37, 30, 48], [2, 42, 12], [6, 41, 55], [33, 41, 40], [0, 0, 1], [0, 1]], ![[63, 41, 10], [6, 29, 60], [35, 49, 5], [22, 16, 36], [45, 11, 24], [36, 45, 41], [24, 25, 57]], ![[0, 1], [48, 8, 26], [51, 43, 50], [27, 10, 43], [34, 15, 3], [46, 22, 25], [63, 41, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44, 34], []]
 b := ![[], [12, 33, 57], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [62, 25, 47, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![201670, 402469, 70149]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3010, 6007, 1047]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![39, 45, -8]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![39, 45, -8]] 
 ![![71, 0, 0], ![0, 71, 0], ![4, 21, 1]] where
  M :=![![![39, 45, -8], ![-136, -217, 37], ![629, 1048, -180]]]
  hmulB := by decide  
  f := ![![![4, -4, -1]], ![![-17, -28, -5]], ![![-6, -11, -2]]]
  g := ![![![1, 3, -8], ![-4, -14, 37], ![19, 68, -180]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [20, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [70, 70], [0, 1]]
 g := ![![[32, 32], [45, 45], [70, 9], [30], [1], [1]], ![[0, 39], [0, 26], [61, 62], [30], [1], [1]]]
 h' := ![![[70, 70], [23, 23], [20, 20], [25, 3], [25, 39], [51, 70], [0, 1]], ![[0, 1], [0, 48], [0, 51], [22, 68], [57, 32], [52, 1], [70, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36]]
 b := ![[], [9, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [20, 1, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-65, -146, 37]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3, -13, 37]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4, -4, -1]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![4, -4, -1]] 
 ![![71, 0, 0], ![49, 1, 0], ![13, 0, 1]] where
  M :=![![![4, -4, -1], ![-17, -28, -5], ![-85, -177, -33]]]
  hmulB := by decide  
  f := ![![![39, 45, -8]], ![![25, 28, -5]], ![![16, 23, -4]]]
  g := ![![![3, -4, -1], ![20, -28, -5], ![127, -177, -33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![39, 45, -8]] ![![4, -4, -1]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-103, -201, -37]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![-103, -201, -37]] 
 ![![73, 0, 0], ![0, 73, 0], ![60, 37, 1]] where
  M :=![![![-103, -201, -37], ![-629, -1287, -238], ![-4046, -8245, -1525]]]
  hmulB := by decide  
  f := ![![![-5, 20, -3]], ![![-51, -101, 17]], ![![-26, -28, 5]]]
  g := ![![![29, 16, -37], ![187, 103, -238], ![1198, 660, -1525]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [22, 48, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 72], [0, 1]]
 g := ![![[42, 27], [32], [8], [20, 4], [41], [1]], ![[60, 46], [32], [8], [47, 69], [41], [1]]]
 h' := ![![[25, 72], [45, 10], [47, 18], [71, 9], [20, 71], [51, 25], [0, 1]], ![[0, 1], [3, 63], [59, 55], [4, 64], [43, 2], [19, 48], [25, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56]]
 b := ![[], [15, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [22, 48, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-490, -1604, 296]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-250, -172, 296]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, -20, 3]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![5, -20, 3]] 
 ![![73, 0, 0], ![35, 1, 0], ![16, 0, 1]] where
  M :=![![![5, -20, 3], ![51, 101, -17], ![-289, -493, 84]]]
  hmulB := by decide  
  f := ![![![103, 201, 37]], ![![58, 114, 21]], ![![78, 157, 29]]]
  g := ![![![9, -20, 3], ![-44, 101, -17], ![214, -493, 84]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![-103, -201, -37]] ![![5, -20, 3]]
  ![![73, 0, 0]] where
 M := ![![![-73, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


lemma PB76I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 75 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 75 (by omega)

def PB76I1 : PrimesBelowBoundCertificateInterval O 31 75 76 where
  m := 10
  g := ![2, 1, 3, 2, 3, 2, 1, 1, 2, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73]
  hP := PB76I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0]
    · exact ![I43N0, I43N1, I43N2]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1, I53N2]
    · exact ![I59N0, I59N1]
    · exact ![I61N0]
    · exact ![I67N0]
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
    · exact ![1369, 37]
    · exact ![68921]
    · exact ![43, 43, 43]
    · exact ![2209, 47]
    · exact ![53, 53, 53]
    · exact ![3481, 59]
    · exact ![226981]
    · exact ![300763]
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
      exact NI37N1
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
      exact NI43N2
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
  β := ![I37N1, I43N0, I43N1, I43N2, I47N1, I53N0, I53N1, I53N2, I59N1, I71N1, I73N1]
  Il := ![[I37N1], [], [I43N0, I43N1, I43N2], [I47N1], [I53N0, I53N1, I53N2], [I59N1], [], [], [I71N1], [I73N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
