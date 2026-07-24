
import IdealArithmetic.Examples.NF3_1_936684_4.RI3_1_936684_4
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-51, 12, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-51, 12, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![23, 12, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-51, 12, 1], ![350, 33, 12], ![4200, 1358, 33]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-23, -12, 37]], ![![-2, 0, 1], ![2, -3, 12], ![93, 26, 33]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [17, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 36], [0, 1]]
 g := ![![[29, 26], [1], [32, 33], [33], [1]], ![[13, 11], [1], [6, 4], [33], [1]]]
 h' := ![![[25, 36], [30, 10], [11, 1], [24, 12], [20, 25], [0, 1]], ![[0, 1], [21, 27], [36, 36], [28, 25], [16, 12], [25, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [31, 36]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [17, 12, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![717, 506, 73]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-26, -10, 73]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-12, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-12, 1, 0]] 
 ![![37, 0, 0], ![25, 1, 0], ![4, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-12, 1, 0], ![0, -12, 1], ![350, 84, -12]]]
  hmulB := by decide  
  f := ![![![433, -36, 0], ![1332, 0, 0]], ![![301, -25, 0], ![926, 0, 0]], ![![52, -4, 0], ![160, 1, 0]]]
  g := ![![![1, 0, 0], ![-25, 37, 0], ![-4, 0, 37]], ![![-1, 1, 0], ![8, -12, 1], ![-46, 84, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![-51, 12, 1]] ![![37, 0, 0], ![-12, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-444, 37, 0]], ![![-1887, 444, 37], ![962, -111, 0]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-12, 1, 0]]], ![![![-51, 12, 1]], ![![26, -3, 0]]]]
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


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [13, 34, 32, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 16, 30], [20, 24, 11], [0, 1]]
 g := ![![[4, 29, 1], [33, 9], [31, 33], [6, 9, 1], []], ![[9, 22, 12, 29], [17, 16], [], [36, 31, 14, 19], [40, 39]], ![[13, 31, 16, 17], [24, 1], [37, 33], [39, 22, 38, 28], [18, 39]]]
 h' := ![![[30, 16, 30], [18, 31, 40], [23, 8, 38], [4, 7, 22], [0, 0, 1], [0, 1]], ![[20, 24, 11], [35, 9, 4], [25, 20, 4], [5, 2], [11, 36, 24], [30, 16, 30]], ![[0, 1], [21, 1, 38], [13, 13, 40], [24, 32, 19], [2, 5, 16], [20, 24, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12, 15], []]
 b := ![[], [29, 31, 20], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [13, 34, 32, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1595310, 1280676, 196595]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![38910, 31236, 4795]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-59, 5, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-59, 5, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![27, 5, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-59, 5, 1], ![350, 25, 5], ![1750, 770, 25]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-27, -5, 43]], ![![-2, 0, 1], ![5, 0, 5], ![25, 15, 25]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [11, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 42], [0, 1]]
 g := ![![[29, 4], [28, 35], [13], [25, 23], [1]], ![[0, 39], [0, 8], [13], [41, 20], [1]]]
 h' := ![![[25, 42], [36, 2], [17, 32], [26, 20], [32, 25], [0, 1]], ![[0, 1], [0, 41], [0, 11], [10, 23], [12, 18], [25, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [7, 39]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [11, 18, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2255, 72, 195]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-70, -21, 195]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-5, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-5, 1, 0]] 
 ![![43, 0, 0], ![38, 1, 0], ![18, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-5, 1, 0], ![0, -5, 1], ![350, 84, -5]]]
  hmulB := by decide  
  f := ![![![151, -30, 0], ![1290, 0, 0]], ![![136, -27, 0], ![1162, 0, 0]], ![![66, -13, 0], ![564, 1, 0]]]
  g := ![![![1, 0, 0], ![-38, 43, 0], ![-18, 0, 43]], ![![-1, 1, 0], ![4, -5, 1], ![-64, 84, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-59, 5, 1]] ![![43, 0, 0], ![-5, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-215, 43, 0]], ![![-2537, 215, 43], ![645, 0, 0]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-5, 1, 0]]], ![![![-59, 5, 1]], ![![15, 0, 0]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-63, -16, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-63, -16, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![31, 31, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-63, -16, 1], ![350, 21, -16], ![-5600, -994, 21]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-31, -31, 47]], ![![-2, -1, 1], ![18, 11, -16], ![-133, -35, 21]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [31, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 46], [0, 1]]
 g := ![![[28, 32], [38, 32], [28, 16], [22, 14], [1]], ![[29, 15], [39, 15], [5, 31], [43, 33], [1]]]
 h' := ![![[25, 46], [44, 19], [25, 28], [23, 43], [16, 25], [0, 1]], ![[0, 1], [2, 28], [20, 19], [17, 4], [30, 22], [25, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [19, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [31, 22, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![731, 496, 63]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-26, -31, 63]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![16, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![16, 1, 0]] 
 ![![47, 0, 0], ![16, 1, 0], ![26, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![16, 1, 0], ![0, 16, 1], ![350, 84, 16]]]
  hmulB := by decide  
  f := ![![![17, 1, 0], ![-47, 0, 0]], ![![-16, -1, 0], ![48, 0, 0]], ![![6, 0, 0], ![-16, 1, 0]]]
  g := ![![![1, 0, 0], ![-16, 47, 0], ![-26, 0, 47]], ![![0, 1, 0], ![-6, 16, 1], ![-30, 84, 16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![-63, -16, 1]] ![![47, 0, 0], ![16, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![752, 47, 0]], ![![-2961, -752, 47], ![-658, -235, 0]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![16, 1, 0]]], ![![![-63, -16, 1]], ![![-14, -5, 0]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0]] 
 ![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [14, 51, 41, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 26, 19], [7, 26, 34], [0, 1]]
 g := ![![[11, 7, 37], [39, 40], [49, 36, 13], [27, 38], [1]], ![[25, 9, 37, 51], [25, 11], [2, 38, 34, 39], [26, 17], [12, 10, 14, 22]], ![[19, 10, 18, 31], [37, 6], [39, 11, 41, 33], [42, 28], [16, 43, 16, 31]]]
 h' := ![![[5, 26, 19], [46, 44, 39], [3, 17, 26], [30, 49, 15], [39, 2, 12], [0, 1]], ![[7, 26, 34], [20, 19, 48], [30, 10, 45], [1, 30, 49], [10, 32, 32], [5, 26, 19]], ![[0, 1], [12, 43, 19], [0, 26, 35], [5, 27, 42], [13, 19, 9], [7, 26, 34]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26, 28], []]
 b := ![[], [44, 30, 32], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [14, 51, 41, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4784257, 1574630, 137694]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![90269, 29710, 2598]
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


def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![17, 1, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![17, 1, 0]] 
 ![![59, 0, 0], ![17, 1, 0], ![6, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![17, 1, 0], ![0, 17, 1], ![350, 84, 17]]]
  hmulB := by decide  
  f := ![![![86, 5, 0], ![-295, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-12, -1, 0], ![42, 1, 0]]]
  g := ![![![1, 0, 0], ![-17, 59, 0], ![-6, 0, 59]], ![![0, 1, 0], ![-5, 17, 1], ![-20, 84, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N0 : Nat.card (O ⧸ I59N0) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N0)

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := prime_ideal_of_norm_prime hp59.out _ NI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![21, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![21, 1, 0]] 
 ![![59, 0, 0], ![21, 1, 0], ![31, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![21, 1, 0], ![0, 21, 1], ![350, 84, 21]]]
  hmulB := by decide  
  f := ![![![484, 23, 0], ![-1357, 0, 0]], ![![168, 8, 0], ![-471, 0, 0]], ![![218, 10, 0], ![-611, 1, 0]]]
  g := ![![![1, 0, 0], ![-21, 59, 0], ![-31, 0, 59]], ![![0, 1, 0], ![-8, 21, 1], ![-35, 84, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![17, 1, 0]] ![![59, 0, 0], ![21, 1, 0]]
  ![![59, 0, 0], ![-56, -21, 1]] where
 M := ![![![3481, 0, 0], ![1239, 59, 0]], ![![1003, 59, 0], ![357, 38, 1]]]
 hmul := by decide  
 g := ![![![![59, 0, 0], ![0, 0, 0]], ![![21, 1, 0], ![0, 0, 0]]], ![![![17, 1, 0], ![0, 0, 0]], ![![7, 1, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-56, -21, 1]] ![![59, 0, 0], ![21, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![1239, 59, 0]], ![![-3304, -1239, 59], ![-826, -413, 0]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![21, 1, 0]]], ![![![-56, -21, 1]], ![![-14, -7, 0]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1, I59N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
    exact isPrimeI59N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0 ⊙ MulI59N1)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-27, -22, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-27, -22, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![34, 39, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-27, -22, 1], ![350, 57, -22], ![-7700, -1498, 57]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-34, -39, 61]], ![![-1, -1, 1], ![18, 15, -22], ![-158, -61, 57]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [57, 47, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [14, 60], [0, 1]]
 g := ![![[34, 15], [12], [22, 16], [33, 45], [14, 1]], ![[0, 46], [12], [2, 45], [53, 16], [28, 60]]]
 h' := ![![[14, 60], [45, 36], [27, 45], [10, 57], [56, 17], [0, 1]], ![[0, 1], [0, 25], [47, 16], [15, 4], [50, 44], [14, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [11, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [57, 47, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2089, -19, 48]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-61, -31, 48]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![22, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![22, 1, 0]] 
 ![![61, 0, 0], ![22, 1, 0], ![4, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![22, 1, 0], ![0, 22, 1], ![350, 84, 22]]]
  hmulB := by decide  
  f := ![![![375, 17, 0], ![-1037, 0, 0]], ![![110, 5, 0], ![-304, 0, 0]], ![![8, 0, 0], ![-22, 1, 0]]]
  g := ![![![1, 0, 0], ![-22, 61, 0], ![-4, 0, 61]], ![![0, 1, 0], ![-8, 22, 1], ![-26, 84, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-27, -22, 1]] ![![61, 0, 0], ![22, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![1342, 61, 0]], ![![-1647, -1342, 61], ![-244, -427, 0]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![22, 1, 0]]], ![![![-27, -22, 1]], ![![-4, -7, 0]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-61, -31, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-61, -31, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![6, 36, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-61, -31, 1], ![350, 23, -31], ![-10850, -2254, 23]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-6, -36, 67]], ![![-1, -1, 1], ![8, 17, -31], ![-164, -46, 23]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [53, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [53, 66], [0, 1]]
 g := ![![[66, 26], [60, 14], [47], [35], [62], [1]], ![[37, 41], [65, 53], [47], [35], [62], [1]]]
 h' := ![![[53, 66], [36, 19], [44, 9], [18, 39], [59, 13], [14, 53], [0, 1]], ![[0, 1], [38, 48], [52, 58], [8, 28], [11, 54], [9, 14], [53, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [26, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [53, 14, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1453, 1750, 365]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-11, -170, 365]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![31, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![31, 1, 0]] 
 ![![67, 0, 0], ![31, 1, 0], ![44, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![31, 1, 0], ![0, 31, 1], ![350, 84, 31]]]
  hmulB := by decide  
  f := ![![![342, 11, 0], ![-737, 0, 0]], ![![124, 4, 0], ![-267, 0, 0]], ![![170, 5, 0], ![-366, 1, 0]]]
  g := ![![![1, 0, 0], ![-31, 67, 0], ![-44, 0, 67]], ![![0, 1, 0], ![-15, 31, 1], ![-54, 84, 31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![-61, -31, 1]] ![![67, 0, 0], ![31, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![2077, 67, 0]], ![![-4087, -2077, 67], ![-1541, -938, 0]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![31, 1, 0]]], ![![![-61, -31, 1]], ![![-23, -14, 0]]]]
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


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [26, 6, 13, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 8, 49], [36, 62, 22], [0, 1]]
 g := ![![[21, 15, 64], [35, 52, 45], [50, 67, 48], [1, 15], [58, 1], []], ![[63, 42, 69, 15], [65, 11, 53, 8], [7, 32, 15, 37], [47, 43], [62, 10], [30, 58]], ![[47, 59, 65, 53], [16, 56, 15, 34], [65, 33, 26, 11], [46, 20], [25, 64], [57, 58]]]
 h' := ![![[22, 8, 49], [13, 58, 63], [49, 32, 51], [50, 37, 41], [54, 52, 21], [0, 0, 1], [0, 1]], ![[36, 62, 22], [36, 5, 3], [70, 67, 44], [17, 48, 24], [23, 50, 16], [59, 13, 62], [22, 8, 49]], ![[0, 1], [39, 8, 5], [22, 43, 47], [4, 57, 6], [8, 40, 34], [27, 58, 8], [36, 62, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 70], []]
 b := ![[], [63, 19, 29], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [26, 6, 13, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3163902, -288260, 73272]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-44562, -4060, 1032]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-66, -23, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-66, -23, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![7, 50, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-66, -23, 1], ![350, 18, -23], ![-8050, -1582, 18]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-7, -50, 73]], ![![-1, -1, 1], ![7, 16, -23], ![-112, -34, 18]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [36, 66, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 72], [0, 1]]
 g := ![![[14, 71], [57], [46], [66, 6], [49], [1]], ![[0, 2], [57], [46], [35, 67], [49], [1]]]
 h' := ![![[7, 72], [62, 12], [17, 38], [33, 51], [43, 58], [37, 7], [0, 1]], ![[0, 1], [0, 61], [64, 35], [25, 22], [11, 15], [13, 66], [7, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40]]
 b := ![[], [3, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [36, 66, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![363, 90, 177]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-12, -120, 177]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![23, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![23, 1, 0]] 
 ![![73, 0, 0], ![23, 1, 0], ![55, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![23, 1, 0], ![0, 23, 1], ![350, 84, 23]]]
  hmulB := by decide  
  f := ![![![691, 30, 0], ![-2190, 0, 0]], ![![207, 9, 0], ![-656, 0, 0]], ![![537, 23, 0], ![-1702, 1, 0]]]
  g := ![![![1, 0, 0], ![-23, 73, 0], ![-55, 0, 73]], ![![0, 1, 0], ![-8, 23, 1], ![-39, 84, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-66, -23, 1]] ![![73, 0, 0], ![23, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![1679, 73, 0]], ![![-4818, -1679, 73], ![-1168, -511, 0]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![23, 1, 0]]], ![![![-66, -23, 1]], ![![-16, -7, 0]]]]
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


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [43, 73, 7, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [58, 33, 6], [14, 45, 73], [0, 1]]
 g := ![![[6, 41, 22], [23, 42, 22], [52, 47, 9], [5, 48, 23], [72, 1], []], ![[41, 28, 64, 14], [11, 58, 0, 37], [42, 68, 45, 68], [44, 60, 6, 47], [27, 50], [65, 36]], ![[52, 68, 43, 72], [11, 27, 12, 13], [50, 6, 74, 64], [54, 31, 54, 16], [69, 62], [77, 36]]]
 h' := ![![[58, 33, 6], [38, 14, 38], [55, 39, 41], [22, 8, 76], [64, 73, 55], [0, 0, 1], [0, 1]], ![[14, 45, 73], [36, 12, 56], [50, 78, 25], [43, 75, 71], [43, 28, 69], [16, 63, 45], [58, 33, 6]], ![[0, 1], [48, 53, 64], [76, 41, 13], [78, 75, 11], [6, 57, 34], [45, 16, 33], [14, 45, 73]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 34], []]
 b := ![[], [44, 23, 47], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [43, 73, 7, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-469576, -155788, -14378]
  a := ![1, -4, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5944, -1972, -182]
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



lemma PB274I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB274I1 : PrimesBelowBoundCertificateInterval O 31 79 274 where
  m := 11
  g := ![2, 1, 2, 2, 1, 3, 2, 2, 1, 2, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB274I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0]
    · exact ![I59N0, I59N1, I59N1]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1]
    · exact ![I71N0]
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
    · exact ![1369, 37]
    · exact ![68921]
    · exact ![1849, 43]
    · exact ![2209, 47]
    · exact ![148877]
    · exact ![59, 59, 59]
    · exact ![3721, 61]
    · exact ![4489, 67]
    · exact ![357911]
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
      exact NI47N1
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
  β := ![I37N1, I43N1, I47N1, I59N0, I59N1, I61N1, I67N1, I73N1]
  Il := ![[I37N1], [], [I43N1], [I47N1], [], [I59N0, I59N1, I59N1], [I61N1], [I67N1], [], [I73N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
