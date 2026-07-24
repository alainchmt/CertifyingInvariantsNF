
import IdealArithmetic.Examples.NF3_1_933907_1.RI3_1_933907_1
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [13, 20, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 4, 20], [34, 32, 17], [0, 1]]
 g := ![![[34, 18, 3], [11, 27], [29, 2, 28], [36, 1], []], ![[30, 28, 34, 13], [25, 10], [11, 32, 30, 13], [4, 25], [19, 30]], ![[5, 13, 24, 8], [9, 9], [13, 13, 1, 20], [22, 16], [22, 30]]]
 h' := ![![[2, 4, 20], [17, 34, 15], [30, 7, 8], [13, 7, 18], [0, 0, 1], [0, 1]], ![[34, 32, 17], [29, 0, 13], [24, 27, 26], [19, 35, 13], [16, 23, 32], [2, 4, 20]], ![[0, 1], [15, 3, 9], [13, 3, 3], [1, 32, 6], [19, 14, 4], [34, 32, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 18], []]
 b := ![[], [4, 19, 25], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [13, 20, 1, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4095715, 1661707, -346505]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-110695, 44911, -9365]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-20, 1, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-20, 1, 0]] 
 ![![41, 0, 0], ![21, 1, 0], ![15, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-20, 1, 0], ![0, -19, 2], ![-754, 117, -20]]]
  hmulB := by decide  
  f := ![![![21, 493, -52], ![41, 1066, 0]], ![![21, 246, -26], ![42, 533, 0]], ![![15, 180, -19], ![30, 390, 0]]]
  g := ![![![1, 0, 0], ![-21, 41, 0], ![-15, 0, 41]], ![![-1, 1, 0], ![9, -19, 2], ![-71, 117, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N0)

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := prime_ideal_of_norm_prime hp41.out _ NI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-15, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-15, 1, 0]] 
 ![![41, 0, 0], ![26, 1, 0], ![18, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-15, 1, 0], ![0, -14, 2], ![-754, 117, -15]]]
  hmulB := by decide  
  f := ![![![196, -13, 0], ![533, 0, 0]], ![![136, -9, 0], ![370, 0, 0]], ![![108, 0, -1], ![294, 21, 0]]]
  g := ![![![1, 0, 0], ![-26, 41, 0], ![-18, 0, 41]], ![![-1, 1, 0], ![8, -14, 2], ![-86, 117, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-7, 1, 0]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-7, 1, 0]] 
 ![![41, 0, 0], ![34, 1, 0], ![20, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-7, 1, 0], ![0, -6, 2], ![-754, 117, -7]]]
  hmulB := by decide  
  f := ![![![57, -8, 0], ![328, 0, 0]], ![![50, -7, 0], ![288, 0, 0]], ![![36, -2, -1], ![208, 21, 0]]]
  g := ![![![1, 0, 0], ![-34, 41, 0], ![-20, 0, 41]], ![![-1, 1, 0], ![4, -6, 2], ![-112, 117, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-20, 1, 0]] ![![41, 0, 0], ![-15, 1, 0]]
  ![![41, 0, 0], ![-96, 24, 1]] where
 M := ![![![1681, 0, 0], ![-615, 41, 0]], ![![-820, 41, 0], ![300, -34, 2]]]
 hmul := by decide  
 g := ![![![![41, 0, 0], ![0, 0, 0]], ![![81, -23, -1], ![41, 0, 0]]], ![![![76, -23, -1], ![41, 0, 0]], ![![12, -2, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-96, 24, 1]] ![![41, 0, 0], ![-7, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-287, 41, 0]], ![![-3936, 984, 41], ![-82, -123, 41]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-7, 1, 0]]], ![![![-96, 24, 1]], ![![-2, -3, 1]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1, I41N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
    exact isPrimeI41N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0 ⊙ MulI41N1)
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


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [4, 28, 12, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 10, 26], [41, 32, 17], [0, 1]]
 g := ![![[24, 39, 38], [41, 27, 11], [28, 10], [30, 31, 1], []], ![[34, 13, 32, 22], [21, 20, 15, 28], [36, 15], [3, 23, 42, 7], [19, 31]], ![[23, 12, 42, 6], [3, 19, 22, 17], [11, 41], [12, 32, 16, 23], [28, 31]]]
 h' := ![![[33, 10, 26], [8, 6, 9], [12, 13, 21], [9, 25, 15], [0, 0, 1], [0, 1]], ![[41, 32, 17], [35, 10, 14], [42, 42, 21], [33, 9, 12], [24, 4, 32], [33, 10, 26]], ![[0, 1], [13, 27, 20], [40, 31, 1], [16, 9, 16], [21, 39, 10], [41, 32, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 7], []]
 b := ![[], [0, 25, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [4, 28, 12, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![16779503, -5042137, 883736]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![390221, -117259, 20552]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-86, -6, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-86, -6, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![8, 41, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-86, -6, 1], ![-754, 25, -12], ![4901, -1079, 31]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-8, -41, 47]], ![![-2, -1, 1], ![-14, 11, -12], ![99, -50, 31]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [43, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [45, 46], [0, 1]]
 g := ![![[23, 7], [2, 9], [40, 8], [23, 4], [1]], ![[9, 40], [31, 38], [24, 39], [15, 43], [1]]]
 h' := ![![[45, 46], [8, 17], [19, 3], [45, 33], [4, 45], [0, 1]], ![[0, 1], [21, 30], [13, 44], [26, 14], [8, 2], [45, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [14, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [43, 2, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4388, -377, 243]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![52, -220, 243]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![12, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![12, 1, 0]] 
 ![![47, 0, 0], ![12, 1, 0], ![16, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![12, 1, 0], ![0, 13, 2], ![-754, 117, 12]]]
  hmulB := by decide  
  f := ![![![25, 2, 0], ![-94, 0, 0]], ![![-12, -1, 0], ![48, 0, 0]], ![![8, -6, -1], ![-30, 24, 0]]]
  g := ![![![1, 0, 0], ![-12, 47, 0], ![-16, 0, 47]], ![![0, 1, 0], ![-4, 13, 2], ![-50, 117, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![-86, -6, 1]] ![![47, 0, 0], ![12, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![564, 47, 0]], ![![-4042, -282, 47], ![-1786, -47, 0]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![12, 1, 0]]], ![![![-86, -6, 1]], ![![-38, -1, 0]]]]
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


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [5, 15, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [13, 33, 20], [37, 19, 33], [0, 1]]
 g := ![![[8, 21, 1], [50, 24], [43, 36, 44], [10, 9], [1]], ![[4, 51, 38, 31], [7, 52], [11, 13, 33, 48], [10, 37], [30, 0, 18, 50]], ![[35, 9, 0, 30], [14, 36], [4, 36, 43, 33], [4, 15], [37, 8, 1, 3]]]
 h' := ![![[13, 33, 20], [24, 12, 1], [50, 12, 36], [28, 8, 37], [48, 38, 50], [0, 1]], ![[37, 19, 33], [14, 51, 47], [7, 7, 23], [32, 7, 15], [33, 10, 14], [13, 33, 20]], ![[0, 1], [30, 43, 5], [43, 34, 47], [18, 38, 1], [12, 5, 42], [37, 19, 33]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33, 39], []]
 b := ![[], [20, 20, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [5, 15, 3, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-27835017, 8967706, -1641728]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-525189, 169202, -30976]
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


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [52, 42, 55, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [58, 15, 19], [5, 43, 40], [0, 1]]
 g := ![![[42, 53, 48], [15, 6, 53], [31, 12], [1, 23, 16], [1]], ![[43, 39, 5, 29], [9, 30, 24, 22], [24, 16], [38, 48, 46, 21], [6, 45, 21, 15]], ![[6, 17, 9, 11], [12, 22, 11, 10], [30, 29], [24, 34, 31, 14], [25, 17, 17, 44]]]
 h' := ![![[58, 15, 19], [46, 17, 15], [30, 13, 42], [7, 50, 37], [7, 17, 4], [0, 1]], ![[5, 43, 40], [58, 43, 24], [51, 38, 47], [1, 54, 4], [41, 49, 23], [58, 15, 19]], ![[0, 1], [26, 58, 20], [37, 8, 29], [57, 14, 18], [5, 52, 32], [5, 43, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 47], []]
 b := ![[], [23, 26, 41], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [52, 42, 55, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4401046, 1554473, -289277]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-74594, 26347, -4903]
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


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [46, 37, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [10, 41, 23], [47, 19, 38], [0, 1]]
 g := ![![[21, 0, 49], [56, 56], [11, 57, 47], [34, 49, 16], [1]], ![[45, 1, 0, 37], [45, 34], [51, 59, 59, 40], [21, 43, 37, 18], [10, 18, 51, 28]], ![[57, 29, 15, 7], [51, 57], [12, 41, 21, 33], [32, 9, 25, 29], [36, 50, 9, 33]]]
 h' := ![![[10, 41, 23], [5, 47, 54], [43, 17, 19], [22, 7, 48], [15, 24, 57], [0, 1]], ![[47, 19, 38], [13, 22, 33], [3, 3, 20], [27, 17, 36], [52, 0, 49], [10, 41, 23]], ![[0, 1], [32, 53, 35], [11, 41, 22], [11, 37, 38], [53, 37, 16], [47, 19, 38]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50], []]
 b := ![[], [8, 27], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [46, 37, 4, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![691424874, -469420437, 116594973]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![11334834, -7695417, 1911393]
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


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [55, 49, 35, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [47, 6, 53], [52, 60, 14], [0, 1]]
 g := ![![[43, 24, 14], [22], [9, 60], [19, 29], [32, 1], []], ![[7, 13, 48, 13], [24, 1, 65, 66], [3, 47], [11, 56], [51, 49], [7, 62]], ![[61, 44, 46, 9], [42, 46, 64, 1], [12, 25], [36, 10], [24, 36], [46, 62]]]
 h' := ![![[47, 6, 53], [63, 31, 58], [29, 42], [16, 24, 23], [49, 52, 37], [0, 0, 1], [0, 1]], ![[52, 60, 14], [45, 10, 31], [60, 51, 15], [15, 28, 39], [33, 38, 18], [15, 27, 60], [47, 6, 53]], ![[0, 1], [42, 26, 45], [2, 41, 52], [40, 15, 5], [12, 44, 12], [40, 40, 6], [52, 60, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [63, 17], []]
 b := ![[], [66, 30, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [55, 49, 35, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-297413, -8844, 16348]
  a := ![-1, 2, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4439, -132, 244]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![17, 1, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![17, 1, 0]] 
 ![![71, 0, 0], ![17, 1, 0], ![60, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![17, 1, 0], ![0, 18, 2], ![-754, 117, 17]]]
  hmulB := by decide  
  f := ![![![749, 44, 0], ![-3124, 0, 0]], ![![153, 9, 0], ![-638, 0, 0]], ![![632, 28, -1], ![-2636, 36, 0]]]
  g := ![![![1, 0, 0], ![-17, 71, 0], ![-60, 0, 71]], ![![0, 1, 0], ![-6, 18, 2], ![-53, 117, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N0 : Nat.card (O ⧸ I71N0) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N0)

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := prime_ideal_of_norm_prime hp71.out _ NI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-12, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-12, 1, 0]] 
 ![![71, 0, 0], ![59, 1, 0], ![5, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-12, 1, 0], ![0, -11, 2], ![-754, 117, -12]]]
  hmulB := by decide  
  f := ![![![121, -10, 0], ![710, 0, 0]], ![![109, -9, 0], ![640, 0, 0]], ![![19, 4, -1], ![112, 36, 0]]]
  g := ![![![1, 0, 0], ![-59, 71, 0], ![-5, 0, 71]], ![![-1, 1, 0], ![9, -11, 2], ![-107, 117, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-6, 1, 0]] i)))

def SI71N2: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-6, 1, 0]] 
 ![![71, 0, 0], ![65, 1, 0], ![56, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-6, 1, 0], ![0, -5, 2], ![-754, 117, -6]]]
  hmulB := by decide  
  f := ![![![121, -20, 0], ![1420, 0, 0]], ![![115, -19, 0], ![1350, 0, 0]], ![![100, -14, -1], ![1174, 36, 0]]]
  g := ![![![1, 0, 0], ![-65, 71, 0], ![-56, 0, 71]], ![![-1, 1, 0], ![3, -5, 2], ![-113, 117, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![17, 1, 0]] ![![71, 0, 0], ![-12, 1, 0]]
  ![![71, 0, 0], ![-102, 3, 1]] where
 M := ![![![5041, 0, 0], ![-852, 71, 0]], ![![1207, 71, 0], ![-204, 6, 2]]]
 hmul := by decide  
 g := ![![![![71, 0, 0], ![0, 0, 0]], ![![90, -2, -1], ![71, 0, 0]]], ![![![17, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![-102, 3, 1]] ![![71, 0, 0], ![-6, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-426, 71, 0]], ![![-7242, 213, 71], ![-142, 0, 0]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-6, 1, 0]]], ![![![-102, 3, 1]], ![![-2, 0, 0]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![29, 1, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![29, 1, 0]] 
 ![![73, 0, 0], ![29, 1, 0], ![3, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![29, 1, 0], ![0, 30, 2], ![-754, 117, 29]]]
  hmulB := by decide  
  f := ![![![871, 30, 0], ![-2190, 0, 0]], ![![319, 11, 0], ![-802, 0, 0]], ![![35, -14, -1], ![-88, 37, 0]]]
  g := ![![![1, 0, 0], ![-29, 73, 0], ![-3, 0, 73]], ![![0, 1, 0], ![-12, 30, 2], ![-58, 117, 29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N0 : Nat.card (O ⧸ I73N0) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N0)

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := prime_ideal_of_norm_prime hp73.out _ NI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-25, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-25, 1, 0]] 
 ![![73, 0, 0], ![48, 1, 0], ![65, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-25, 1, 0], ![0, -24, 2], ![-754, 117, -25]]]
  hmulB := by decide  
  f := ![![![1451, -58, 0], ![4234, 0, 0]], ![![976, -39, 0], ![2848, 0, 0]], ![![1305, -40, -1], ![3808, 37, 0]]]
  g := ![![![1, 0, 0], ![-48, 73, 0], ![-65, 0, 73]], ![![-1, 1, 0], ![14, -24, 2], ![-65, 117, -25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1

def I73N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-5, 1, 0]] i)))

def SI73N2: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-5, 1, 0]] 
 ![![73, 0, 0], ![68, 1, 0], ![63, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-5, 1, 0], ![0, -4, 2], ![-754, 117, -5]]]
  hmulB := by decide  
  f := ![![![241, -48, 0], ![3504, 0, 0]], ![![226, -45, 0], ![3286, 0, 0]], ![![201, -38, -1], ![2922, 37, 0]]]
  g := ![![![1, 0, 0], ![-68, 73, 0], ![-63, 0, 73]], ![![-1, 1, 0], ![2, -4, 2], ![-115, 117, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N2 : Nat.card (O ⧸ I73N2) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N2)

lemma isPrimeI73N2 : Ideal.IsPrime I73N2 := prime_ideal_of_norm_prime hp73.out _ NI73N2
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![29, 1, 0]] ![![73, 0, 0], ![-25, 1, 0]]
  ![![73, 0, 0], ![-107, 39, 1]] where
 M := ![![![5329, 0, 0], ![-1825, 73, 0]], ![![2117, 73, 0], ![-725, 5, 2]]]
 hmul := by decide  
 g := ![![![![73, 0, 0], ![0, 0, 0]], ![![82, -38, -1], ![73, 0, 0]]], ![![![29, 1, 0], ![0, 0, 0]], ![![100, -40, -1], ![75, 0, 0]]]]
 hle2 := by decide  

def MulI73N1 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-107, 39, 1]] ![![73, 0, 0], ![-5, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-365, 73, 0]], ![![-7811, 2847, 73], ![-219, -146, 73]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-5, 1, 0]]], ![![![-107, 39, 1]], ![![-3, -2, 1]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![5, 1, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![5, 1, 0]] 
 ![![79, 0, 0], ![5, 1, 0], ![64, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![5, 1, 0], ![0, 6, 2], ![-754, 117, 5]]]
  hmulB := by decide  
  f := ![![![61, 12, 0], ![-948, 0, 0]], ![![-5, -1, 0], ![80, 0, 0]], ![![56, 8, -1], ![-872, 40, 0]]]
  g := ![![![1, 0, 0], ![-5, 79, 0], ![-64, 0, 79]], ![![0, 1, 0], ![-2, 6, 2], ![-21, 117, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N0 : Nat.card (O ⧸ I79N0) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N0)

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := prime_ideal_of_norm_prime hp79.out _ NI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![20, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![20, 1, 0]] 
 ![![79, 0, 0], ![20, 1, 0], ![27, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![20, 1, 0], ![0, 21, 2], ![-754, 117, 20]]]
  hmulB := by decide  
  f := ![![![41, 2, 0], ![-158, 0, 0]], ![![-20, -1, 0], ![80, 0, 0]], ![![13, -10, -1], ![-50, 40, 0]]]
  g := ![![![1, 0, 0], ![-20, 79, 0], ![-27, 0, 79]], ![![0, 1, 0], ![-6, 21, 2], ![-46, 117, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1

def I79N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-26, 1, 0]] i)))

def SI79N2: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-26, 1, 0]] 
 ![![79, 0, 0], ![53, 1, 0], ![70, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-26, 1, 0], ![0, -25, 2], ![-754, 117, -26]]]
  hmulB := by decide  
  f := ![![![27, 1424, -114], ![79, 4503, 0]], ![![27, 949, -76], ![80, 3002, 0]], ![![18, 1262, -101], ![52, 3990, 0]]]
  g := ![![![1, 0, 0], ![-53, 79, 0], ![-70, 0, 79]], ![![-1, 1, 0], ![15, -25, 2], ![-65, 117, -26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N2 : Nat.card (O ⧸ I79N2) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N2)

lemma isPrimeI79N2 : Ideal.IsPrime I79N2 := prime_ideal_of_norm_prime hp79.out _ NI79N2
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![5, 1, 0]] ![![79, 0, 0], ![20, 1, 0]]
  ![![79, 0, 0], ![-108, 13, 1]] where
 M := ![![![6241, 0, 0], ![1580, 79, 0]], ![![395, 79, 0], ![100, 26, 2]]]
 hmul := by decide  
 g := ![![![![79, 0, 0], ![0, 0, 0]], ![![20, 1, 0], ![0, 0, 0]]], ![![![5, 1, 0], ![0, 0, 0]], ![![4, 0, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI79N1 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-108, 13, 1]] ![![79, 0, 0], ![-26, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![-2054, 79, 0]], ![![-8532, 1027, 79], ![2054, -316, 0]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![-26, 1, 0]]], ![![![-108, 13, 1]], ![![26, -4, 0]]]]
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


lemma PB274I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB274I1 : PrimesBelowBoundCertificateInterval O 31 79 274 where
  m := 11
  g := ![1, 3, 1, 2, 1, 1, 1, 1, 3, 3, 3]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB274I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0]
    · exact ![I47N0, I47N1]
    · exact ![I53N0]
    · exact ![I59N0]
    · exact ![I61N0]
    · exact ![I67N0]
    · exact ![I71N0, I71N1, I71N2]
    · exact ![I73N0, I73N1, I73N2]
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
    · exact ![41, 41, 41]
    · exact ![79507]
    · exact ![2209, 47]
    · exact ![148877]
    · exact ![205379]
    · exact ![226981]
    · exact ![300763]
    · exact ![71, 71, 71]
    · exact ![73, 73, 73]
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
      exact NI41N2
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
      exact NI79N2
  β := ![I41N0, I41N1, I41N2, I47N1, I71N0, I71N1, I71N2, I73N0, I73N1, I73N2, I79N0, I79N1, I79N2]
  Il := ![[], [I41N0, I41N1, I41N2], [], [I47N1], [], [], [], [], [I71N0, I71N1, I71N2], [I73N0, I73N1, I73N2], [I79N0, I79N1, I79N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
