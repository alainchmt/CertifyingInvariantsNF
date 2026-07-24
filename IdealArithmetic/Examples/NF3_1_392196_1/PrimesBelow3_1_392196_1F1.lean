
import IdealArithmetic.Examples.NF3_1_392196_1.RI3_1_392196_1
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [21, 14, 22, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 25, 8], [19, 11, 29], [0, 1]]
 g := ![![[9], [18, 21], [29, 15, 10], [15, 1], []], ![[10, 27, 25, 20], [17, 10], [8, 7, 20, 31], [34, 10], [28, 27]], ![[5, 7, 23, 17], [24, 4], [9, 33, 17, 35], [22, 33], [7, 27]]]
 h' := ![![[33, 25, 8], [22, 3], [20, 10, 24], [18, 28, 26], [0, 0, 1], [0, 1]], ![[19, 11, 29], [10, 1, 24], [16, 36, 11], [19, 18, 29], [20, 25, 11], [33, 25, 8]], ![[0, 1], [5, 33, 13], [18, 28, 2], [9, 28, 19], [29, 12, 25], [19, 11, 29]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 21], []]
 b := ![[], [11, 8, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [21, 14, 22, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![21016, 7992, -16983]
  a := ![-1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![568, 216, -459]
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


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [4, 2, 8, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 14, 33], [16, 26, 8], [0, 1]]
 g := ![![[6, 10, 37], [17, 32], [25, 23], [21, 33, 1], []], ![[15, 17, 13, 20], [26, 1], [11, 1], [3, 7, 18, 4], [2, 23]], ![[8, 31, 36, 20], [38, 5], [40, 40], [10, 38, 10, 10], [27, 23]]]
 h' := ![![[17, 14, 33], [5, 29, 18], [27, 21, 27], [39, 31, 8], [0, 0, 1], [0, 1]], ![[16, 26, 8], [21, 30, 31], [17, 17, 1], [26, 30, 1], [35, 11, 26], [17, 14, 33]], ![[0, 1], [17, 23, 33], [13, 3, 13], [38, 21, 32], [25, 30, 14], [16, 26, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21, 25], []]
 b := ![[], [12, 9, 39], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [4, 2, 8, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1014586, -370558, 94423]
  a := ![2, -5, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![24746, -9038, 2303]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![5, -19, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![5, -19, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![5, 24, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![5, -19, 1], ![42, 21, -112], ![-1474, 424, -54]]]
  hmulB := by decide  
  f := ![![![-4, 19, -1], ![43, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-5, -24, 43]], ![![0, -1, 1], ![14, 63, -112], ![-28, 40, -54]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [20, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [29, 42], [0, 1]]
 g := ![![[5, 31], [28, 15], [38], [9, 24], [1]], ![[1, 12], [33, 28], [38], [17, 19], [1]]]
 h' := ![![[29, 42], [42, 17], [35, 12], [35, 9], [23, 29], [0, 1]], ![[0, 1], [19, 26], [39, 31], [38, 34], [4, 14], [29, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40]]
 b := ![[], [11, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [20, 14, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![750829, 114254, -346209]
  a := ![-65, 2, -131]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![57718, 195890, -346209]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-17, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-17, 1, 0]] 
 ![![43, 0, 0], ![26, 1, 0], ![11, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-17, 1, 0], ![2, -19, 6], ![80, -22, -15]]]
  hmulB := by decide  
  f := ![![![-12, 284, -90], ![43, 645, 0]], ![![0, 170, -54], ![44, 387, 0]], ![![8, 72, -23], ![39, 165, 0]]]
  g := ![![![1, 0, 0], ![-26, 43, 0], ![-11, 0, 43]], ![![-1, 1, 0], ![10, -19, 6], ![19, -22, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![5, -19, 1]] ![![43, 0, 0], ![-17, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-731, 43, 0]], ![![215, -817, 43], ![-43, 344, -129]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-17, 1, 0]]], ![![![5, -19, 1]], ![![-1, 8, -3]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![11, 20, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![11, 20, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![11, 20, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![11, 20, 1], ![120, -51, 122], ![1646, -434, 30]]]
  hmulB := by decide  
  f := ![![![-10, -20, -1], ![47, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-11, -20, 47]], ![![0, 0, 1], ![-26, -53, 122], ![28, -22, 30]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [42, 28, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 46], [0, 1]]
 g := ![![[32, 28], [7, 12], [16, 14], [46, 32], [1]], ![[0, 19], [0, 35], [0, 33], [43, 15], [1]]]
 h' := ![![[19, 46], [35, 13], [33, 23], [42, 25], [5, 19], [0, 1]], ![[0, 1], [0, 34], [0, 24], [0, 22], [37, 28], [19, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [32, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [42, 28, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2204, 1590, -1213]
  a := ![-2, 4, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![237, 550, -1213]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![19, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![19, 1, 0]] 
 ![![47, 0, 0], ![19, 1, 0], ![17, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![19, 1, 0], ![2, 17, 6], ![80, -22, 21]]]
  hmulB := by decide  
  f := ![![![214, 2292, 810], ![141, -6345, 0]], ![![70, 916, 324], ![95, -2538, 0]], ![![77, 829, 293], ![52, -2295, 0]]]
  g := ![![![1, 0, 0], ![-19, 47, 0], ![-17, 0, 47]], ![![0, 1, 0], ![-9, 17, 6], ![3, -22, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![11, 20, 1]] ![![47, 0, 0], ![19, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![893, 47, 0]], ![![517, 940, 47], ![329, 329, 141]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![19, 1, 0]]], ![![![11, 20, 1]], ![![7, 7, 3]]]]
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


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [14, 42, 33, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [10, 2, 25], [10, 50, 28], [0, 1]]
 g := ![![[22, 25, 15], [5, 4], [3, 33, 43], [13, 29], [1]], ![[40, 33, 51, 25], [1, 15], [35, 10, 11, 24], [24, 9], [43, 52, 52, 43]], ![[45, 20, 41, 44], [0, 28], [44, 49, 8, 17], [32, 52], [36, 50, 34, 10]]]
 h' := ![![[10, 2, 25], [51, 14, 11], [11, 32, 51], [14, 12, 34], [39, 11, 20], [0, 1]], ![[10, 50, 28], [2, 44, 52], [4, 37, 11], [22, 6, 39], [27, 27, 3], [10, 2, 25]], ![[0, 1], [40, 48, 43], [26, 37, 44], [19, 35, 33], [19, 15, 30], [10, 50, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 13], []]
 b := ![[], [21, 0, 44], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [14, 42, 33, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![25546, 8586, -19080]
  a := ![-1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![482, 162, -360]
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


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [32, 49, 32, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 44, 27], [16, 14, 32], [0, 1]]
 g := ![![[31, 0, 12], [19, 16, 15], [19, 15], [33, 45, 21], [1]], ![[6, 37, 46, 16], [11, 27, 15, 28], [37, 17], [52, 22, 30, 27], [32, 6, 27, 36]], ![[52, 29, 19, 47], [51, 44, 53, 54], [26, 1], [2, 2, 24, 38], [56, 42, 28, 23]]]
 h' := ![![[11, 44, 27], [41, 2, 37], [18, 35, 29], [6, 32, 29], [27, 10, 27], [0, 1]], ![[16, 14, 32], [25, 13, 41], [24, 11, 53], [38, 56, 31], [12, 52, 58], [11, 44, 27]], ![[0, 1], [35, 44, 40], [22, 13, 36], [21, 30, 58], [3, 56, 33], [16, 14, 32]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 30], []]
 b := ![[], [5, 13, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [32, 49, 32, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1643032, 125316, -499258]
  a := ![2, 18, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![27848, 2124, -8462]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![16, 1, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![16, 1, 0]] 
 ![![61, 0, 0], ![16, 1, 0], ![24, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![16, 1, 0], ![2, 14, 6], ![80, -22, 18]]]
  hmulB := by decide  
  f := ![![![2045, 15862, 6804], ![854, -69174, 0]], ![![530, 4154, 1782], ![245, -18117, 0]], ![![808, 6241, 2677], ![323, -27216, 0]]]
  g := ![![![1, 0, 0], ![-16, 61, 0], ![-24, 0, 61]], ![![0, 1, 0], ![-6, 14, 6], ![0, -22, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N0 : Nat.card (O ⧸ I61N0) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N0)

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := prime_ideal_of_norm_prime hp61.out _ NI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![21, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![21, 1, 0]] 
 ![![61, 0, 0], ![21, 1, 0], ![5, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![21, 1, 0], ![2, 19, 6], ![80, -22, 23]]]
  hmulB := by decide  
  f := ![![![-1047, -11544, -3648], ![-488, 37088, 0]], ![![-355, -3968, -1254], ![-182, 12749, 0]], ![![-102, -947, -299], ![7, 3040, 0]]]
  g := ![![![1, 0, 0], ![-21, 61, 0], ![-5, 0, 61]], ![![0, 1, 0], ![-7, 19, 6], ![7, -22, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![24, 1, 0]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![61, 0, 0], ![24, 1, 0]] 
 ![![61, 0, 0], ![24, 1, 0], ![14, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![24, 1, 0], ![2, 22, 6], ![80, -22, 26]]]
  hmulB := by decide  
  f := ![![![-407, -5540, -1512], ![-244, 15372, 0]], ![![-174, -2177, -594], ![-60, 6039, 0]], ![![-106, -1272, -347], ![-24, 3528, 0]]]
  g := ![![![1, 0, 0], ![-24, 61, 0], ![-14, 0, 61]], ![![0, 1, 0], ![-10, 22, 6], ![4, -22, 26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![16, 1, 0]] ![![61, 0, 0], ![21, 1, 0]]
  ![![61, 0, 0], ![36, 16, 1]] where
 M := ![![![3721, 0, 0], ![1281, 61, 0]], ![![976, 61, 0], ![338, 35, 6]]]
 hmul := by decide  
 g := ![![![![25, -16, -1], ![61, 0, 0]], ![![-15, -15, -1], ![61, 0, 0]]], ![![![-20, -15, -1], ![61, 0, 0]], ![![2, -1, 0], ![6, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![36, 16, 1]] ![![61, 0, 0], ![24, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![1464, 61, 0]], ![![2196, 976, 61], ![976, 366, 122]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![24, 1, 0]]], ![![![36, 16, 1]], ![![16, 6, 2]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![1, 1, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![1, 1, 0]] 
 ![![67, 0, 0], ![1, 1, 0], ![34, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![1, 1, 0], ![2, -1, 6], ![80, -22, 3]]]
  hmulB := by decide  
  f := ![![![-89, 45, -270], ![0, 3015, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-46, 22, -137], ![56, 1530, 0]]]
  g := ![![![1, 0, 0], ![-1, 67, 0], ![-34, 0, 67]], ![![0, 1, 0], ![-3, -1, 6], ![0, -22, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N0 : Nat.card (O ⧸ I67N0) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N0)

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := prime_ideal_of_norm_prime hp67.out _ NI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![18, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![18, 1, 0]] 
 ![![67, 0, 0], ![18, 1, 0], ![64, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![18, 1, 0], ![2, 16, 6], ![80, -22, 20]]]
  hmulB := by decide  
  f := ![![![-4889, -43267, -16236], ![-1943, 181302, 0]], ![![-1326, -11609, -4356], ![-468, 48642, 0]], ![![-4676, -41330, -15509], ![-1834, 173184, 0]]]
  g := ![![![1, 0, 0], ![-18, 67, 0], ![-64, 0, 67]], ![![0, 1, 0], ![-10, 16, 6], ![-12, -22, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1

def I67N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-19, 1, 0]] i)))

def SI67N2: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-19, 1, 0]] 
 ![![67, 0, 0], ![48, 1, 0], ![12, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-19, 1, 0], ![2, -21, 6], ![80, -22, -17]]]
  hmulB := by decide  
  f := ![![![-283, 3379, -966], ![134, 10787, 0]], ![![-191, 2413, -690], ![135, 7705, 0]], ![![-47, 605, -173], ![37, 1932, 0]]]
  g := ![![![1, 0, 0], ![-48, 67, 0], ![-12, 0, 67]], ![![-1, 1, 0], ![14, -21, 6], ![20, -22, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N2 : Nat.card (O ⧸ I67N2) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N2)

lemma isPrimeI67N2 : Ideal.IsPrime I67N2 := prime_ideal_of_norm_prime hp67.out _ NI67N2
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![1, 1, 0]] ![![67, 0, 0], ![18, 1, 0]]
  ![![67, 0, 0], ![-19, 14, 1]] where
 M := ![![![4489, 0, 0], ![1206, 67, 0]], ![![67, 67, 0], ![20, 17, 6]]]
 hmul := by decide  
 g := ![![![![67, 0, 0], ![0, 0, 0]], ![![18, 1, 0], ![0, 0, 0]]], ![![![1, 1, 0], ![0, 0, 0]], ![![2, -1, 0], ![6, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![-19, 14, 1]] ![![67, 0, 0], ![-19, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-1273, 67, 0]], ![![-1273, 938, 67], ![469, -335, 67]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-19, 1, 0]]], ![![![-19, 14, 1]], ![![7, -5, 1]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![24, 1, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![24, 1, 0]] 
 ![![71, 0, 0], ![24, 1, 0], ![7, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![24, 1, 0], ![2, 22, 6], ![80, -22, 26]]]
  hmulB := by decide  
  f := ![![![193, 2638, 720], ![142, -8520, 0]], ![![56, 879, 240], ![72, -2840, 0]], ![![17, 260, 71], ![20, -840, 0]]]
  g := ![![![1, 0, 0], ![-24, 71, 0], ![-7, 0, 71]], ![![0, 1, 0], ![-8, 22, 6], ![6, -22, 26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N0 : Nat.card (O ⧸ I71N0) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N0)

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := prime_ideal_of_norm_prime hp71.out _ NI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-21, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-21, 1, 0]] 
 ![![71, 0, 0], ![50, 1, 0], ![50, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-21, 1, 0], ![2, -23, 6], ![80, -22, -19]]]
  hmulB := by decide  
  f := ![![![2809, -36621, 9558], ![-1278, -113103, 0]], ![![1970, -25770, 6726], ![-922, -79591, 0]], ![![1969, -25789, 6731], ![-931, -79650, 0]]]
  g := ![![![1, 0, 0], ![-50, 71, 0], ![-50, 0, 71]], ![![-1, 1, 0], ![12, -23, 6], ![30, -22, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, 1, 0]] i)))

def SI71N2: IdealEqSpanCertificate' Table ![![-3, 1, 0]] 
 ![![71, 0, 0], ![68, 1, 0], ![57, 0, 1]] where
  M :=![![![-3, 1, 0], ![2, -5, 6], ![80, -22, -1]]]
  hmulB := by decide  
  f := ![![![137, 1, 6]], ![![138, 1, 6]], ![![115, 1, 5]]]
  g := ![![![-1, 1, 0], ![0, -5, 6], ![23, -22, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![24, 1, 0]] ![![71, 0, 0], ![-21, 1, 0]]
  ![![137, 1, 6]] where
 M := ![![![5041, 0, 0], ![-1491, 71, 0]], ![![1704, 71, 0], ![-502, 1, 6]]]
 hmul := by decide  
 g := ![![![![-213, 71, 0]], ![![65, -26, 6]]], ![![![-70, 19, 6]], ![![28, -9, 0]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![137, 1, 6]] ![![-3, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![71, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![47, -11, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![47, -11, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![47, 62, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![47, -11, 1], ![58, 47, -64], ![-834, 248, 4]]]
  hmulB := by decide  
  f := ![![![-46, 11, -1], ![73, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-47, -62, 73]], ![![0, -1, 1], ![42, 55, -64], ![-14, 0, 4]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [11, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [49, 72], [0, 1]]
 g := ![![[42, 48], [46], [24], [63, 27], [65], [1]], ![[58, 25], [46], [24], [72, 46], [65], [1]]]
 h' := ![![[49, 72], [32, 62], [10, 51], [37, 43], [63, 63], [62, 49], [0, 1]], ![[0, 1], [4, 11], [27, 22], [27, 30], [11, 10], [54, 24], [49, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45]]
 b := ![[], [51, 59]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [11, 24, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2051, 1078, -609]
  a := ![-2, 4, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![364, 532, -609]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-9, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-9, 1, 0]] 
 ![![73, 0, 0], ![64, 1, 0], ![69, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-9, 1, 0], ![2, -11, 6], ![80, -22, -7]]]
  hmulB := by decide  
  f := ![![![-717, 4046, -2208], ![146, 26864, 0]], ![![-625, 3540, -1932], ![147, 23506, 0]], ![![-675, 3824, -2087], ![160, 25392, 0]]]
  g := ![![![1, 0, 0], ![-64, 73, 0], ![-69, 0, 73]], ![![-1, 1, 0], ![4, -11, 6], ![27, -22, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![47, -11, 1]] ![![73, 0, 0], ![-9, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-657, 73, 0]], ![![3431, -803, 73], ![-365, 146, -73]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-9, 1, 0]]], ![![![47, -11, 1]], ![![-5, 2, -1]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![43, 8, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![43, 8, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![43, 8, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![43, 8, 1], ![96, 5, 50], ![686, -170, 38]]]
  hmulB := by decide  
  f := ![![![-42, -8, -1], ![79, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-43, -8, 79]], ![![0, 0, 1], ![-26, -5, 50], ![-12, -6, 38]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [62, 37, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [42, 78], [0, 1]]
 g := ![![[35, 65], [54, 10], [59, 8], [77, 64], [26], [1]], ![[0, 14], [0, 69], [0, 71], [0, 15], [26], [1]]]
 h' := ![![[42, 78], [49, 12], [55, 57], [45, 61], [20, 71], [17, 42], [0, 1]], ![[0, 1], [0, 67], [0, 22], [0, 18], [0, 8], [43, 37], [42, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [66, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [62, 37, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![838, 437, -528]
  a := ![2, -1, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![298, 59, -528]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![29, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![29, 1, 0]] 
 ![![79, 0, 0], ![29, 1, 0], ![41, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![29, 1, 0], ![2, 27, 6], ![80, -22, 31]]]
  hmulB := by decide  
  f := ![![![-603, -9716, -2160], ![-316, 28440, 0]], ![![-235, -3563, -792], ![-78, 10428, 0]], ![![-328, -5043, -1121], ![-123, 14760, 0]]]
  g := ![![![1, 0, 0], ![-29, 79, 0], ![-41, 0, 79]], ![![0, 1, 0], ![-13, 27, 6], ![-7, -22, 31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![43, 8, 1]] ![![79, 0, 0], ![29, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![2291, 79, 0]], ![![3397, 632, 79], ![1343, 237, 79]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![29, 1, 0]]], ![![![43, 8, 1]], ![![17, 3, 1]]]]
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


lemma PB178I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB178I1 : PrimesBelowBoundCertificateInterval O 31 79 178 where
  m := 11
  g := ![1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB178I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0]
    · exact ![I59N0]
    · exact ![I61N0, I61N1, I61N2]
    · exact ![I67N0, I67N1, I67N2]
    · exact ![I71N0, I71N1, I71N2]
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
    · exact ![50653]
    · exact ![68921]
    · exact ![1849, 43]
    · exact ![2209, 47]
    · exact ![148877]
    · exact ![205379]
    · exact ![61, 61, 61]
    · exact ![67, 67, 67]
    · exact ![71, 71, 71]
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
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
      exact NI61N2
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
      exact NI67N2
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
      exact NI71N2
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I43N1, I47N1, I61N0, I61N1, I61N2, I67N0, I67N1, I67N2, I71N0, I71N1, I71N2, I73N1, I79N1]
  Il := ![[], [], [I43N1], [I47N1], [], [], [I61N0, I61N1, I61N2], [I67N0, I67N1, I67N2], [I71N0, I71N1, I71N2], [I73N1], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
