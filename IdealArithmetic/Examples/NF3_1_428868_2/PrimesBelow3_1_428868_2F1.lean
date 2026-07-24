
import IdealArithmetic.Examples.NF3_1_428868_2.RI3_1_428868_2
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [31, 15, 14, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 0, 8], [14, 36, 29], [0, 1]]
 g := ![![[20, 27, 28], [21, 27], [9, 9, 16], [23, 1], []], ![[32, 1, 25, 35], [6, 33], [34, 3, 6, 22], [14, 1], [29, 27]], ![[3, 18, 16, 13], [10, 16], [3, 15, 31, 31], [], [8, 27]]]
 h' := ![![[9, 0, 8], [8, 12, 19], [17, 19, 29], [27, 31, 33], [0, 0, 1], [0, 1]], ![[14, 36, 29], [3, 30, 3], [35, 1, 12], [26, 19, 30], [33, 23, 36], [9, 0, 8]], ![[0, 1], [2, 32, 15], [33, 17, 33], [3, 24, 11], [22, 14], [14, 36, 29]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 19], []]
 b := ![[], [9, 12, 30], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [31, 15, 14, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-81289, 53354, -26714]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2197, 1442, -722]
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


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [3, 15, 26, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 29, 16], [6, 11, 25], [0, 1]]
 g := ![![[38, 34, 37], [40, 9], [36, 39], [5, 15, 1], []], ![[36, 22, 39, 8], [33, 21], [18, 25], [2, 9, 21, 9], [12, 10]], ![[31, 15, 18, 32], [26, 20], [22, 10], [5, 15, 23, 33], [3, 10]]]
 h' := ![![[9, 29, 16], [39, 14, 18], [35, 32, 3], [26, 3, 11], [0, 0, 1], [0, 1]], ![[6, 11, 25], [32, 36, 12], [7, 19, 12], [15, 34, 5], [4, 25, 11], [9, 29, 16]], ![[0, 1], [35, 32, 11], [21, 31, 26], [13, 4, 25], [27, 16, 29], [6, 11, 25]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 11], []]
 b := ![[], [2, 36, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [3, 15, 26, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![401103, -170232, 36162]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![9783, -4152, 882]
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


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [40, 27, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 33, 19], [31, 9, 24], [0, 1]]
 g := ![![[2, 2, 23], [3, 36, 10], [13, 23], [9, 37, 1], []], ![[11, 14, 16, 42], [24, 9, 0, 33], [38, 16], [2, 42, 14, 34], [34, 17]], ![[36, 1, 15, 25], [39, 34, 10, 14], [29, 11], [3, 38, 16, 35], [29, 17]]]
 h' := ![![[6, 33, 19], [9, 20, 25], [37, 29, 15], [27, 40, 25], [0, 0, 1], [0, 1]], ![[31, 9, 24], [10, 22, 3], [2, 41, 41], [19, 37, 39], [9, 2, 9], [6, 33, 19]], ![[0, 1], [40, 1, 15], [15, 16, 30], [33, 9, 22], [16, 41, 33], [31, 9, 24]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36], []]
 b := ![[], [11, 23], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [40, 27, 6, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-230136, -7998, -6966]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5352, -186, -162]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0]] 
 ![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [7, 33, 41, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 29, 3], [32, 17, 44], [0, 1]]
 g := ![![[44, 31, 7], [35, 36, 21], [8, 6, 1], [3, 6, 1], []], ![[36, 41, 21, 36], [20, 17, 25, 4], [21, 46, 43, 21], [5, 26, 43, 21], [40, 9]], ![[27, 11, 44, 33], [1, 32, 36, 11], [23, 8, 12, 15], [11, 20, 12, 15], [46, 9]]]
 h' := ![![[21, 29, 3], [37, 37, 17], [38, 41, 31], [26, 0, 1], [0, 0, 1], [0, 1]], ![[32, 17, 44], [26, 7, 24], [15, 22, 39], [46, 23, 17], [20, 23, 17], [21, 29, 3]], ![[0, 1], [42, 3, 6], [35, 31, 24], [23, 24, 29], [44, 24, 29], [32, 17, 44]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 16], []]
 b := ![[], [3, 34, 26], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [7, 33, 41, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-686388, 362276, -129673]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-14604, 7708, -2759]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![22, -13, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![22, -13, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![22, 40, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![22, -13, 1], ![95, -20, -27], ![-1330, 439, 7]]]
  hmulB := by decide  
  f := ![![![-21, 13, -1], ![53, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-22, -40, 53]], ![![0, -1, 1], ![13, 20, -27], ![-28, 3, 7]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [11, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [32, 52], [0, 1]]
 g := ![![[26, 29], [4], [41, 4], [36], [32, 1]], ![[0, 24], [4], [10, 49], [36], [11, 52]]]
 h' := ![![[32, 52], [49, 20], [26, 2], [18, 2], [19, 6], [0, 1]], ![[0, 1], [0, 33], [37, 51], [29, 51], [52, 47], [32, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [42, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [11, 21, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![296, 172, -319]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![138, 244, -319]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-26, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-26, 1, 0]] 
 ![![53, 0, 0], ![27, 1, 0], ![46, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-26, 1, 0], ![0, -25, 2], ![95, -29, -27]]]
  hmulB := by decide  
  f := ![![![27, 849, -68], ![53, 1802, 0]], ![![27, 424, -34], ![54, 901, 0]], ![![20, 737, -59], ![39, 1564, 0]]]
  g := ![![![1, 0, 0], ![-27, 53, 0], ![-46, 0, 53]], ![![-1, 1, 0], ![11, -25, 2], ![40, -29, -27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![22, -13, 1]] ![![53, 0, 0], ![-26, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-1378, 53, 0]], ![![1166, -689, 53], ![-477, 318, -53]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-26, 1, 0]]], ![![![22, -13, 1]], ![![-9, 6, -1]]]]
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


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [31, 12, 14, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [36, 23, 19], [9, 35, 40], [0, 1]]
 g := ![![[35, 52, 25], [15, 56, 7], [58, 36], [40, 11, 19], [1]], ![[31, 56, 54, 4], [52, 57, 14, 16], [37, 17], [21, 43, 21, 12], [57, 3, 37, 15]], ![[44, 53, 27, 37], [19, 24, 30, 24], [21, 35], [23, 31, 21, 30], [8, 32, 1, 44]]]
 h' := ![![[36, 23, 19], [7, 52, 5], [32, 32, 19], [58, 22, 53], [28, 47, 45], [0, 1]], ![[9, 35, 40], [2, 4, 42], [34, 6, 34], [58, 13, 31], [49, 29, 49], [36, 23, 19]], ![[0, 1], [26, 3, 12], [18, 21, 6], [16, 24, 34], [9, 42, 24], [9, 35, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37, 31], []]
 b := ![[], [37, 58, 17], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [31, 12, 14, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8568393, -10119680, 8182474]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![145227, -171520, 138686]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-4, -19, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-4, -19, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![57, 42, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-4, -19, 1], ![95, -52, -39], ![-1900, 613, -13]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-57, -42, 61]], ![![-1, -1, 1], ![38, 26, -39], ![-19, 19, -13]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [36, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [32, 60], [0, 1]]
 g := ![![[33, 39], [3], [22, 12], [18, 22], [32, 1]], ![[0, 22], [3], [40, 49], [51, 39], [3, 60]]]
 h' := ![![[32, 60], [15, 51], [1, 8], [23, 16], [7, 12], [0, 1]], ![[0, 1], [0, 10], [13, 53], [47, 45], [25, 49], [32, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [20, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [36, 29, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![293, 4, 3]
  a := ![-1, 2, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2, -2, 3]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-22, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-22, 1, 0]] 
 ![![61, 0, 0], ![39, 1, 0], ![13, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-22, 1, 0], ![0, -21, 2], ![95, -29, -23]]]
  hmulB := by decide  
  f := ![![![815, -37, 0], ![2257, 0, 0]], ![![529, -24, 0], ![1465, 0, 0]], ![![191, 2, -1], ![529, 31, 0]]]
  g := ![![![1, 0, 0], ![-39, 61, 0], ![-13, 0, 61]], ![![-1, 1, 0], ![13, -21, 2], ![25, -29, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-4, -19, 1]] ![![61, 0, 0], ![-22, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-1342, 61, 0]], ![![-244, -1159, 61], ![183, 366, -61]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-22, 1, 0]]], ![![![-4, -19, 1]], ![![3, 6, -1]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![25, -11, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![25, -11, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![25, 56, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![25, -11, 1], ![95, -15, -23], ![-1140, 381, 8]]]
  hmulB := by decide  
  f := ![![![-24, 11, -1], ![67, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-25, -56, 67]], ![![0, -1, 1], ![10, 19, -23], ![-20, -1, 8]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [57, 55, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 66], [0, 1]]
 g := ![![[28, 4], [33, 4], [35], [22], [10], [1]], ![[9, 63], [14, 63], [35], [22], [10], [1]]]
 h' := ![![[12, 66], [62, 2], [13, 2], [20, 13], [66, 25], [10, 12], [0, 1]], ![[0, 1], [19, 65], [37, 65], [42, 54], [31, 42], [20, 55], [12, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [19, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [57, 55, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![532, 854, -437]
  a := ![0, 3, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![171, 378, -437]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![23, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![23, 1, 0]] 
 ![![67, 0, 0], ![23, 1, 0], ![59, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![23, 1, 0], ![0, 24, 2], ![95, -29, 22]]]
  hmulB := by decide  
  f := ![![![668, 29, 0], ![-1943, 0, 0]], ![![230, 10, 0], ![-669, 0, 0]], ![![580, 13, -1], ![-1687, 34, 0]]]
  g := ![![![1, 0, 0], ![-23, 67, 0], ![-59, 0, 67]], ![![0, 1, 0], ![-10, 24, 2], ![-8, -29, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![25, -11, 1]] ![![67, 0, 0], ![23, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![1541, 67, 0]], ![![1675, -737, 67], ![670, -268, 0]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![23, 1, 0]]], ![![![25, -11, 1]], ![![10, -4, 0]]]]
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


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [28, 66, 7, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 6, 60], [49, 64, 11], [0, 1]]
 g := ![![[2, 34, 10], [23, 27, 8], [2, 35, 8], [48, 5], [64, 1], []], ![[6, 13, 56, 54], [0, 54, 24, 18], [3, 59, 1, 60], [55, 38], [67, 49], [15, 50]], ![[47, 65, 45, 61], [32, 28, 37, 13], [36, 14, 27, 68], [7, 54], [69, 36], [64, 50]]]
 h' := ![![[15, 6, 60], [66, 10, 62], [15, 53, 47], [10, 41, 47], [54, 8, 54], [0, 0, 1], [0, 1]], ![[49, 64, 11], [54, 70, 24], [23, 37, 11], [51, 36, 1], [10, 59, 31], [18, 62, 64], [15, 6, 60]], ![[0, 1], [45, 62, 56], [66, 52, 13], [41, 65, 23], [33, 4, 57], [41, 9, 6], [49, 64, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52, 19], []]
 b := ![[], [45, 0, 34], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [28, 66, 7, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![537896, 2840, -214420]
  a := ![2, -8, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![7576, 40, -3020]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![47, -28, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![47, -28, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![47, 45, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![47, -28, 1], ![95, -10, -57], ![-2755, 874, 47]]]
  hmulB := by decide  
  f := ![![![-46, 28, -1], ![73, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-47, -45, 73]], ![![0, -1, 1], ![38, 35, -57], ![-68, -17, 47]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [2, 5, 1] where
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
 g := ![![[39, 37], [69], [4], [14, 2], [25], [1]], ![[0, 36], [69], [4], [4, 71], [25], [1]]]
 h' := ![![[68, 72], [7, 16], [46, 19], [45, 71], [27, 41], [71, 68], [0, 1]], ![[0, 1], [0, 57], [24, 54], [55, 2], [41, 32], [23, 5], [68, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47]]
 b := ![[], [4, 60]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [2, 5, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![141, 62, 3]
  a := ![13, 0, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![0, -1, 3]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-16, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-16, 1, 0]] 
 ![![73, 0, 0], ![57, 1, 0], ![26, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-16, 1, 0], ![0, -15, 2], ![95, -29, -17]]]
  hmulB := by decide  
  f := ![![![673, -42, 0], ![3066, 0, 0]], ![![529, -33, 0], ![2410, 0, 0]], ![![234, -7, -1], ![1066, 37, 0]]]
  g := ![![![1, 0, 0], ![-57, 73, 0], ![-26, 0, 73]], ![![-1, 1, 0], ![11, -15, 2], ![30, -29, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![47, -28, 1]] ![![73, 0, 0], ![-16, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-1168, 73, 0]], ![![3431, -2044, 73], ![-657, 438, -73]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-16, 1, 0]]], ![![![47, -28, 1]], ![![-9, 6, -1]]]]
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


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [58, 34, 50, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 9, 39], [17, 69, 40], [0, 1]]
 g := ![![[57, 53, 73], [5, 53, 62], [46, 74, 42], [61, 61, 52], [29, 1], []], ![[0, 71, 4, 77], [44, 12, 32, 15], [45, 50, 67, 27], [36, 36, 45, 63], [50, 21], [18, 20]], ![[18, 21, 63, 22], [74, 62, 39, 10], [2, 0, 48, 18], [68, 69, 14, 22], [21, 2], [17, 20]]]
 h' := ![![[12, 9, 39], [26, 3, 51], [18, 42, 46], [17, 52, 68], [56, 62, 17], [0, 0, 1], [0, 1]], ![[17, 69, 40], [61, 66, 2], [44, 60, 72], [34, 46, 5], [36, 18, 36], [48, 24, 69], [12, 9, 39]], ![[0, 1], [1, 10, 26], [33, 56, 40], [36, 60, 6], [5, 78, 26], [14, 55, 9], [17, 69, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17, 55], []]
 b := ![[], [43, 26, 31], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [58, 34, 50, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-270417, 333775, -246638]
  a := ![1, -5, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3423, 4225, -3122]
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



lemma PB186I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB186I1 : PrimesBelowBoundCertificateInterval O 31 79 186 where
  m := 11
  g := ![1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB186I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0]
    · exact ![I43N0]
    · exact ![I47N0]
    · exact ![I53N0, I53N1]
    · exact ![I59N0]
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
    · exact ![50653]
    · exact ![68921]
    · exact ![79507]
    · exact ![103823]
    · exact ![2809, 53]
    · exact ![205379]
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
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
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
  β := ![I53N1, I61N1, I67N1, I73N1]
  Il := ![[], [], [], [], [I53N1], [], [I61N1], [I67N1], [], [I73N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
