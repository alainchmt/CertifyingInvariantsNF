
import IdealArithmetic.Examples.NF3_1_948300_2.RI3_1_948300_2
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [11, 31, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 22, 35], [14, 14, 2], [0, 1]]
 g := ![![[29, 13, 4], [33, 26], [8, 8, 21], [28, 1], []], ![[0, 2, 16, 31], [17, 36], [20, 24, 35, 6], [6, 11], [24, 4]], ![[20, 12, 8, 5], [34, 34], [15, 12, 33, 17], [30, 3], [20, 4]]]
 h' := ![![[14, 22, 35], [18, 34, 35], [23, 30, 10], [25, 9, 13], [0, 0, 1], [0, 1]], ![[14, 14, 2], [1, 19, 15], [22, 13, 6], [7, 34, 16], [6, 13, 14], [14, 22, 35]], ![[0, 1], [24, 21, 24], [18, 31, 21], [24, 31, 8], [13, 24, 22], [14, 14, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 3], []]
 b := ![[], [8, 20, 20], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [11, 31, 9, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-439227, -82103, -15096]
  a := ![1, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-11871, -2219, -408]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-7, 11, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-7, 11, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![34, 11, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-7, 11, 1], ![186, 24, 32], ![2029, 279, 3]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-34, -11, 41]], ![![-1, 0, 1], ![-22, -8, 32], ![47, 6, 3]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [6, 30, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 40], [0, 1]]
 g := ![![[5, 10], [40], [36], [10, 39], [1]], ![[33, 31], [40], [36], [29, 2], [1]]]
 h' := ![![[11, 40], [39, 16], [22, 9], [22, 35], [35, 11], [0, 1]], ![[0, 1], [10, 25], [39, 32], [38, 6], [33, 30], [11, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38]]
 b := ![[], [39, 19]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [6, 30, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8907, 3776, 1536]
  a := ![-3, 0, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1491, -320, 1536]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![9, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![9, 1, 0]] 
 ![![41, 0, 0], ![9, 1, 0], ![38, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![9, 1, 0], ![-1, 10, 3], ![197, 20, 8]]]
  hmulB := by decide  
  f := ![![![1281, -12800, -3840], ![0, 52480, 0]], ![![280, -2800, -840], ![1, 11480, 0]], ![![1191, -11863, -3559], ![-17, 48640, 0]]]
  g := ![![![1, 0, 0], ![-9, 41, 0], ![-38, 0, 41]], ![![0, 1, 0], ![-5, 10, 3], ![-7, 20, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-7, 11, 1]] ![![41, 0, 0], ![9, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![369, 41, 0]], ![![-287, 451, 41], ![123, 123, 41]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![9, 1, 0]]], ![![![-7, 11, 1]], ![![3, 3, 1]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![2, 10, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![2, 10, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![2, 10, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![2, 10, 1], ![187, 32, 29], ![1832, 259, 13]]]
  hmulB := by decide  
  f := ![![![-1, -10, -1], ![43, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-2, -10, 43]], ![![0, 0, 1], ![3, -6, 29], ![42, 3, 13]]]
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
  c := ![1065924, 439187, 96641]
  a := ![1, -64, -67]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![20294, -12261, 96641]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![14, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![14, 1, 0]] 
 ![![43, 0, 0], ![14, 1, 0], ![30, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![14, 1, 0], ![-1, 15, 3], ![197, 20, 13]]]
  hmulB := by decide  
  f := ![![![1001, -15000, -3000], ![0, 43000, 0]], ![![325, -4875, -975], ![1, 13975, 0]], ![![700, -10465, -2093], ![-5, 30000, 0]]]
  g := ![![![1, 0, 0], ![-14, 43, 0], ![-30, 0, 43]], ![![0, 1, 0], ![-7, 15, 3], ![-11, 20, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![2, 10, 1]] ![![43, 0, 0], ![14, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![602, 43, 0]], ![![86, 430, 43], ![215, 172, 43]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![14, 1, 0]]], ![![![2, 10, 1]], ![![5, 4, 1]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-35, 12, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-35, 12, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![12, 12, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-35, 12, 1], ![185, -3, 35], ![2226, 299, -26]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-12, -12, 47]], ![![-1, 0, 1], ![-5, -9, 35], ![54, 13, -26]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [28, 25, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 46], [0, 1]]
 g := ![![[16, 42], [41, 14], [22, 17], [16, 14], [1]], ![[0, 5], [20, 33], [20, 30], [42, 33], [1]]]
 h' := ![![[22, 46], [27, 18], [42, 22], [22, 39], [19, 22], [0, 1]], ![[0, 1], [0, 29], [9, 25], [34, 8], [33, 25], [22, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [18, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [28, 25, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5569, 4066, 1083]
  a := ![3, -1, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-395, -190, 1083]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![12, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![12, 1, 0]] 
 ![![47, 0, 0], ![12, 1, 0], ![26, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![12, 1, 0], ![-1, 13, 3], ![197, 20, 11]]]
  hmulB := by decide  
  f := ![![![-155, 1871, 432], ![47, -6768, 0]], ![![-36, 468, 108], ![1, -1692, 0]], ![![-86, 1035, 239], ![27, -3744, 0]]]
  g := ![![![1, 0, 0], ![-12, 47, 0], ![-26, 0, 47]], ![![0, 1, 0], ![-5, 13, 3], ![-7, 20, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![-35, 12, 1]] ![![47, 0, 0], ![12, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![564, 47, 0]], ![![-1645, 564, 47], ![-235, 141, 47]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![12, 1, 0]]], ![![![-35, 12, 1]], ![![-5, 3, 1]]]]
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


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [7, 21, 14, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [32, 35, 30], [7, 17, 23], [0, 1]]
 g := ![![[3, 52, 38], [31, 29], [42, 6, 49], [17, 37], [1]], ![[38, 26, 37, 22], [6, 11], [27, 40, 7, 34], [14, 29], [5, 3, 50, 23]], ![[28, 31, 7, 41], [52, 38], [19, 25, 6, 35], [3, 43], [49, 20, 6, 30]]]
 h' := ![![[32, 35, 30], [41, 42, 12], [24, 1, 33], [36, 49, 46], [46, 32, 39], [0, 1]], ![[7, 17, 23], [26, 1, 33], [42, 10, 8], [25, 50, 26], [32, 16, 33], [32, 35, 30]], ![[0, 1], [44, 10, 8], [39, 42, 12], [32, 7, 34], [0, 5, 34], [7, 17, 23]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43, 39], []]
 b := ![[], [37, 20, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [7, 21, 14, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-433646, -78228, -14151]
  a := ![1, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-8182, -1476, -267]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![0, 1, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![0, 1, 0]] 
 ![![59, 0, 0], ![0, 1, 0], ![39, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![0, 1, 0], ![-1, 1, 3], ![197, 20, -1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![1, 0, -1], ![-20, 20, 0]]]
  g := ![![![1, 0, 0], ![0, 59, 0], ![-39, 0, 59]], ![![0, 1, 0], ![-2, 1, 3], ![4, 20, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N0 : Nat.card (O ⧸ I59N0) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N0)

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := prime_ideal_of_norm_prime hp59.out _ NI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![394151803629834, 85555461382405, 21891504509055]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![394151803629834, 85555461382405, 21891504509055]] 
 ![![59, 0, 0], ![1, 1, 0], ![58, 0, 1]] where
  M :=![![![394151803629834, 85555461382405, 21891504509055], ![4227070926901430, 917537355193339, 234774879638160], ![13833398270084195, 3002707993682345, 768317936937584]]]
  hmulB := by decide  
  f := ![![![315267776, 5324455, -10609845]], ![![-30172816, 1927454, 270735]], ![![352518767, -3570735, -8953126]]]
  g := ![![![-16290015580979, 85555461382405, 21891504509055], ![-174701855039071, 917537355193339, 234774879638160], ![-571724577389458, 3002707993682345, 768317936937584]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-1, 1, 0]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-1, 1, 0]] 
 ![![59, 0, 0], ![58, 1, 0], ![39, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-1, 1, 0], ![-1, 0, 3], ![197, 20, -2]]]
  hmulB := by decide  
  f := ![![![-3362, -1, 10092], ![59, -198476, 0]], ![![-3304, -1, 9918], ![60, -195054, 0]], ![![-2222, -1, 6671], ![59, -131196, 0]]]
  g := ![![![1, 0, 0], ![-58, 59, 0], ![-39, 0, 59]], ![![-1, 1, 0], ![-2, 0, 3], ![-15, 20, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![0, 1, 0]] ![![394151803629834, 85555461382405, 21891504509055]]
  ![![59, 0, 0], ![-20, -19, 1]] where
 M := ![![![23254956414160206, 5047772221561895, 1291598766034245]], ![![4227070926901430, 917537355193339, 234774879638160]]]
 hmul := by decide  
 g := ![![![![349434865923734, 43074370561610, 24127351394360], ![-131914966232995, 0, 0]]], ![![![63517038530870, 7829660750716, 4385646818935], ![-23978282679005, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-20, -19, 1]] ![![59, 0, 0], ![-1, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-59, 59, 0]], ![![-1180, -1121, 59], ![236, 0, -59]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-1, 1, 0]]], ![![![-20, -19, 1]], ![![4, 0, -1]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-817, 50, 8]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![-817, 50, 8]] 
 ![![61, 0, 0], ![0, 61, 0], ![58, 52, 1]] where
  M :=![![![-817, 50, 8], ![1526, -607, 142], ![8746, 1472, -699]]]
  hmulB := by decide  
  f := ![![![-3529, -766, -196]], ![![-37846, -8215, -2102]], ![![-37648, -8172, -2091]]]
  g := ![![![-21, -6, 8], ![-110, -131, 142], ![808, 620, -699]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [42, 29, 1] where
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
 g := ![![[37, 16], [57], [13, 1], [30, 36], [32, 1]], ![[0, 45], [57], [45, 60], [23, 25], [3, 60]]]
 h' := ![![[32, 60], [55, 4], [3, 22], [21, 1], [59, 6], [0, 1]], ![[0, 1], [0, 57], [36, 39], [53, 60], [7, 55], [32, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59]]
 b := ![[], [16, 60]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [42, 29, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![30461, 5312, 1599]
  a := ![-1, 21, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1021, -1276, 1599]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3529, -766, -196]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![-3529, -766, -196]] 
 ![![61, 0, 0], ![28, 1, 0], ![34, 0, 1]] where
  M :=![![![-3529, -766, -196], ![-37846, -8215, -2102], ![-123854, -26884, -6879]]]
  hmulB := by decide  
  f := ![![![-817, 50, 8]], ![![-350, 13, 6]], ![![-312, 52, -7]]]
  g := ![![![403, -766, -196], ![4322, -8215, -2102], ![14144, -26884, -6879]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![-817, 50, 8]] ![![-3529, -766, -196]]
  ![![61, 0, 0]] where
 M := ![![![61, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-2, 28, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-2, 28, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![65, 28, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-2, 28, 1], ![169, 46, 83], ![5378, 619, -9]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-65, -28, 67]], ![![-1, 0, 1], ![-78, -34, 83], ![89, 13, -9]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [48, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [54, 66], [0, 1]]
 g := ![![[24, 1], [29, 9], [22], [54], [35], [1]], ![[11, 66], [46, 58], [22], [54], [35], [1]]]
 h' := ![![[54, 66], [15, 66], [65, 64], [60, 42], [21, 56], [19, 54], [0, 1]], ![[0, 1], [28, 1], [37, 3], [50, 25], [30, 11], [54, 13], [54, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [53, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [48, 13, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3723, 800, 287]
  a := ![1, 1, -4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-334, -108, 287]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-16, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-16, 1, 0]] 
 ![![67, 0, 0], ![51, 1, 0], ![9, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-16, 1, 0], ![-1, -15, 3], ![197, 20, -17]]]
  hmulB := by decide  
  f := ![![![-581, -8971, 1794], ![67, -40066, 0]], ![![-438, -6826, 1365], ![68, -30485, 0]], ![![-79, -1205, 241], ![5, -5382, 0]]]
  g := ![![![1, 0, 0], ![-51, 67, 0], ![-9, 0, 67]], ![![-1, 1, 0], ![11, -15, 3], ![-10, 20, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![-2, 28, 1]] ![![67, 0, 0], ![-16, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-1072, 67, 0]], ![![-134, 1876, 67], ![201, -402, 67]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-16, 1, 0]]], ![![![-2, 28, 1]], ![![3, -6, 1]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-39, 17, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-39, 17, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![32, 17, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-39, 17, 1], ![180, -2, 50], ![3211, 399, -35]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-32, -17, 71]], ![![-1, 0, 1], ![-20, -12, 50], ![61, 14, -35]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [59, 53, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 70], [0, 1]]
 g := ![![[37, 36], [14, 9], [6, 29], [43], [40], [1]], ![[46, 35], [34, 62], [31, 42], [43], [40], [1]]]
 h' := ![![[18, 70], [26, 6], [1, 68], [31, 10], [56, 16], [12, 18], [0, 1]], ![[0, 1], [63, 65], [18, 3], [69, 61], [60, 55], [52, 53], [18, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [47, 50]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [59, 53, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2072, 3000, 1041]
  a := ![-2, 3, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-440, -207, 1041]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![21, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![21, 1, 0]] 
 ![![71, 0, 0], ![21, 1, 0], ![35, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![21, 1, 0], ![-1, 22, 3], ![197, 20, 20]]]
  hmulB := by decide  
  f := ![![![-636, 13551, 1848], ![71, -43736, 0]], ![![-203, 4003, 546], ![72, -12922, 0]], ![![-315, 6680, 911], ![40, -21560, 0]]]
  g := ![![![1, 0, 0], ![-21, 71, 0], ![-35, 0, 71]], ![![0, 1, 0], ![-8, 22, 3], ![-13, 20, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![-39, 17, 1]] ![![71, 0, 0], ![21, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![1491, 71, 0]], ![![-2769, 1207, 71], ![-639, 355, 71]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![21, 1, 0]]], ![![![-39, 17, 1]], ![![-9, 5, 1]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-28, 5, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-28, 5, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![45, 5, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-28, 5, 1], ![192, -3, 14], ![847, 159, -12]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-45, -5, 73]], ![![-1, 0, 1], ![-6, -1, 14], ![19, 3, -12]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [50, 49, 1] where
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
 g := ![![[55, 19], [37], [19], [26, 55], [65], [1]], ![[0, 54], [37], [19], [32, 18], [65], [1]]]
 h' := ![![[24, 72], [40, 47], [49, 16], [14, 26], [53, 36], [23, 24], [0, 1]], ![[0, 1], [0, 26], [68, 57], [54, 47], [41, 37], [15, 49], [24, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66]]
 b := ![[], [42, 33]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [50, 49, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6425, 2255, 305]
  a := ![0, -5, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-100, 10, 305]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-14, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-14, 1, 0]] 
 ![![73, 0, 0], ![59, 1, 0], ![12, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-14, 1, 0], ![-1, -13, 3], ![197, 20, -15]]]
  hmulB := by decide  
  f := ![![![-1155, -15211, 3510], ![73, -85410, 0]], ![![-930, -12286, 2835], ![74, -68985, 0]], ![![-182, -2501, 577], ![53, -14040, 0]]]
  g := ![![![1, 0, 0], ![-59, 73, 0], ![-12, 0, 73]], ![![-1, 1, 0], ![10, -13, 3], ![-11, 20, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-28, 5, 1]] ![![73, 0, 0], ![-14, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-1022, 73, 0]], ![![-2044, 365, 73], ![584, -73, 0]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-14, 1, 0]]], ![![![-28, 5, 1]], ![![8, -1, 0]]]]
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


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [19, 18, 73, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [74, 43, 27], [11, 35, 52], [0, 1]]
 g := ![![[46, 37, 62], [11], [53, 44, 38], [63, 58, 8], [6, 1], []], ![[40, 76, 68, 12], [50, 61, 27, 53], [3, 23, 23, 3], [28, 71, 53, 7], [2, 40], [60, 18]], ![[51, 8, 3, 55], [1, 76, 11, 26], [46, 3, 67, 62], [43, 22, 0, 40], [42, 32], [35, 18]]]
 h' := ![![[74, 43, 27], [28, 44, 33], [20, 13], [67, 16, 14], [44, 31, 18], [0, 0, 1], [0, 1]], ![[11, 35, 52], [64, 26, 52], [34, 6, 35], [19, 40, 53], [43, 71, 45], [70, 44, 35], [74, 43, 27]], ![[0, 1], [19, 9, 73], [5, 60, 44], [53, 23, 12], [73, 56, 16], [9, 35, 43], [11, 35, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26, 21], []]
 b := ![[], [67, 41, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [19, 18, 73, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2406577, 1131280, 99540]
  a := ![-2, -6, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-30463, 14320, 1260]
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



lemma PB276I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB276I1 : PrimesBelowBoundCertificateInterval O 31 79 276 where
  m := 11
  g := ![1, 2, 2, 2, 1, 3, 2, 2, 2, 2, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB276I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0]
    · exact ![I59N0, I59N1, I59N2]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1]
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
    · exact ![1681, 41]
    · exact ![1849, 43]
    · exact ![2209, 47]
    · exact ![148877]
    · exact ![59, 59, 59]
    · exact ![3721, 61]
    · exact ![4489, 67]
    · exact ![5041, 71]
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
      exact NI41N1
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
      exact NI59N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
  β := ![I41N1, I43N1, I47N1, I59N0, I59N1, I59N2, I61N1, I67N1, I71N1, I73N1]
  Il := ![[], [I41N1], [I43N1], [I47N1], [], [I59N0, I59N1, I59N2], [I61N1], [I67N1], [I71N1], [I73N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
