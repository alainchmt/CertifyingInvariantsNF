
import IdealArithmetic.Examples.NF3_3_392472_1.RI3_3_392472_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![182, 162, -45]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![182, 162, -45]] 
 ![![37, 0, 0], ![0, 37, 0], ![5, 26, 1]] where
  M :=![![![182, 162, -45], ![-1485, -1321, 369], ![6831, 6084, -1690]]]
  hmulB := by decide  
  f := ![![![338, 0, -9]], ![![-297, 5, 9]], ![![-155, 4, 5]]]
  g := ![![![11, 36, -45], ![-90, -295, 369], ![413, 1352, -1690]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [30, 35, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 36], [0, 1]]
 g := ![![[32, 21], [27], [33, 1], [4], [1]], ![[0, 16], [27], [35, 36], [4], [1]]]
 h' := ![![[2, 36], [11, 13], [9, 8], [3, 36], [7, 2], [0, 1]], ![[0, 1], [0, 24], [25, 29], [1, 1], [11, 35], [2, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [7, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [30, 35, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![129, 360, 233]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-28, -154, 233]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![338, 0, -9]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![338, 0, -9]] 
 ![![37, 0, 0], ![23, 1, 0], ![20, 0, 1]] where
  M :=![![![338, 0, -9], ![-297, 5, 9], ![297, 18, -4]]]
  hmulB := by decide  
  f := ![![![182, 162, -45]], ![![73, 65, -18]], ![![283, 252, -70]]]
  g := ![![![14, 0, -9], ![-16, 5, 9], ![-1, 18, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![182, 162, -45]] ![![338, 0, -9]]
  ![![37, 0, 0]] where
 M := ![![![37, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [2, 2, 31, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 37, 13], [13, 3, 28], [0, 1]]
 g := ![![[22, 19, 32], [14, 36], [34, 20], [16, 10, 1], []], ![[8, 34, 13, 14], [2, 33], [33, 10], [11, 28, 31, 35], [28, 5]], ![[28, 26, 34, 14], [25, 10], [15, 1], [16, 33, 40, 38], [13, 5]]]
 h' := ![![[38, 37, 13], [18, 21, 27], [13, 22, 35], [9, 30, 15], [0, 0, 1], [0, 1]], ![[13, 3, 28], [39, 12, 26], [24, 0, 22], [34, 29, 25], [35, 40, 3], [38, 37, 13]], ![[0, 1], [11, 8, 29], [15, 19, 25], [2, 23, 1], [20, 1, 37], [13, 3, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25, 35], []]
 b := ![[], [30, 31, 32], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [2, 2, 31, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-31980, 64042, 105944]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-780, 1562, 2584]
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


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [9, 19, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 20, 24], [20, 22, 19], [0, 1]]
 g := ![![[8, 9, 38], [42, 4, 35], [11, 38], [19, 34, 1], []], ![[24, 11, 13, 6], [36, 24, 31, 16], [39, 25], [6, 24, 3, 6], [33, 17]], ![[32, 16, 38, 29], [35, 31, 2, 19], [10, 16], [0, 20, 14, 32], [38, 17]]]
 h' := ![![[14, 20, 24], [9, 41, 9], [31, 7, 32], [1, 21, 34], [0, 0, 1], [0, 1]], ![[20, 22, 19], [18, 1, 21], [36, 23, 12], [0, 35, 5], [28, 38, 22], [14, 20, 24]], ![[0, 1], [18, 1, 13], [6, 13, 42], [28, 30, 4], [15, 5, 20], [20, 22, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29, 16], []]
 b := ![[], [6, 19, 28], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [9, 19, 9, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-219128, 516, -19522]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5096, 12, -454]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-553, -278, 84]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-553, -278, 84]] 
 ![![47, 0, 0], ![0, 47, 0], ![13, 9, 1]] where
  M :=![![![-553, -278, 84], ![2772, 2277, -640], ![-11946, -10454, 2917]]]
  hmulB := by decide  
  f := ![![![1033, 1430, 284]], ![![9372, 12971, 2576]], ![![2885, 3993, 793]]]
  g := ![![![-35, -22, 84], ![236, 171, -640], ![-1061, -781, 2917]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [1, 35, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 46], [0, 1]]
 g := ![![[35, 1], [35, 1], [35, 1], [12, 3], [1]], ![[0, 46], [0, 46], [0, 46], [1, 44], [1]]]
 h' := ![![[12, 46], [12, 46], [12, 46], [35, 1], [46, 12], [0, 1]], ![[0, 1], [0, 1], [0, 1], [0, 46], [2, 35], [12, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [35, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [1, 35, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-128, 620, 753]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-211, -131, 753]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1033, 1430, 284]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![1033, 1430, 284]] 
 ![![47, 0, 0], ![30, 1, 0], ![5, 0, 1]] where
  M :=![![![1033, 1430, 284], ![9372, 12971, 2576], ![37818, 52342, 10395]]]
  hmulB := by decide  
  f := ![![![-553, -278, 84]], ![![-294, -129, 40]], ![![-313, -252, 71]]]
  g := ![![![-921, 1430, 284], ![-8354, 12971, 2576], ![-33711, 52342, 10395]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-553, -278, 84]] ![![1033, 1430, 284]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0]] 
 ![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [25, 34, 13, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [7, 10, 2], [33, 42, 51], [0, 1]]
 g := ![![[40, 14, 24], [33, 52], [43, 0, 13], [12, 10], [1]], ![[38, 40, 22, 20], [43, 46], [18, 7, 50, 51], [0, 7], [34, 45, 16, 8]], ![[18, 6, 20, 2], [21, 1], [40, 39, 1, 31], [8, 28], [40, 41, 25, 45]]]
 h' := ![![[7, 10, 2], [36, 6, 36], [38, 18, 30], [7, 35, 38], [28, 19, 40], [0, 1]], ![[33, 42, 51], [28, 23, 40], [34, 52, 24], [52, 43, 23], [23, 37, 22], [7, 10, 2]], ![[0, 1], [51, 24, 30], [29, 36, 52], [6, 28, 45], [10, 50, 44], [33, 42, 51]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42, 24], []]
 b := ![[], [47, 36, 41], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [25, 34, 13, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-30104, -66250, -34291]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-568, -1250, -647]
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


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [29, 5, 15, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [56, 6, 55], [47, 52, 4], [0, 1]]
 g := ![![[53], [50, 56, 41], [51, 12], [1, 20, 48], [1]], ![[20, 16, 5, 30], [2, 44, 2, 52], [9, 4], [50, 58, 20, 40], [5, 22, 9, 54]], ![[37, 52, 47, 29], [6, 18, 34, 1], [51, 45], [26, 46, 12, 20], [39, 16, 2, 5]]]
 h' := ![![[56, 6, 55], [25, 17], [11, 7, 10], [30, 20, 22], [30, 54, 44], [0, 1]], ![[47, 52, 4], [33, 43, 50], [56, 2, 20], [9, 32, 2], [5, 30, 7], [56, 6, 55]], ![[0, 1], [57, 58, 9], [5, 50, 29], [56, 7, 35], [32, 34, 8], [47, 52, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45, 24], []]
 b := ![[], [2, 35, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [29, 5, 15, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![20889776, 36870634, 14166195]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![354064, 624926, 240105]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1939, 12, 50]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![-1939, 12, 50]] 
 ![![61, 0, 0], ![0, 61, 0], ![21, 10, 1]] where
  M :=![![![-1939, 12, 50], ![1650, -77, -26], ![-1254, 344, -51]]]
  hmulB := by decide  
  f := ![![![-211, -292, -58]], ![![-1914, -2649, -526]], ![![-513, -710, -141]]]
  g := ![![![-49, -8, 50], ![36, 3, -26], ![-3, 14, -51]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [11, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [47, 60], [0, 1]]
 g := ![![[29, 42], [5], [9, 52], [11, 4], [47, 1]], ![[51, 19], [5], [13, 9], [16, 57], [33, 60]]]
 h' := ![![[47, 60], [47, 15], [23, 35], [1, 33], [32, 2], [0, 1]], ![[0, 1], [20, 46], [21, 26], [27, 28], [4, 59], [47, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [28, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [11, 14, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![97, 174, 54]
  a := ![-1, 2, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-17, -6, 54]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-211, -292, -58]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![-211, -292, -58]] 
 ![![61, 0, 0], ![42, 1, 0], ![12, 0, 1]] where
  M :=![![![-211, -292, -58], ![-1914, -2649, -526], ![-7722, -10688, -2123]]]
  hmulB := by decide  
  f := ![![![-1939, 12, 50]], ![![-1308, 7, 34]], ![![-402, 8, 9]]]
  g := ![![![209, -292, -58], ![1896, -2649, -526], ![7650, -10688, -2123]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![-1939, 12, 50]] ![![-211, -292, -58]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 136, 28]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![61, 136, 28]] 
 ![![67, 0, 0], ![0, 67, 0], ![62, 24, 1]] where
  M :=![![![61, 136, 28], ![924, 1233, 244], ![3564, 4976, 989]]]
  hmulB := by decide  
  f := ![![![79, 72, -20]], ![![-660, -589, 164]], ![![-118, -104, 29]]]
  g := ![![![-25, -8, 28], ![-212, -69, 244], ![-862, -280, 989]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [4, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [55, 66], [0, 1]]
 g := ![![[3, 17], [35, 64], [4], [40], [10], [1]], ![[0, 50], [4, 3], [4], [40], [10], [1]]]
 h' := ![![[55, 66], [61, 33], [46, 8], [14, 2], [43, 43], [63, 55], [0, 1]], ![[0, 1], [0, 34], [17, 59], [57, 65], [63, 24], [6, 12], [55, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [2, 45]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [4, 12, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![169, 1105, 998]
  a := ![0, 3, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-921, -341, 998]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-79, -72, 20]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![-79, -72, 20]] 
 ![![67, 0, 0], ![20, 1, 0], ![58, 0, 1]] where
  M :=![![![-79, -72, 20], ![660, 589, -164], ![-3036, -2704, 753]]]
  hmulB := by decide  
  f := ![![![-61, -136, -28]], ![![-32, -59, -12]], ![![-106, -192, -39]]]
  g := ![![![3, -72, 20], ![-24, 589, -164], ![110, -2704, 753]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![61, 136, 28]] ![![-79, -72, 20]]
  ![![67, 0, 0]] where
 M := ![![![-67, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-342230, 444, 9209]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-342230, 444, 9209]] 
 ![![71, 0, 0], ![0, 71, 0], ![14, 60, 1]] where
  M :=![![![-342230, 444, 9209], ![303897, -1053, -8321], ![-289245, -1990, 7268]]]
  hmulB := by decide  
  f := ![![![-341014, -303562, 84543]], ![![2789919, 2483515, -691667]], ![![2110049, 1878312, -523116]]]
  g := ![![![-6636, -7776, 9209], ![5921, 7017, -8321], ![-5507, -6170, 7268]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [10, 39, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [32, 70], [0, 1]]
 g := ![![[11, 64], [17, 15], [18, 15], [18], [30], [1]], ![[0, 7], [0, 56], [1, 56], [18], [30], [1]]]
 h' := ![![[32, 70], [43, 63], [33, 50], [60, 21], [13, 36], [61, 32], [0, 1]], ![[0, 1], [0, 8], [0, 21], [22, 50], [29, 35], [20, 39], [32, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43]]
 b := ![[], [11, 57]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [10, 39, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2072, 3200, 1142]
  a := ![2, -8, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-196, -920, 1142]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![341014, 303562, -84543]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![341014, 303562, -84543]] 
 ![![71, 0, 0], ![23, 1, 0], ![8, 0, 1]] where
  M :=![![![341014, 303562, -84543], ![-2789919, -2483515, 691667], ![12807465, 11400880, -3175182]]]
  hmulB := by decide  
  f := ![![![342230, -444, -9209]], ![![106583, -129, -2866]], ![![42635, -22, -1140]]]
  g := ![![![-84008, 303562, -84543], ![687290, -2483515, 691667], ![-3155089, 11400880, -3175182]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-342230, 444, 9209]] ![![341014, 303562, -84543]]
  ![![71, 0, 0]] where
 M := ![![![-71, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0]] 
 ![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [40, 25, 32, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 64], [26, 8], [0, 1]]
 g := ![![[27, 7, 12], [23, 64], [72, 54], [1, 15, 18], [41, 1], []], ![[58, 55, 23], [34, 8], [6, 25], [42, 42, 71], [56, 64], []], ![[72, 11, 38], [8, 1], [16, 67], [3, 16, 57], [67, 8], []]]
 h' := ![![[15, 64], [17, 64, 31], [34, 61, 8], [33, 20, 45], [39, 30, 50], [0, 0, 1], [0, 1]], ![[26, 8], [68, 33, 29], [48, 65, 64], [19, 7, 68], [59, 27, 35], [6, 22, 8], [15, 64]], ![[0, 1], [7, 49, 13], [20, 20, 1], [21, 46, 33], [17, 16, 61], [19, 51, 64], [26, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32], []]
 b := ![[], [51, 5, 47], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [40, 25, 32, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4307, -292, 5475]
  a := ![13, 0, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![59, -4, 75]
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


def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![230995, 205628, -57268]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![230995, 205628, -57268]] 
 ![![79, 0, 0], ![10, 1, 0], ![24, 0, 1]] where
  M :=![![![230995, 205628, -57268], ![-1889844, -1682293, 468524], ![8675568, 7722772, -2150817]]]
  hmulB := by decide  
  f := ![![![354853, 491180, 97548]], ![![85666, 118571, 23548]], ![![272232, 376796, 74831]]]
  g := ![![![-5707, 205628, -57268], ![46690, -1682293, 468524], ![-214336, 7722772, -2150817]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N0 : Nat.card (O ⧸ I79N0) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N0)

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := prime_ideal_of_norm_prime hp79.out _ NI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3961, 3526, -982]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![3961, 3526, -982]] 
 ![![79, 0, 0], ![74, 1, 0], ![69, 0, 1]] where
  M :=![![![3961, 3526, -982], ![-32406, -28847, 8034], ![148764, 132426, -36881]]]
  hmulB := by decide  
  f := ![![![-4277, 74, 130]], ![![-3952, 77, 122]], ![![-3759, 96, 121]]]
  g := ![![![-2395, 3526, -982], ![19594, -28847, 8034], ![-89949, 132426, -36881]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![230995, 205628, -57268]] ![![3961, 3526, -982]]
  ![![-14268026525, -12701034714, 3537279370]] where
 M := ![![![-14268026525, -12701034714, 3537279370]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI79N1 : IdealMulLeCertificate' Table 
  ![![-14268026525, -12701034714, 3537279370]] ![![3961, 3526, -982]]
  ![![79, 0, 0]] where
 M := ![![![881293906075039, 784505444719228, -218487311289696]]]
 hmul := by decide  
 g := ![![![![11155619064241, 9930448667332, -2765662168224]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1, I79N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
    exact isPrimeI79N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0 ⊙ MulI79N1)


lemma PB140I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB140I1 : PrimesBelowBoundCertificateInterval O 31 79 140 where
  m := 11
  g := ![2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB140I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0]
    · exact ![I43N0]
    · exact ![I47N0, I47N1]
    · exact ![I53N0]
    · exact ![I59N0]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1]
    · exact ![I73N0]
    · exact ![I79N0, I79N1, I79N1]
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
    · exact ![148877]
    · exact ![205379]
    · exact ![3721, 61]
    · exact ![4489, 67]
    · exact ![5041, 71]
    · exact ![389017]
    · exact ![79, 79, 79]
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
      exact NI71N1
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
      exact NI79N1
  β := ![I37N1, I47N1, I61N1, I67N1, I71N1, I79N0, I79N1]
  Il := ![[I37N1], [], [], [I47N1], [], [], [I61N1], [I67N1], [I71N1], [], [I79N0, I79N1, I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
