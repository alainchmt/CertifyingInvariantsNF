
import IdealArithmetic.Examples.NF3_1_410267_1.RI3_1_410267_1
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [6, 36, 24, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 33, 6], [25, 3, 31], [0, 1]]
 g := ![![[2, 36, 3], [12, 7], [21, 14, 3], [13, 1], []], ![[10, 19], [21, 21], [13, 7, 23, 17], [30, 9], [13, 36]], ![[24, 26, 21, 19], [7, 3], [21, 4, 14, 17], [18, 16], [25, 36]]]
 h' := ![![[25, 33, 6], [5, 11, 15], [22, 27, 28], [33, 7, 22], [0, 0, 1], [0, 1]], ![[25, 3, 31], [12, 16], [29, 4, 24], [32, 23, 34], [29, 4, 3], [25, 33, 6]], ![[0, 1], [5, 10, 22], [11, 6, 22], [2, 7, 18], [31, 33, 33], [25, 3, 31]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14, 31], []]
 b := ![[], [10, 4, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [6, 36, 24, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-221630, 63714, -34595]
  a := ![-2, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5990, 1722, -935]
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


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [19, 21, 36, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 20, 10], [21, 20, 31], [0, 1]]
 g := ![![[3, 21, 20], [3, 18], [5, 33], [4, 5, 1], []], ![[36, 39, 25, 33], [19, 5], [36, 10], [10, 5, 8, 23], [39, 18]], ![[12, 30, 14, 36], [32, 37], [14, 9], [36, 0, 24, 18], [18, 18]]]
 h' := ![![[25, 20, 10], [21, 37, 15], [23, 31, 31], [6, 26, 19], [0, 0, 1], [0, 1]], ![[21, 20, 31], [26, 6, 14], [31, 16, 28], [10, 3, 25], [7, 3, 20], [25, 20, 10]], ![[0, 1], [28, 39, 12], [12, 35, 23], [14, 12, 38], [17, 38, 20], [21, 20, 31]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40, 17], []]
 b := ![[], [9, 27, 27], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [19, 21, 36, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7721407, -1261078, 93808]
  a := ![5, 0, 13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![188327, -30758, 2288]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![15, 13, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![15, 13, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![15, 13, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![15, 13, 1], ![143, 15, 64], ![1469, -143, -11]]]
  hmulB := by decide  
  f := ![![![-14, -13, -1], ![43, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-15, -13, 43]], ![![0, 0, 1], ![-19, -19, 64], ![38, 0, -11]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [6, 18, 1] where
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
 g := ![![[3, 36], [18, 1], [11], [17, 23], [1]], ![[0, 7], [0, 42], [11], [33, 20], [1]]]
 h' := ![![[25, 42], [21, 37], [18, 1], [27, 22], [37, 25], [0, 1]], ![[0, 1], [0, 6], [0, 42], [18, 21], [17, 18], [25, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [18, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [6, 18, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1083346, 249994, -211339]
  a := ![-66, -64, -133]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![98917, 69707, -211339]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-21, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-21, 1, 0]] 
 ![![43, 0, 0], ![22, 1, 0], ![11, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-21, 1, 0], ![2, -20, 5], ![117, -13, -22]]]
  hmulB := by decide  
  f := ![![![-14, 359, -90], ![43, 774, 0]], ![![4, 179, -45], ![44, 387, 0]], ![![14, 91, -23], ![47, 198, 0]]]
  g := ![![![1, 0, 0], ![-22, 43, 0], ![-11, 0, 43]], ![![-1, 1, 0], ![9, -20, 5], ![15, -13, -22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![15, 13, 1]] ![![43, 0, 0], ![-21, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-903, 43, 0]], ![![645, 559, 43], ![-172, -258, 43]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-21, 1, 0]]], ![![![15, 13, 1]], ![![-4, -6, 1]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![20, -1, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![20, -1, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![20, 46, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![20, -1, 1], ![115, 6, -6], ![-169, 39, 8]]]
  hmulB := by decide  
  f := ![![![-19, 1, -1], ![47, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-20, -46, 47]], ![![0, -1, 1], ![5, 6, -6], ![-7, -7, 8]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [21, 44, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 46], [0, 1]]
 g := ![![[20, 9], [34, 7], [9, 4], [42, 9], [1]], ![[0, 38], [8, 40], [21, 43], [22, 38], [1]]]
 h' := ![![[3, 46], [38, 3], [46, 17], [11, 2], [26, 3], [0, 1]], ![[0, 1], [0, 44], [3, 30], [17, 45], [35, 44], [3, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [15, 37]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [21, 44, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5918, 4023, -2660]
  a := ![-5, -1, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1006, 2689, -2660]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![6, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![6, 1, 0]] 
 ![![47, 0, 0], ![6, 1, 0], ![39, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![6, 1, 0], ![2, 7, 5], ![117, -13, 5]]]
  hmulB := by decide  
  f := ![![![-329, -1175, -840], ![-47, 7896, 0]], ![![-42, -147, -105], ![1, 987, 0]], ![![-273, -975, -697], ![-39, 6552, 0]]]
  g := ![![![1, 0, 0], ![-6, 47, 0], ![-39, 0, 47]], ![![0, 1, 0], ![-5, 7, 5], ![0, -13, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![20, -1, 1]] ![![47, 0, 0], ![6, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![282, 47, 0]], ![![940, -47, 47], ![235, 0, 0]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![6, 1, 0]]], ![![![20, -1, 1]], ![![5, 0, 0]]]]
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


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [3, 25, 35, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 23, 9], [18, 29, 44], [0, 1]]
 g := ![![[0, 40, 15], [35, 4], [49, 32, 9], [3, 6], [1]], ![[47, 1, 22, 25], [12, 38], [30, 52, 35, 36], [47, 17], [42, 16, 2, 40]], ![[11, 12, 29, 40], [47, 47], [9, 42, 37, 44], [10, 9], [39, 40, 20, 13]]]
 h' := ![![[0, 23, 9], [39, 4, 11], [12, 4, 2], [0, 4, 50], [50, 28, 18], [0, 1]], ![[18, 29, 44], [8, 5, 37], [16, 28, 41], [47, 29, 2], [33, 15, 32], [0, 23, 9]], ![[0, 1], [29, 44, 5], [45, 21, 10], [51, 20, 1], [44, 10, 3], [18, 29, 44]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 41], []]
 b := ![[], [39, 10, 19], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [3, 25, 35, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-210039, 68158, -37895]
  a := ![-2, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3963, 1286, -715]
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


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [56, 12, 55, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [43, 17, 2], [20, 41, 57], [0, 1]]
 g := ![![[34, 1, 49], [1, 0, 45], [11, 26], [25, 27, 16], [1]], ![[3, 56, 30, 14], [42, 51, 33, 18], [58, 21], [18, 9, 1, 24], [23, 30, 0, 8]], ![[52, 0, 49, 7], [43, 29, 53, 17], [13, 46], [40, 39, 9, 5], [8, 55, 47, 51]]]
 h' := ![![[43, 17, 2], [3, 24, 7], [53, 11, 24], [16, 26, 47], [3, 47, 4], [0, 1]], ![[20, 41, 57], [48, 12, 40], [33, 43, 3], [53, 42, 32], [44, 8, 22], [43, 17, 2]], ![[0, 1], [57, 23, 12], [43, 5, 32], [2, 50, 39], [0, 4, 33], [20, 41, 57]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31, 22], []]
 b := ![[], [31, 28, 48], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [56, 12, 55, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2947817, 591829, -35931]
  a := ![3, 21, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![49963, 10031, -609]
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


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [35, 14, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 22, 28], [43, 38, 33], [0, 1]]
 g := ![![[5, 19, 12], [28, 1], [45, 21, 13], [47, 12, 39], [1]], ![[31, 15, 26, 55], [33, 14], [43, 39, 19, 6], [16, 5, 47, 26], [21, 3, 35, 53]], ![[9, 7, 41, 29], [58, 57], [32, 12, 14, 43], [9, 57, 57, 28], [46, 60, 53, 8]]]
 h' := ![![[8, 22, 28], [56, 9, 45], [11, 42, 60], [2, 25, 14], [26, 47, 51], [0, 1]], ![[43, 38, 33], [43, 52, 10], [10, 38, 40], [40, 22, 12], [21, 43, 21], [8, 22, 28]], ![[0, 1], [47, 0, 6], [8, 42, 22], [51, 14, 35], [0, 32, 50], [43, 38, 33]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54, 43], []]
 b := ![[], [46, 16, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [35, 14, 10, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1491755, 251808, -9333]
  a := ![-3, 1, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-24455, 4128, -153]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![38, 19, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![38, 19, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![38, 19, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![38, 19, 1], ![155, 44, 94], ![2171, -221, 6]]]
  hmulB := by decide  
  f := ![![![-37, -19, -1], ![67, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-38, -19, 67]], ![![0, 0, 1], ![-51, -26, 94], ![29, -5, 6]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [25, 58, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 66], [0, 1]]
 g := ![![[5, 59], [1, 4], [29], [54], [14], [1]], ![[0, 8], [37, 63], [29], [54], [14], [1]]]
 h' := ![![[9, 66], [42, 40], [59, 65], [39, 37], [7, 11], [42, 9], [0, 1]], ![[0, 1], [0, 27], [41, 2], [37, 30], [39, 56], [56, 58], [9, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39]]
 b := ![[], [63, 53]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [25, 58, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2111, 2027, -655]
  a := ![4, 3, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![403, 216, -655]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-27, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-27, 1, 0]] 
 ![![67, 0, 0], ![40, 1, 0], ![61, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-27, 1, 0], ![2, -26, 5], ![117, -13, -28]]]
  hmulB := by decide  
  f := ![![![4544, -74109, 14260], ![-2881, -191084, 0]], ![![2703, -44226, 8510], ![-1741, -114034, 0]], ![![4127, -67472, 12983], ![-2648, -173972, 0]]]
  g := ![![![1, 0, 0], ![-40, 67, 0], ![-61, 0, 67]], ![![-1, 1, 0], ![11, -26, 5], ![35, -13, -28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![38, 19, 1]] ![![67, 0, 0], ![-27, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-1809, 67, 0]], ![![2546, 1273, 67], ![-871, -469, 67]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-27, 1, 0]]], ![![![38, 19, 1]], ![![-13, -7, 1]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![31, 7, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![31, 7, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![31, 7, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![31, 7, 1], ![131, 25, 34], ![767, -65, 11]]]
  hmulB := by decide  
  f := ![![![-30, -7, -1], ![71, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-31, -7, 71]], ![![0, 0, 1], ![-13, -3, 34], ![6, -2, 11]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [9, 38, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 70], [0, 1]]
 g := ![![[20, 8], [17, 29], [50, 19], [12], [24], [1]], ![[0, 63], [51, 42], [38, 52], [12], [24], [1]]]
 h' := ![![[33, 70], [60, 24], [47, 61], [12, 44], [7, 56], [62, 33], [0, 1]], ![[0, 1], [0, 47], [1, 10], [44, 27], [9, 15], [15, 38], [33, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [15, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [9, 38, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6394, 1185, -1555]
  a := ![-5, -5, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![769, 170, -1555]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-34, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-34, 1, 0]] 
 ![![71, 0, 0], ![37, 1, 0], ![60, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-34, 1, 0], ![2, -33, 5], ![117, -13, -35]]]
  hmulB := by decide  
  f := ![![![785, -17416, 2640], ![-568, -37488, 0]], ![![415, -9071, 1375], ![-283, -19525, 0]], ![![672, -14718, 2231], ![-462, -31680, 0]]]
  g := ![![![1, 0, 0], ![-37, 71, 0], ![-60, 0, 71]], ![![-1, 1, 0], ![13, -33, 5], ![38, -13, -35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![31, 7, 1]] ![![71, 0, 0], ![-34, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-2414, 71, 0]], ![![2201, 497, 71], ![-923, -213, 0]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-34, 1, 0]]], ![![![31, 7, 1]], ![![-13, -3, 0]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-26, -30, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-26, -30, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![47, 43, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-26, -30, 1], ![57, -69, -151], ![-3562, 416, -9]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-47, -43, 73]], ![![-1, -1, 1], ![98, 88, -151], ![-43, 11, -9]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [43, 37, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [36, 72], [0, 1]]
 g := ![![[45, 70], [61], [38], [26, 3], [55], [1]], ![[10, 3], [61], [38], [61, 70], [55], [1]]]
 h' := ![![[36, 72], [32, 56], [63, 34], [50, 29], [68, 52], [30, 36], [0, 1]], ![[0, 1], [4, 17], [46, 39], [72, 44], [42, 21], [12, 37], [36, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20]]
 b := ![[], [39, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [43, 37, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-29475, 7022, -1514]
  a := ![6, -6, 14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![571, 988, -1514]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![5, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![5, 1, 0]] 
 ![![73, 0, 0], ![5, 1, 0], ![9, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![5, 1, 0], ![2, 6, 5], ![117, -13, 4]]]
  hmulB := by decide  
  f := ![![![695, 2110, 1760], ![146, -25696, 0]], ![![43, 143, 120], ![74, -1752, 0]], ![![85, 260, 217], ![28, -3168, 0]]]
  g := ![![![1, 0, 0], ![-5, 73, 0], ![-9, 0, 73]], ![![0, 1, 0], ![-1, 6, 5], ![2, -13, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-26, -30, 1]] ![![73, 0, 0], ![5, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![365, 73, 0]], ![![-1898, -2190, 73], ![-73, -219, -146]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![5, 1, 0]]], ![![![-26, -30, 1]], ![![-1, -3, -2]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![47, 38, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![47, 38, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![47, 38, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![47, 38, 1], ![193, 72, 189], ![4394, -468, -4]]]
  hmulB := by decide  
  f := ![![![-46, -38, -1], ![79, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-47, -38, 79]], ![![0, 0, 1], ![-110, -90, 189], ![58, -4, -4]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [61, 28, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [51, 78], [0, 1]]
 g := ![![[16, 2], [70, 21], [3, 4], [40, 51], [73], [1]], ![[39, 77], [35, 58], [49, 75], [34, 28], [73], [1]]]
 h' := ![![[51, 78], [75, 70], [54, 69], [9, 2], [58, 29], [18, 51], [0, 1]], ![[0, 1], [11, 9], [18, 10], [32, 77], [36, 50], [12, 28], [51, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55]]
 b := ![[], [69, 67]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [61, 28, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![45374, 15431, -10656]
  a := ![15, 13, 31]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![6914, 5321, -10656]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-31, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-31, 1, 0]] 
 ![![79, 0, 0], ![48, 1, 0], ![4, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-31, 1, 0], ![2, -30, 5], ![117, -13, -32]]]
  hmulB := by decide  
  f := ![![![2025, -37784, 6300], ![-1264, -99540, 0]], ![![1252, -22941, 3825], ![-710, -60435, 0]], ![![130, -1914, 319], ![6, -5040, 0]]]
  g := ![![![1, 0, 0], ![-48, 79, 0], ![-4, 0, 79]], ![![-1, 1, 0], ![18, -30, 5], ![11, -13, -32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![47, 38, 1]] ![![79, 0, 0], ![-31, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![-2449, 79, 0]], ![![3713, 3002, 79], ![-1264, -1106, 158]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![-31, 1, 0]]], ![![![47, 38, 1]], ![![-16, -14, 2]]]]
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


lemma PB182I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB182I1 : PrimesBelowBoundCertificateInterval O 31 79 182 where
  m := 11
  g := ![1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB182I1_primes
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
    · exact ![I61N0]
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1]
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
    · exact ![226981]
    · exact ![4489, 67]
    · exact ![5041, 71]
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
      exact NI79N1
  β := ![I43N1, I47N1, I67N1, I71N1, I73N1, I79N1]
  Il := ![[], [], [I43N1], [I47N1], [], [], [], [I67N1], [I71N1], [I73N1], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
