
import IdealArithmetic.Examples.NF3_1_441484_2.RI3_1_441484_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6583, 673, 49]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![6583, 673, 49]] 
 ![![37, 0, 0], ![1, 1, 0], ![30, 0, 1]] where
  M :=![![![6583, 673, 49], ![-4302, 9850, 7207], ![-81672, -1885, 3940]]]
  hmulB := by decide  
  f := ![![![-52394195, 2743985, -4367661]], ![![14034217, -734999, 1169914]], ![![-64443360, 3375023, -5372098]]]
  g := ![![![120, 673, 49], ![-6226, 9850, 7207], ![-5351, -1885, 3940]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-652, 17, 54]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-652, 17, 54]] 
 ![![37, 0, 0], ![36, 1, 0], ![4, 0, 1]] where
  M :=![![![-652, 17, 54], ![-6915, -675, -29], ![3477, -628, -666]]]
  hmulB := by decide  
  f := ![![![-431338, 22590, -35957]], ![![-292485, 15318, -24382]], ![![-227431, 11911, -18959]]]
  g := ![![![-40, 17, 54], ![473, -675, -29], ![777, -628, -666]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![6583, 673, 49]] ![![-652, 17, 54]]
  ![![-8775538, -373136, 303331]] where
 M := ![![![-8775538, -373136, 303331]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![-8775538, -373136, 303331]] ![![-652, 17, 54]]
  ![![37, 0, 0]] where
 M := ![![![9356568103, -87809214, -665076554]]]
 hmul := by decide  
 g := ![![![![252880219, -2373222, -17975042]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1, I37N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
    exact isPrimeI37N1
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


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [33, 23, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 3, 6], [29, 37, 35], [0, 1]]
 g := ![![[1, 13, 21], [35, 16], [1, 25], [34, 37, 1], []], ![[10, 39, 40, 7], [35, 8], [39, 10], [1, 25, 14, 14], [15, 36]], ![[30, 28, 32, 7], [18, 39], [19, 31], [23, 20, 20, 28], [27, 36]]]
 h' := ![![[8, 3, 6], [39, 16, 12], [28, 38, 4], [26, 6, 5], [0, 0, 1], [0, 1]], ![[29, 37, 35], [38, 22, 7], [2, 37, 7], [10, 14, 16], [20, 32, 37], [8, 3, 6]], ![[0, 1], [26, 3, 22], [28, 7, 30], [32, 21, 20], [32, 9, 3], [29, 37, 35]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37, 35], []]
 b := ![[], [32, 18, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [33, 23, 4, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1957176, 42066, 77121]
  a := ![-3, -6, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-47736, 1026, 1881]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, -2]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![31, 0, -2]] 
 ![![43, 0, 0], ![6, 1, 0], ![6, 0, 1]] where
  M :=![![![31, 0, -2], ![258, 35, 8], ![-210, 22, 29]]]
  hmulB := by decide  
  f := ![![![-839, 44, -70]], ![![96, -5, 8]], ![![-420, 22, -35]]]
  g := ![![![1, 0, -2], ![0, 35, 8], ![-12, 22, 29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N0)

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := prime_ideal_of_norm_prime hp43.out _ NI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![13, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![13, 1, 0]] 
 ![![43, 0, 0], ![13, 1, 0], ![22, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![13, 1, 0], ![3, 18, 11], ![-129, -2, 9]]]
  hmulB := by decide  
  f := ![![![-474, -3235, -1980], ![-215, 7740, 0]], ![![-149, -971, -594], ![-42, 2322, 0]], ![![-254, -1656, -1013], ![-72, 3960, 0]]]
  g := ![![![1, 0, 0], ![-13, 43, 0], ![-22, 0, 43]], ![![0, 1, 0], ![-11, 18, 11], ![-7, -2, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1

def I43N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-20, 1, 0]] i)))

def SI43N2: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-20, 1, 0]] 
 ![![43, 0, 0], ![23, 1, 0], ![16, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-20, 1, 0], ![3, -15, 11], ![-129, -2, -24]]]
  hmulB := by decide  
  f := ![![![186, -1123, 825], ![-86, -3225, 0]], ![![101, -599, 440], ![-42, -1720, 0]], ![![72, -418, 307], ![-26, -1200, 0]]]
  g := ![![![1, 0, 0], ![-23, 43, 0], ![-16, 0, 43]], ![![-1, 1, 0], ![4, -15, 11], ![7, -2, -24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N2 : Nat.card (O ⧸ I43N2) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N2)

lemma isPrimeI43N2 : Ideal.IsPrime I43N2 := prime_ideal_of_norm_prime hp43.out _ NI43N2
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![31, 0, -2]] ![![43, 0, 0], ![13, 1, 0]]
  ![![43, 0, 0], ![-20, 10, 1]] where
 M := ![![![1333, 0, -86], ![661, 35, -18]]]
 hmul := by decide  
 g := ![![![![31, 0, -2], ![0, 0, 0]], ![![27, -5, -1], ![25, 0, 0]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-20, 10, 1]] ![![43, 0, 0], ![-20, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-860, 43, 0]], ![![-860, 430, 43], ![301, -172, 86]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-20, 1, 0]]], ![![![-20, 10, 1]], ![![7, -4, 2]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0]] 
 ![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [27, 16, 43, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 13, 18], [18, 33, 29], [0, 1]]
 g := ![![[4, 12, 8], [12, 41, 3], [1, 46, 9], [0, 4, 1], []], ![[13, 43, 21, 37], [38, 20, 10, 32], [15, 40, 29, 7], [44, 26, 23, 3], [25, 42]], ![[1, 8, 33, 38], [5, 45, 38, 20], [9, 12, 18, 46], [1, 30, 25, 13], [14, 42]]]
 h' := ![![[33, 13, 18], [5, 41, 33], [20, 11, 12], [0, 33, 3], [0, 0, 1], [0, 1]], ![[18, 33, 29], [27, 33, 41], [40, 21, 30], [28, 46, 35], [38, 29, 33], [33, 13, 18]], ![[0, 1], [42, 20, 20], [40, 15, 5], [9, 15, 9], [40, 18, 13], [18, 33, 29]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36, 33], []]
 b := ![[], [19, 17, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [27, 16, 43, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![26724717, -256855, 325381]
  a := ![7, 9, 26]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![568611, -5465, 6923]
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


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [39, 8, 35, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 48, 16], [17, 4, 37], [0, 1]]
 g := ![![[19, 37, 13], [14, 25], [23, 10, 24], [32, 6], [1]], ![[46, 34, 25, 49], [35, 7], [22, 36, 0, 24], [24, 9], [47, 22, 34, 15]], ![[21, 8, 10, 16], [14, 40], [44, 50, 45, 36], [48, 13], [20, 39, 46, 38]]]
 h' := ![![[1, 48, 16], [0, 27, 15], [4, 20, 5], [8, 28, 36], [14, 45, 18], [0, 1]], ![[17, 4, 37], [50, 1, 15], [14, 16, 22], [17, 38, 9], [23, 23, 50], [1, 48, 16]], ![[0, 1], [21, 25, 23], [39, 17, 26], [37, 40, 8], [52, 38, 38], [17, 4, 37]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 42], []]
 b := ![[], [13, 8, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [39, 8, 35, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-140520857131, 4005629389, 6381917673]
  a := ![-131, -260, -459]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2651336927, 75577913, 120413541]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![9, 23, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![9, 23, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![9, 23, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![9, 23, 1], ![-60, 122, 249], ![-2862, -57, -82]]]
  hmulB := by decide  
  f := ![![![-8, -23, -1], ![59, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-9, -23, 59]], ![![0, 0, 1], ![-39, -95, 249], ![-36, 31, -82]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [13, 53, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 58], [0, 1]]
 g := ![![[54, 35], [21, 4], [21], [58, 57], [6, 1]], ![[28, 24], [45, 55], [21], [46, 2], [12, 58]]]
 h' := ![![[6, 58], [22, 34], [14, 2], [13, 27], [40, 23], [0, 1]], ![[0, 1], [49, 25], [26, 57], [57, 32], [1, 36], [6, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [7, 37]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [13, 53, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3891, -8366, -1318]
  a := ![-7, -10, -26]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![267, 372, -1318]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-13, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-13, 1, 0]] 
 ![![59, 0, 0], ![46, 1, 0], ![23, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-13, 1, 0], ![3, -8, 11], ![-129, -2, -17]]]
  hmulB := by decide  
  f := ![![![-676, 1940, -2673], ![236, 14337, 0]], ![![-527, 1509, -2079], ![178, 11151, 0]], ![![-260, 756, -1042], ![108, 5589, 0]]]
  g := ![![![1, 0, 0], ![-46, 59, 0], ![-23, 0, 59]], ![![-1, 1, 0], ![2, -8, 11], ![6, -2, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![9, 23, 1]] ![![59, 0, 0], ![-13, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-767, 59, 0]], ![![531, 1357, 59], ![-177, -177, 236]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-13, 1, 0]]], ![![![9, 23, 1]], ![![-3, -3, 4]]]]
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


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [12, 19, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 9, 49], [53, 51, 12], [0, 1]]
 g := ![![[20, 49, 56], [15, 16], [49, 37, 4], [45, 27, 16], [1]], ![[24, 1, 5, 34], [42, 36], [18, 48, 25, 52], [31, 44, 21, 42], [14, 34, 3, 41]], ![[11, 35, 55, 41], [37, 4], [41, 17, 22, 5], [42, 11, 55, 42], [59, 40, 53, 20]]]
 h' := ![![[4, 9, 49], [60, 49, 42], [22, 48, 4], [9, 2, 59], [49, 42, 57], [0, 1]], ![[53, 51, 12], [58, 58, 29], [47, 15, 55], [9, 13, 57], [18, 2, 24], [4, 9, 49]], ![[0, 1], [40, 15, 51], [22, 59, 2], [45, 46, 6], [0, 17, 41], [53, 51, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44, 56], []]
 b := ![[], [36, 39, 25], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [12, 19, 4, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1957185, 42090, 77165]
  a := ![-3, -6, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-32085, 690, 1265]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-23, 5, 5]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![-23, 5, 5]] 
 ![![67, 0, 0], ![0, 1, 0], ![49, 0, 1]] where
  M :=![![![-23, 5, 5], ![-630, -8, 35], ![-120, -65, -38]]]
  hmulB := by decide  
  f := ![![![-2579, 135, -215]], ![![420, -22, 35]], ![![-2483, 130, -207]]]
  g := ![![![-4, 5, 5], ![-35, -8, 35], ![26, -65, -38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N0 : Nat.card (O ⧸ I67N0) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N0)

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := prime_ideal_of_norm_prime hp67.out _ NI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2579, 135, -215]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![-2579, 135, -215]] 
 ![![67, 0, 0], ![0, 67, 0], ![55, 43, 1]] where
  M :=![![![-2579, 135, -215], ![28140, -1474, 2345], ![-39990, 2095, -3334]]]
  hmulB := by decide  
  f := ![![![-23, 5, 5]], ![![-630, -8, 35]], ![![-425, -2, 26]]]
  g := ![![![138, 140, -215], ![-1505, -1527, 2345], ![2140, 2171, -3334]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P1 : CertificateIrreducibleZModOfList' 67 2 2 6 [5, 36, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 66], [0, 1]]
 g := ![![[34, 6], [48, 19], [24], [1], [23], [1]], ![[19, 61], [34, 48], [24], [1], [23], [1]]]
 h' := ![![[31, 66], [28, 26], [24, 32], [55, 52], [44, 1], [62, 31], [0, 1]], ![[0, 1], [30, 41], [11, 35], [59, 15], [8, 66], [18, 36], [31, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [55, 44]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N1 : CertifiedPrimeIdeal' SI67N1 67 where
  n := 2
  hpos := by decide
  P := [5, 36, 1]
  hirr := P67P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-93450, -372, 5744]
  a := ![5, 28, 18]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-6110, -3692, 5744]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N1 B_one_repr
lemma NI67N1 : Nat.card (O ⧸ I67N1) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![-23, 5, 5]] ![![-2579, 135, -215]]
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
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-24, 16, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-24, 16, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![47, 16, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-24, 16, 1], ![-81, 54, 172], ![-1959, -43, -87]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-47, -16, 71]], ![![-1, 0, 1], ![-115, -38, 172], ![30, 19, -87]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [48, 35, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [36, 70], [0, 1]]
 g := ![![[17, 37], [55, 32], [36, 5], [30], [18], [1]], ![[0, 34], [0, 39], [3, 66], [30], [18], [1]]]
 h' := ![![[36, 70], [58, 26], [47, 48], [25, 17], [20, 32], [23, 36], [0, 1]], ![[0, 1], [0, 45], [0, 23], [69, 54], [36, 39], [41, 35], [36, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [61, 40]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [48, 35, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6162, -3966, -594]
  a := ![-5, -6, -18]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![480, 78, -594]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-30, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-30, 1, 0]] 
 ![![71, 0, 0], ![41, 1, 0], ![16, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-30, 1, 0], ![3, -25, 11], ![-129, -2, -34]]]
  hmulB := by decide  
  f := ![![![3229, -33125, 14586], ![-1775, -94146, 0]], ![![1876, -19111, 8415], ![-993, -54315, 0]], ![![734, -7465, 3287], ![-385, -21216, 0]]]
  g := ![![![1, 0, 0], ![-41, 71, 0], ![-16, 0, 71]], ![![-1, 1, 0], ![12, -25, 11], ![7, -2, -34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![-24, 16, 1]] ![![71, 0, 0], ![-30, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-2130, 71, 0]], ![![-1704, 1136, 71], ![639, -426, 142]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-30, 1, 0]]], ![![![-24, 16, 1]], ![![9, -6, 2]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![533, 19, -21]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![533, 19, -21]] 
 ![![73, 0, 0], ![0, 73, 0], ![65, 13, 1]] where
  M :=![![![533, 19, -21], ![2766, 670, 293], ![-4656, 193, 436]]]
  hmulB := by decide  
  f := ![![![3227, -169, 269]], ![![-35208, 1844, -2935]], ![![-2711, 142, -226]]]
  g := ![![![26, 4, -21], ![-223, -43, 293], ![-452, -75, 436]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [41, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [62, 72], [0, 1]]
 g := ![![[43, 57], [9], [67], [2, 8], [48], [1]], ![[0, 16], [9], [67], [60, 65], [48], [1]]]
 h' := ![![[62, 72], [53, 38], [35, 3], [64, 40], [5, 9], [32, 62], [0, 1]], ![[0, 1], [0, 35], [2, 70], [62, 33], [52, 64], [7, 11], [62, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [68]]
 b := ![[], [41, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [41, 11, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11110, -5434, 385]
  a := ![6, 11, 22]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-495, -143, 385]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3227, -169, 269]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![3227, -169, 269]] 
 ![![73, 0, 0], ![7, 1, 0], ![59, 0, 1]] where
  M :=![![![3227, -169, 269], ![-35208, 1844, -2935], ![50046, -2621, 4172]]]
  hmulB := by decide  
  f := ![![![533, 19, -21]], ![![89, 11, 2]], ![![367, 18, -11]]]
  g := ![![![-157, -169, 269], ![1713, 1844, -2935], ![-2435, -2621, 4172]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![533, 19, -21]] ![![3227, -169, 269]]
  ![![73, 0, 0]] where
 M := ![![![73, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-499, -249, -143]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![-499, -249, -143]] 
 ![![79, 0, 0], ![0, 79, 0], ![51, 15, 1]] where
  M :=![![![-499, -249, -143], ![17700, -1458, -2167], ![17106, 2071, 354]]]
  hmulB := by decide  
  f := ![![![-50275, 2633, -4191]], ![![548538, -28728, 45727]], ![![61827, -3238, 5154]]]
  g := ![![![86, 24, -143], ![1623, 393, -2167], ![-12, -41, 354]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [9, 67, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 78], [0, 1]]
 g := ![![[25, 44], [61, 2], [50, 49], [2, 42], [65], [1]], ![[0, 35], [6, 77], [6, 30], [32, 37], [65], [1]]]
 h' := ![![[12, 78], [4, 26], [24, 9], [61, 72], [49, 11], [70, 12], [0, 1]], ![[0, 1], [0, 53], [53, 70], [56, 7], [23, 68], [56, 67], [12, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38]]
 b := ![[], [44, 19]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [9, 67, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-51336, -15215, -1620]
  a := ![-10, -20, -35]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![396, 115, -1620]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![50275, -2633, 4191]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![50275, -2633, 4191]] 
 ![![79, 0, 0], ![76, 1, 0], ![8, 0, 1]] where
  M :=![![![50275, -2633, 4191], ![-548538, 28728, -45727], ![779712, -40835, 64998]]]
  hmulB := by decide  
  f := ![![![499, 249, 143]], ![![256, 258, 165]], ![![-166, -1, 10]]]
  g := ![![![2745, -2633, 4191], ![-29950, 28728, -45727], ![42572, -40835, 64998]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![-499, -249, -143]] ![![50275, -2633, 4191]]
  ![![79, 0, 0]] where
 M := ![![![-79, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


lemma PB189I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB189I1 : PrimesBelowBoundCertificateInterval O 31 79 189 where
  m := 11
  g := ![3, 1, 3, 1, 1, 2, 1, 2, 2, 2, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB189I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1, I37N1]
    · exact ![I41N0]
    · exact ![I43N0, I43N1, I43N2]
    · exact ![I47N0]
    · exact ![I53N0]
    · exact ![I59N0, I59N1]
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
    · exact ![37, 37, 37]
    · exact ![68921]
    · exact ![43, 43, 43]
    · exact ![103823]
    · exact ![148877]
    · exact ![3481, 59]
    · exact ![226981]
    · exact ![67, 4489]
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
      exact NI37N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
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
  β := ![I37N0, I37N1, I43N0, I43N1, I43N2, I59N1, I67N0, I71N1, I73N1, I79N1]
  Il := ![[I37N0, I37N1, I37N1], [], [I43N0, I43N1, I43N2], [], [], [I59N1], [], [I67N0], [I71N1], [I73N1], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
