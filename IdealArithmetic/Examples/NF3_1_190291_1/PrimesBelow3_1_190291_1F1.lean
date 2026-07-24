
import IdealArithmetic.Examples.NF3_1_190291_1.RI3_1_190291_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![0, 1, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![0, 1, 0]] 
 ![![37, 0, 0], ![0, 1, 0], ![28, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![0, 1, 0], ![2, 1, 8], ![83, -5, -1]]]
  hmulB := by decide  
  f := ![![![-37, -19, -152], ![0, 703, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-28, -15, -115], ![23, 532, 0]]]
  g := ![![![1, 0, 0], ![0, 37, 0], ![-28, 0, 37]], ![![0, 1, 0], ![-6, 1, 8], ![3, -5, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![0, 1, 0]] ![![37, 0, 0], ![0, 1, 0]]
  ![![37, 0, 0], ![-9, 14, 1]] where
 M := ![![![1369, 0, 0], ![0, 37, 0]], ![![0, 37, 0], ![2, 1, 8]]]
 hmul := by decide  
 g := ![![![![37, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]]], ![![![0, 1, 0], ![0, 0, 0]], ![![2, -3, 0], ![8, 0, 0]]]]
 hle2 := by decide  
def MulI37N1 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![-9, 14, 1]] ![![37, 0, 0], ![0, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![0, 37, 0]], ![![-333, 518, 37], ![111, 0, 111]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![0, 1, 0]]], ![![![-9, 14, 1]], ![![3, 0, 3]]]]
 hle2 := by decide  

def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N0, I37N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N0
    exact isPrimeI37N0
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


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [17, 33, 12, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 35, 36], [9, 5, 5], [0, 1]]
 g := ![![[35, 36, 18], [2, 16], [2, 18], [29, 29, 1], []], ![[40, 32, 19, 16], [28, 40], [9, 10], [17, 18, 15, 39], [6, 25]], ![[15, 40, 27, 4], [29, 25], [27, 20], [17, 7, 32, 16], [37, 25]]]
 h' := ![![[20, 35, 36], [30, 12, 31], [8, 27, 37], [40, 26, 31], [0, 0, 1], [0, 1]], ![[9, 5, 5], [37, 30, 13], [12, 10, 9], [40, 28, 25], [11, 39, 5], [20, 35, 36]], ![[0, 1], [1, 40, 38], [24, 4, 36], [14, 28, 26], [26, 2, 35], [9, 5, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 2], []]
 b := ![[], [9, 14, 25], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [17, 33, 12, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1417657, 170396, -62976]
  a := ![-3, -2, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-34577, 4156, -1536]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-4, 4, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-4, 4, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![39, 4, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-4, 4, 1], ![91, -5, 31], ![310, -9, -13]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-39, -4, 43]], ![![-1, 0, 1], ![-26, -3, 31], ![19, 1, -13]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [3, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 42], [0, 1]]
 g := ![![[4, 16], [42, 35], [40], [21, 15], [1]], ![[27, 27], [9, 8], [40], [13, 28], [1]]]
 h' := ![![[31, 42], [3, 4], [22, 32], [23, 13], [40, 31], [0, 1]], ![[0, 1], [41, 39], [25, 11], [39, 30], [12, 12], [31, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [39, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [3, 12, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1751, 891, -261]
  a := ![2, 0, 9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![196, 45, -261]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![12, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![12, 1, 0]] 
 ![![43, 0, 0], ![12, 1, 0], ![13, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![12, 1, 0], ![2, 13, 8], ![83, -5, 11]]]
  hmulB := by decide  
  f := ![![![-479, -3505, -2160], ![-215, 11610, 0]], ![![-138, -974, -600], ![-42, 3225, 0]], ![![-149, -1060, -653], ![-50, 3510, 0]]]
  g := ![![![1, 0, 0], ![-12, 43, 0], ![-13, 0, 43]], ![![0, 1, 0], ![-6, 13, 8], ![0, -5, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-4, 4, 1]] ![![43, 0, 0], ![12, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![516, 43, 0]], ![![-172, 172, 43], ![43, 43, 43]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![12, 1, 0]]], ![![![-4, 4, 1]], ![![1, 1, 1]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0]] 
 ![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [44, 41, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 6, 41], [44, 40, 6], [0, 1]]
 g := ![![[0, 22, 32], [3, 41, 36], [3, 19, 28], [15, 44, 1], []], ![[46, 7, 37, 22], [39, 30, 24, 41], [4, 12, 0, 43], [5, 16, 39, 35], [8, 36]], ![[27, 25, 23, 2], [15, 32, 6, 12], [7, 39, 0, 34], [3, 28, 41, 28], [43, 36]]]
 h' := ![![[0, 6, 41], [9, 34, 28], [9, 32, 6], [45, 34, 34], [0, 0, 1], [0, 1]], ![[44, 40, 6], [23, 13, 23], [12, 0, 1], [15, 9, 28], [24, 15, 40], [0, 6, 41]], ![[0, 1], [11, 0, 43], [36, 15, 40], [29, 4, 32], [44, 32, 6], [44, 40, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31, 25], []]
 b := ![[], [24, 12, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [44, 41, 3, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-78834713275, 8400910848, -2313012504]
  a := ![-129, -64, -452]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1677334325, 178742784, -49213032]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-12, -11, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-12, -11, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![41, 42, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-12, -11, 1], ![61, -28, -89], ![-935, 66, -6]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-41, -42, 53]], ![![-1, -1, 1], ![70, 70, -89], ![-13, 6, -6]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [51, 43, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [10, 52], [0, 1]]
 g := ![![[5, 28], [15], [], [16], [10, 1]], ![[20, 25], [15], [], [16], [20, 52]]]
 h' := ![![[10, 52], [30, 44], [0, 11], [8], [20, 49], [0, 1]], ![[0, 1], [46, 9], [4, 42], [8], [33, 4], [10, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51]]
 b := ![[], [5, 52]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [51, 43, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1627, 1693, -1344]
  a := ![-3, -1, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1009, 1097, -1344]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-17, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-17, 1, 0]] 
 ![![53, 0, 0], ![36, 1, 0], ![6, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-17, 1, 0], ![2, -16, 8], ![83, -5, -18]]]
  hmulB := by decide  
  f := ![![![1896, -17455, 8736], ![-901, -57876, 0]], ![![1296, -11845, 5928], ![-582, -39273, 0]], ![![214, -1976, 989], ![-104, -6552, 0]]]
  g := ![![![1, 0, 0], ![-36, 53, 0], ![-6, 0, 53]], ![![-1, 1, 0], ![10, -16, 8], ![7, -5, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![-12, -11, 1]] ![![53, 0, 0], ![-17, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-901, 53, 0]], ![![-636, -583, 53], ![265, 159, -106]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-17, 1, 0]]], ![![![-12, -11, 1]], ![![5, 3, -2]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![22, 24, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![22, 24, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![22, 24, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![22, 24, 1], ![131, 41, 191], ![1970, -109, -7]]]
  hmulB := by decide  
  f := ![![![-21, -24, -1], ![59, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-22, -24, 59]], ![![0, 0, 1], ![-69, -77, 191], ![36, 1, -7]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [51, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [58, 58], [0, 1]]
 g := ![![[22, 22], [38, 53], [49], [11, 22], [58, 1]], ![[0, 37], [44, 6], [49], [48, 37], [57, 58]]]
 h' := ![![[58, 58], [9, 9], [53, 17], [29, 52], [51, 9], [0, 1]], ![[0, 1], [0, 50], [36, 42], [36, 7], [42, 50], [58, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41]]
 b := ![[], [25, 50]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [51, 1, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![881, 1358, -676]
  a := ![-3, -2, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![267, 298, -676]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-14, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-14, 1, 0]] 
 ![![59, 0, 0], ![45, 1, 0], ![7, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-14, 1, 0], ![2, -13, 8], ![83, -5, -15]]]
  hmulB := by decide  
  f := ![![![-1693, 12001, -7392], ![649, 54516, 0]], ![![-1295, 9144, -5632], ![473, 41536, 0]], ![![-189, 1423, -877], ![127, 6468, 0]]]
  g := ![![![1, 0, 0], ![-45, 59, 0], ![-7, 0, 59]], ![![-1, 1, 0], ![9, -13, 8], ![7, -5, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![22, 24, 1]] ![![59, 0, 0], ![-14, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-826, 59, 0]], ![![1298, 1416, 59], ![-177, -295, 177]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-14, 1, 0]]], ![![![22, 24, 1]], ![![-3, -5, 3]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![8, 30, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![8, 30, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![8, 30, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![8, 30, 1], ![143, 33, 239], ![2468, -139, -27]]]
  hmulB := by decide  
  f := ![![![-7, -30, -1], ![61, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-8, -30, 61]], ![![0, 0, 1], ![-29, -117, 239], ![44, 11, -27]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [53, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [51, 60], [0, 1]]
 g := ![![[14, 14], [14], [6, 45], [36, 13], [51, 1]], ![[57, 47], [14], [44, 16], [28, 48], [41, 60]]]
 h' := ![![[51, 60], [37, 40], [48, 40], [44, 44], [42, 47], [0, 1]], ![[0, 1], [3, 21], [14, 21], [31, 17], [60, 14], [51, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [60, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [53, 10, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![136738, 73598, -36603]
  a := ![23, 21, 91]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![7042, 19208, -36603]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![5, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![5, 1, 0]] 
 ![![61, 0, 0], ![5, 1, 0], ![27, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![5, 1, 0], ![2, 6, 8], ![83, -5, 4]]]
  hmulB := by decide  
  f := ![![![5718, 17333, 23128], ![793, -176351, 0]], ![![467, 1415, 1888], ![62, -14396, 0]], ![![2531, 7672, 10237], ![350, -78057, 0]]]
  g := ![![![1, 0, 0], ![-5, 61, 0], ![-27, 0, 61]], ![![0, 1, 0], ![-4, 6, 8], ![0, -5, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![8, 30, 1]] ![![61, 0, 0], ![5, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![305, 61, 0]], ![![488, 1830, 61], ![183, 183, 244]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![5, 1, 0]]], ![![![8, 30, 1]], ![![3, 3, 4]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![3, 1, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![3, 1, 0]] 
 ![![67, 0, 0], ![3, 1, 0], ![49, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![3, 1, 0], ![2, 4, 8], ![83, -5, 2]]]
  hmulB := by decide  
  f := ![![![628, 1259, 2520], ![67, -21105, 0]], ![![25, 55, 112], ![68, -938, 0]], ![![457, 920, 1843], ![100, -15435, 0]]]
  g := ![![![1, 0, 0], ![-3, 67, 0], ![-49, 0, 67]], ![![0, 1, 0], ![-6, 4, 8], ![0, -5, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N0 : Nat.card (O ⧸ I67N0) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N0)

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := prime_ideal_of_norm_prime hp67.out _ NI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![8, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![8, 1, 0]] 
 ![![67, 0, 0], ![8, 1, 0], ![8, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![8, 1, 0], ![2, 9, 8], ![83, -5, 7]]]
  hmulB := by decide  
  f := ![![![2053, 9444, 8400], ![402, -70350, 0]], ![![242, 1124, 1000], ![68, -8375, 0]], ![![240, 1127, 1003], ![91, -8400, 0]]]
  g := ![![![1, 0, 0], ![-8, 67, 0], ![-8, 0, 67]], ![![0, 1, 0], ![-2, 9, 8], ![1, -5, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1

def I67N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-11, 1, 0]] i)))

def SI67N2: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-11, 1, 0]] 
 ![![67, 0, 0], ![56, 1, 0], ![20, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-11, 1, 0], ![2, -10, 8], ![83, -5, -12]]]
  hmulB := by decide  
  f := ![![![-734, 3837, -3072], ![201, 25728, 0]], ![![-606, 3197, -2560], ![202, 21440, 0]], ![![-215, 1145, -917], ![85, 7680, 0]]]
  g := ![![![1, 0, 0], ![-56, 67, 0], ![-20, 0, 67]], ![![-1, 1, 0], ![6, -10, 8], ![9, -5, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N2 : Nat.card (O ⧸ I67N2) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N2)

lemma isPrimeI67N2 : Ideal.IsPrime I67N2 := prime_ideal_of_norm_prime hp67.out _ NI67N2
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![3, 1, 0]] ![![67, 0, 0], ![8, 1, 0]]
  ![![67, 0, 0], ![20, -32, 1]] where
 M := ![![![4489, 0, 0], ![536, 67, 0]], ![![201, 67, 0], ![26, 12, 8]]]
 hmul := by decide  
 g := ![![![![47, 32, -1], ![67, 0, 0]], ![![-12, 33, -1], ![67, 0, 0]]], ![![![-17, 33, -1], ![67, 0, 0]], ![![-2, 4, 0], ![8, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![20, -32, 1]] ![![67, 0, 0], ![-11, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-737, 67, 0]], ![![1340, -2144, 67], ![-201, 335, -268]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-11, 1, 0]]], ![![![20, -32, 1]], ![![-3, 5, -4]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![29, 1, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![29, 1, 0]] 
 ![![71, 0, 0], ![29, 1, 0], ![69, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![29, 1, 0], ![2, 30, 8], ![83, -5, 28]]]
  hmulB := by decide  
  f := ![![![-3619, -69056, -18424], ![-2414, 163513, 0]], ![![-1474, -28186, -7520], ![-993, 66740, 0]], ![![-3524, -67111, -17905], ![-2329, 158907, 0]]]
  g := ![![![1, 0, 0], ![-29, 71, 0], ![-69, 0, 71]], ![![0, 1, 0], ![-20, 30, 8], ![-24, -5, 28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N0 : Nat.card (O ⧸ I71N0) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N0)

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := prime_ideal_of_norm_prime hp71.out _ NI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-21, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-21, 1, 0]] 
 ![![71, 0, 0], ![50, 1, 0], ![1, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-21, 1, 0], ![2, -20, 8], ![83, -5, -22]]]
  hmulB := by decide  
  f := ![![![2245, -25366, 10152], ![-994, -90099, 0]], ![![1577, -17850, 7144], ![-709, -63403, 0]], ![![47, -358, 143], ![38, -1269, 0]]]
  g := ![![![1, 0, 0], ![-50, 71, 0], ![-1, 0, 71]], ![![-1, 1, 0], ![14, -20, 8], ![5, -5, -22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-8, 1, 0]] i)))

def SI71N2: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-8, 1, 0]] 
 ![![71, 0, 0], ![63, 1, 0], ![11, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-8, 1, 0], ![2, -7, 8], ![83, -5, -9]]]
  hmulB := by decide  
  f := ![![![1589, -5639, 6448], ![-213, -57226, 0]], ![![1407, -5002, 5720], ![-212, -50765, 0]], ![![249, -874, 999], ![-8, -8866, 0]]]
  g := ![![![1, 0, 0], ![-63, 71, 0], ![-11, 0, 71]], ![![-1, 1, 0], ![5, -7, 8], ![7, -5, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![29, 1, 0]] ![![71, 0, 0], ![-21, 1, 0]]
  ![![71, 0, 0], ![4, 10, 1]] where
 M := ![![![5041, 0, 0], ![-1491, 71, 0]], ![![2059, 71, 0], ![-607, 9, 8]]]
 hmul := by decide  
 g := ![![![![67, -10, -1], ![71, 0, 0]], ![![-21, 1, 0], ![0, 0, 0]]], ![![![25, -9, -1], ![71, 0, 0]], ![![-9, -1, 0], ![8, 0, 0]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![4, 10, 1]] ![![71, 0, 0], ![-8, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-568, 71, 0]], ![![284, 710, 71], ![71, -71, 71]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-8, 1, 0]]], ![![![4, 10, 1]], ![![1, -1, 1]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![152, 14, 13]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![152, 14, 13]] 
 ![![73, 0, 0], ![0, 73, 0], ![51, 46, 1]] where
  M :=![![![152, 14, 13], ![1107, 101, 99], ![876, 73, 73]]]
  hmulB := by decide  
  f := ![![![2, -1, 1]], ![![81, -4, -9]], ![![51, -3, -5]]]
  g := ![![![-7, -8, 13], ![-54, -61, 99], ![-39, -45, 73]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [12, 47, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [26, 72], [0, 1]]
 g := ![![[10, 67], [27], [71], [26, 37], [19], [1]], ![[0, 6], [27], [71], [39, 36], [19], [1]]]
 h' := ![![[26, 72], [18, 33], [59, 63], [53, 61], [62, 16], [61, 26], [0, 1]], ![[0, 1], [0, 40], [18, 10], [33, 12], [40, 57], [7, 47], [26, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53]]
 b := ![[], [57, 63]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [12, 47, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-728, 175, -166]
  a := ![-1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![106, 107, -166]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2, 1, -1]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-2, 1, -1]] 
 ![![73, 0, 0], ![71, 1, 0], ![0, 0, 1]] where
  M :=![![![-2, 1, -1], ![-81, 4, 9], ![105, -16, 2]]]
  hmulB := by decide  
  f := ![![![-152, -14, -13]], ![![-163, -15, -14]], ![![-12, -1, -1]]]
  g := ![![![-1, 1, -1], ![-5, 4, 9], ![17, -16, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![152, 14, 13]] ![![-2, 1, -1]]
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


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [43, 64, 27, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [56, 27, 21], [75, 51, 58], [0, 1]]
 g := ![![[63, 62, 19], [74, 4, 5], [53, 48, 22], [73, 42, 62], [52, 1], []], ![[66, 71, 15, 20], [54, 18, 33, 64], [28, 13, 67, 32], [26, 4, 71, 65], [74, 73], [50, 46]], ![[1, 50, 21, 57], [65, 25, 30, 28], [77, 3, 1, 33], [24, 65, 46, 35], [16, 18], [13, 46]]]
 h' := ![![[56, 27, 21], [57, 55, 16], [12, 41, 20], [21, 23, 38], [55, 26, 33], [0, 0, 1], [0, 1]], ![[75, 51, 58], [32, 43, 75], [66, 55, 64], [67, 60, 51], [0, 9, 17], [38, 58, 51], [56, 27, 21]], ![[0, 1], [76, 60, 67], [48, 62, 74], [72, 75, 69], [44, 44, 29], [10, 21, 27], [75, 51, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23, 55], []]
 b := ![[], [67, 9, 35], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [43, 64, 27, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6787601, -624574, 171904]
  a := ![5, 3, 20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![85919, -7906, 2176]
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



lemma PB124I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB124I1 : PrimesBelowBoundCertificateInterval O 31 79 124 where
  m := 11
  g := ![3, 1, 2, 1, 2, 2, 2, 3, 3, 2, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB124I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N0, I37N0]
    · exact ![I41N0]
    · exact ![I43N0, I43N1]
    · exact ![I47N0]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1, I67N2]
    · exact ![I71N0, I71N1, I71N2]
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
    · exact ![37, 37, 37]
    · exact ![68921]
    · exact ![1849, 43]
    · exact ![103823]
    · exact ![2809, 53]
    · exact ![3481, 59]
    · exact ![3721, 61]
    · exact ![67, 67, 67]
    · exact ![71, 71, 71]
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
      exact NI37N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
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
  β := ![I37N0, I43N1, I53N1, I59N1, I61N1, I67N0, I67N1, I67N2, I71N0, I71N1, I71N2, I73N1]
  Il := ![[I37N0, I37N0, I37N0], [], [I43N1], [], [I53N1], [I59N1], [I61N1], [I67N0, I67N1, I67N2], [I71N0, I71N1, I71N2], [I73N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
