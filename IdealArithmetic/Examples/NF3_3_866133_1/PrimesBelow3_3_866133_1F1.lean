
import IdealArithmetic.Examples.NF3_3_866133_1.RI3_3_866133_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![57, 6, -2]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![57, 6, -2]] 
 ![![37, 0, 0], ![23, 1, 0], ![22, 0, 1]] where
  M :=![![![57, 6, -2], ![-686, -75, 22], ![1682, 172, -63]]]
  hmulB := by decide  
  f := ![![![941, 34, -18]], ![![417, 15, -8]], ![![780, 28, -15]]]
  g := ![![![-1, 6, -2], ![15, -75, 22], ![-24, 172, -63]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![32, 3, -1]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![32, 3, -1]] 
 ![![37, 0, 0], ![28, 1, 0], ![15, 0, 1]] where
  M :=![![![32, 3, -1], ![-343, -34, 11], ![841, 86, -28]]]
  hmulB := by decide  
  f := ![![![6, -2, -1]], ![![-5, -3, -1]], ![![-22, -7, -2]]]
  g := ![![![-1, 3, -1], ![12, -34, 11], ![-31, 86, -28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![57, 6, -2]] ![![57, 6, -2]]
  ![![-4231, -452, 144]] where
 M := ![![![-4231, -452, 144]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI37N1 : IdealMulLeCertificate' Table 
  ![![-4231, -452, 144]] ![![32, 3, -1]]
  ![![37, 0, 0]] where
 M := ![![![140748, 15059, -4773]]]
 hmul := by decide  
 g := ![![![![3804, 407, -129]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N0, I37N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N0
    exact isPrimeI37N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0 ⊙ MulI37N1)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![0, 1, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![0, 1, 0]] 
 ![![41, 0, 0], ![0, 1, 0], ![21, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![0, 1, 0], ![2, -1, 4], ![349, 63, 1]]]
  hmulB := by decide  
  f := ![![![-41, 20, -84], ![41, 861, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-21, 10, -43], ![31, 441, 0]]]
  g := ![![![1, 0, 0], ![0, 41, 0], ![-21, 0, 41]], ![![0, 1, 0], ![-2, -1, 4], ![8, 63, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N0)

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := prime_ideal_of_norm_prime hp41.out _ NI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![3, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![3, 1, 0]] 
 ![![41, 0, 0], ![3, 1, 0], ![40, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![3, 1, 0], ![2, 2, 4], ![349, 63, 4]]]
  hmulB := by decide  
  f := ![![![-836, -839, -1680], ![-41, 17220, 0]], ![![-60, -60, -120], ![1, 1230, 0]], ![![-814, -818, -1639], ![-62, 16800, 0]]]
  g := ![![![1, 0, 0], ![-3, 41, 0], ![-40, 0, 41]], ![![0, 1, 0], ![-4, 2, 4], ![0, 63, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-3, 1, 0]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-3, 1, 0]] 
 ![![41, 0, 0], ![38, 1, 0], ![18, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-3, 1, 0], ![2, -4, 4], ![349, 63, -2]]]
  hmulB := by decide  
  f := ![![![646, -1295, 1296], ![-41, -13284, 0]], ![![598, -1199, 1200], ![-40, -12300, 0]], ![![285, -569, 569], ![1, -5832, 0]]]
  g := ![![![1, 0, 0], ![-38, 41, 0], ![-18, 0, 41]], ![![-1, 1, 0], ![2, -4, 4], ![-49, 63, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![0, 1, 0]] ![![41, 0, 0], ![3, 1, 0]]
  ![![41, 0, 0], ![-61, -20, 1]] where
 M := ![![![1681, 0, 0], ![123, 41, 0]], ![![0, 41, 0], ![2, 2, 4]]]
 hmul := by decide  
 g := ![![![![41, 0, 0], ![0, 0, 0]], ![![3, 1, 0], ![0, 0, 0]]], ![![![0, 1, 0], ![0, 0, 0]], ![![6, 2, 0], ![4, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-61, -20, 1]] ![![41, 0, 0], ![-3, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-123, 41, 0]], ![![-2501, -820, 41], ![492, 82, -82]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-3, 1, 0]]], ![![![-61, -20, 1]], ![![12, 2, -2]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-43, 19, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-43, 19, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![0, 19, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-43, 19, 1], ![387, 1, 77], ![6837, 1300, 39]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![43, -18, -1], ![43, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, -19, 43]], ![![-1, 0, 1], ![9, -34, 77], ![159, 13, 39]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [38, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 42], [0, 1]]
 g := ![![[8, 17], [20, 21], [31], [29, 9], [1]], ![[0, 26], [0, 22], [31], [2, 34], [1]]]
 h' := ![![[40, 42], [14, 19], [24, 8], [16, 26], [5, 40], [0, 1]], ![[0, 1], [0, 24], [0, 35], [24, 17], [14, 3], [40, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31]]
 b := ![[], [34, 37]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [38, 3, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3268, 2948, 2278]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![76, -938, 2278]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![9, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![9, 1, 0]] 
 ![![43, 0, 0], ![9, 1, 0], ![4, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![9, 1, 0], ![2, 8, 4], ![349, 63, 10]]]
  hmulB := by decide  
  f := ![![![-635, -2684, -1344], ![-172, 14448, 0]], ![![-140, -560, -280], ![1, 3010, 0]], ![![-62, -250, -125], ![-2, 1344, 0]]]
  g := ![![![1, 0, 0], ![-9, 43, 0], ![-4, 0, 43]], ![![0, 1, 0], ![-2, 8, 4], ![-6, 63, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-43, 19, 1]] ![![43, 0, 0], ![9, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![387, 43, 0]], ![![-1849, 817, 43], ![0, 172, 86]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![9, 1, 0]]], ![![![-43, 19, 1]], ![![0, 4, 2]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![16, 1, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![16, 1, 0]] 
 ![![47, 0, 0], ![16, 1, 0], ![11, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![16, 1, 0], ![2, 15, 4], ![349, 63, 17]]]
  hmulB := by decide  
  f := ![![![95, 943, 252], ![94, -2961, 0]], ![![26, 314, 84], ![48, -987, 0]], ![![11, 220, 59], ![55, -693, 0]]]
  g := ![![![1, 0, 0], ![-16, 47, 0], ![-11, 0, 47]], ![![0, 1, 0], ![-6, 15, 4], ![-18, 63, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N0 : Nat.card (O ⧸ I47N0) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N0)

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := prime_ideal_of_norm_prime hp47.out _ NI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-12, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-12, 1, 0]] 
 ![![47, 0, 0], ![35, 1, 0], ![32, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-12, 1, 0], ![2, -13, 4], ![349, 63, -11]]]
  hmulB := by decide  
  f := ![![![2193, -15634, 4816], ![-846, -56588, 0]], ![![1625, -11634, 3584], ![-657, -42112, 0]], ![![1488, -10644, 3279], ![-596, -38528, 0]]]
  g := ![![![1, 0, 0], ![-35, 47, 0], ![-32, 0, 47]], ![![-1, 1, 0], ![7, -13, 4], ![-32, 63, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1

def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-4, 1, 0]] i)))

def SI47N2: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-4, 1, 0]] 
 ![![47, 0, 0], ![43, 1, 0], ![19, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-4, 1, 0], ![2, -5, 4], ![349, 63, -3]]]
  hmulB := by decide  
  f := ![![![347, -874, 700], ![-47, -8225, 0]], ![![321, -800, 640], ![1, -7520, 0]], ![![143, -354, 283], ![13, -3325, 0]]]
  g := ![![![1, 0, 0], ![-43, 47, 0], ![-19, 0, 47]], ![![-1, 1, 0], ![3, -5, 4], ![-49, 63, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N2 : Nat.card (O ⧸ I47N2) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N2)

lemma isPrimeI47N2 : Ideal.IsPrime I47N2 := prime_ideal_of_norm_prime hp47.out _ NI47N2
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![16, 1, 0]] ![![47, 0, 0], ![-12, 1, 0]]
  ![![47, 0, 0], ![-24, -11, 1]] where
 M := ![![![2209, 0, 0], ![-564, 47, 0]], ![![752, 47, 0], ![-190, 3, 4]]]
 hmul := by decide  
 g := ![![![![47, 0, 0], ![0, 0, 0]], ![![12, 12, -1], ![47, 0, 0]]], ![![![16, 1, 0], ![0, 0, 0]], ![![-2, 1, 0], ![4, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![-24, -11, 1]] ![![47, 0, 0], ![-4, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![-188, 47, 0]], ![![-1128, -517, 47], ![423, 94, -47]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![-4, 1, 0]]], ![![![-24, -11, 1]], ![![9, 2, -1]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1, I47N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
    exact isPrimeI47N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0 ⊙ MulI47N1)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![21, 1, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![21, 1, 0]] 
 ![![53, 0, 0], ![21, 1, 0], ![28, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![21, 1, 0], ![2, 20, 4], ![349, 63, 22]]]
  hmulB := by decide  
  f := ![![![1747, 22058, 4416], ![1166, -58512, 0]], ![![685, 8731, 1748], ![478, -23161, 0]], ![![917, 11653, 2333], ![631, -30912, 0]]]
  g := ![![![1, 0, 0], ![-21, 53, 0], ![-28, 0, 53]], ![![0, 1, 0], ![-10, 20, 4], ![-30, 63, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N0 : Nat.card (O ⧸ I53N0) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N0)

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := prime_ideal_of_norm_prime hp53.out _ NI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-16, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-16, 1, 0]] 
 ![![53, 0, 0], ![37, 1, 0], ![12, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-16, 1, 0], ![2, -17, 4], ![349, 63, -15]]]
  hmulB := by decide  
  f := ![![![1357, -13146, 3096], ![-636, -41022, 0]], ![![953, -9172, 2160], ![-423, -28620, 0]], ![![316, -2977, 701], ![-115, -9288, 0]]]
  g := ![![![1, 0, 0], ![-37, 53, 0], ![-12, 0, 53]], ![![-1, 1, 0], ![11, -17, 4], ![-34, 63, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1

def I53N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![50, 2, -1]] i)))

def SI53N2: IdealEqSpanCertificate' Table ![![50, 2, -1]] 
 ![![53, 0, 0], ![48, 1, 0], ![46, 0, 1]] where
  M :=![![![50, 2, -1], ![-345, -15, 7], ![492, 23, -11]]]
  hmulB := by decide  
  f := ![![![4, -1, -1]], ![![-3, -2, -1]], ![![-7, -4, -2]]]
  g := ![![![0, 2, -1], ![1, -15, 7], ![-2, 23, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N2 : Nat.card (O ⧸ I53N2) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N2)

lemma isPrimeI53N2 : Ideal.IsPrime I53N2 := prime_ideal_of_norm_prime hp53.out _ NI53N2
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![21, 1, 0]] ![![53, 0, 0], ![-16, 1, 0]]
  ![![4, -1, -1]] where
 M := ![![![2809, 0, 0], ![-848, 53, 0]], ![![1113, 53, 0], ![-334, 4, 4]]]
 hmul := by decide  
 g := ![![![![2650, 106, -53]], ![![-1145, -47, 23]]], ![![![705, 27, -14]], ![![-304, -12, 6]]]]
 hle2 := by decide  

def MulI53N1 : IdealMulLeCertificate' Table 
  ![![4, -1, -1]] ![![50, 2, -1]]
  ![![53, 0, 0]] where
 M := ![![![53, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-66, -4, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-66, -4, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![52, 55, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-66, -4, 1], ![341, 1, -15], ![-1190, -149, -7]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-52, -55, 59]], ![![-2, -1, 1], ![19, 14, -15], ![-14, 4, -7]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [32, 52, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [7, 58], [0, 1]]
 g := ![![[9, 12], [2, 29], [49], [12, 53], [7, 1]], ![[34, 47], [28, 30], [49], [29, 6], [14, 58]]]
 h' := ![![[7, 58], [54, 37], [40, 41], [29, 7], [12, 17], [0, 1]], ![[0, 1], [18, 22], [32, 18], [19, 52], [13, 42], [7, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [38, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [32, 52, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4349, 2218, 3487]
  a := ![3, -3, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3147, -3213, 3487]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![15, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![15, 1, 0]] 
 ![![59, 0, 0], ![15, 1, 0], ![7, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![15, 1, 0], ![2, 14, 4], ![349, 63, 16]]]
  hmulB := by decide  
  f := ![![![66, 559, 160], ![59, -2360, 0]], ![![5, 139, 40], ![60, -590, 0]], ![![3, 66, 19], ![26, -280, 0]]]
  g := ![![![1, 0, 0], ![-15, 59, 0], ![-7, 0, 59]], ![![0, 1, 0], ![-4, 14, 4], ![-12, 63, 16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-66, -4, 1]] ![![59, 0, 0], ![15, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![885, 59, 0]], ![![-3894, -236, 59], ![-649, -59, 0]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![15, 1, 0]]], ![![![-66, -4, 1]], ![![-11, -1, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-57, -32, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-57, -32, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![4, 29, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-57, -32, 1], ![285, 38, -127], ![-10962, -1913, -26]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-4, -29, 61]], ![![-1, -1, 1], ![13, 61, -127], ![-178, -19, -26]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [53, 31, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [30, 60], [0, 1]]
 g := ![![[19, 49], [45], [24, 60], [1, 49], [30, 1]], ![[25, 12], [45], [55, 1], [7, 12], [60, 60]]]
 h' := ![![[30, 60], [14, 7], [9, 44], [8, 11], [57, 54], [0, 1]], ![[0, 1], [41, 54], [48, 17], [33, 50], [30, 7], [30, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50]]
 b := ![[], [52, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [53, 31, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![853533, 440252, 280834]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4423, -126294, 280834]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![5, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![5, 1, 0]] 
 ![![61, 0, 0], ![5, 1, 0], ![26, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![5, 1, 0], ![2, 4, 4], ![349, 63, 6]]]
  hmulB := by decide  
  f := ![![![2328, 4699, 4704], ![305, -71736, 0]], ![![187, 383, 384], ![62, -5856, 0]], ![![993, 2003, 2005], ![121, -30576, 0]]]
  g := ![![![1, 0, 0], ![-5, 61, 0], ![-26, 0, 61]], ![![0, 1, 0], ![-2, 4, 4], ![-2, 63, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-57, -32, 1]] ![![61, 0, 0], ![5, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![305, 61, 0]], ![![-3477, -1952, 61], ![0, -122, -122]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![5, 1, 0]]], ![![![-57, -32, 1]], ![![0, -2, -2]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![8, 1, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![8, 1, 0]] 
 ![![67, 0, 0], ![8, 1, 0], ![20, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![8, 1, 0], ![2, 7, 4], ![349, 63, 9]]]
  hmulB := by decide  
  f := ![![![1641, 5875, 3360], ![335, -56280, 0]], ![![192, 699, 400], ![68, -6700, 0]], ![![484, 1753, 1003], ![149, -16800, 0]]]
  g := ![![![1, 0, 0], ![-8, 67, 0], ![-20, 0, 67]], ![![0, 1, 0], ![-2, 7, 4], ![-5, 63, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N0 : Nat.card (O ⧸ I67N0) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N0)

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := prime_ideal_of_norm_prime hp67.out _ NI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![22, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![22, 1, 0]] 
 ![![67, 0, 0], ![22, 1, 0], ![19, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![22, 1, 0], ![2, 21, 4], ![349, 63, 23]]]
  hmulB := by decide  
  f := ![![![531, 6715, 1280], ![335, -21440, 0]], ![![166, 2203, 420], ![135, -7035, 0]], ![![145, 1904, 363], ![112, -6080, 0]]]
  g := ![![![1, 0, 0], ![-22, 67, 0], ![-19, 0, 67]], ![![0, 1, 0], ![-8, 21, 4], ![-22, 63, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1

def I67N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-30, 1, 0]] i)))

def SI67N2: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-30, 1, 0]] 
 ![![67, 0, 0], ![37, 1, 0], ![36, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-30, 1, 0], ![2, -31, 4], ![349, 63, -29]]]
  hmulB := by decide  
  f := ![![![145, -2696, 348], ![-67, -5829, 0]], ![![97, -1488, 192], ![1, -3216, 0]], ![![90, -1449, 187], ![-9, -3132, 0]]]
  g := ![![![1, 0, 0], ![-37, 67, 0], ![-36, 0, 67]], ![![-1, 1, 0], ![15, -31, 4], ![-14, 63, -29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N2 : Nat.card (O ⧸ I67N2) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N2)

lemma isPrimeI67N2 : Ideal.IsPrime I67N2 := prime_ideal_of_norm_prime hp67.out _ NI67N2
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![8, 1, 0]] ![![67, 0, 0], ![22, 1, 0]]
  ![![67, 0, 0], ![-56, 24, 1]] where
 M := ![![![4489, 0, 0], ![1474, 67, 0]], ![![536, 67, 0], ![178, 29, 4]]]
 hmul := by decide  
 g := ![![![![67, 0, 0], ![0, 0, 0]], ![![22, 1, 0], ![0, 0, 0]]], ![![![8, 1, 0], ![0, 0, 0]], ![![6, -1, 0], ![4, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![-56, 24, 1]] ![![67, 0, 0], ![-30, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-2010, 67, 0]], ![![-3752, 1608, 67], ![2077, -737, 67]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-30, 1, 0]]], ![![![-56, 24, 1]], ![![31, -11, 1]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![14, 1, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![14, 1, 0]] 
 ![![71, 0, 0], ![14, 1, 0], ![26, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![14, 1, 0], ![2, 13, 4], ![349, 63, 15]]]
  hmulB := by decide  
  f := ![![![4237, 29154, 8976], ![1278, -159324, 0]], ![![828, 5742, 1768], ![285, -31382, 0]], ![![1550, 10676, 3287], ![476, -58344, 0]]]
  g := ![![![1, 0, 0], ![-14, 71, 0], ![-26, 0, 71]], ![![0, 1, 0], ![-4, 13, 4], ![-13, 63, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N0 : Nat.card (O ⧸ I71N0) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N0)

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := prime_ideal_of_norm_prime hp71.out _ NI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-52, -2, 1]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![-52, -2, 1]] 
 ![![71, 0, 0], ![19, 1, 0], ![57, 0, 1]] where
  M :=![![![-52, -2, 1], ![345, 13, -7], ![-492, -23, 9]]]
  hmulB := by decide  
  f := ![![![-44, -5, 1]], ![![-7, -1, 0]], ![![-57, -7, 1]]]
  g := ![![![-1, -2, 1], ![7, 13, -7], ![-8, -23, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-33, 1, 0]] i)))

def SI71N2: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-33, 1, 0]] 
 ![![71, 0, 0], ![38, 1, 0], ![4, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-33, 1, 0], ![2, -34, 4], ![349, 63, -32]]]
  hmulB := by decide  
  f := ![![![2656, -61375, 7224], ![-2059, -128226, 0]], ![![1438, -32829, 3864], ![-1064, -68586, 0]], ![![158, -3458, 407], ![-98, -7224, 0]]]
  g := ![![![1, 0, 0], ![-38, 71, 0], ![-4, 0, 71]], ![![-1, 1, 0], ![18, -34, 4], ![-27, 63, -32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![14, 1, 0]] ![![-52, -2, 1]]
  ![![71, 0, 0], ![-75, 8, 1]] where
 M := ![![![-3692, -142, 71]], ![![-383, -15, 7]]]
 hmul := by decide  
 g := ![![![![23, -10, 0], ![71, 0, 0]]], ![![![2, -1, 0], ![7, 0, 0]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![-75, 8, 1]] ![![71, 0, 0], ![-33, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-2343, 71, 0]], ![![-5325, 568, 71], ![2840, -284, 0]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-33, 1, 0]]], ![![![-75, 8, 1]], ![![40, -4, 0]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![4, 1, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![4, 1, 0]] 
 ![![73, 0, 0], ![4, 1, 0], ![34, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![4, 1, 0], ![2, 3, 4], ![349, 63, 5]]]
  hmulB := by decide  
  f := ![![![1643, 2473, 3300], ![146, -60225, 0]], ![![86, 134, 180], ![74, -3285, 0]], ![![762, 1151, 1537], ![127, -28050, 0]]]
  g := ![![![1, 0, 0], ![-4, 73, 0], ![-34, 0, 73]], ![![0, 1, 0], ![-2, 3, 4], ![-1, 63, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N0 : Nat.card (O ⧸ I73N0) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N0)

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := prime_ideal_of_norm_prime hp73.out _ NI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![28, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![28, 1, 0]] 
 ![![73, 0, 0], ![28, 1, 0], ![67, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![28, 1, 0], ![2, 27, 4], ![349, 63, 29]]]
  hmulB := by decide  
  f := ![![![6013, 100389, 14880], ![3723, -271560, 0]], ![![2292, 38482, 5704], ![1461, -104098, 0]], ![![5523, 92138, 13657], ![3406, -249240, 0]]]
  g := ![![![1, 0, 0], ![-28, 73, 0], ![-67, 0, 73]], ![![0, 1, 0], ![-14, 27, 4], ![-46, 63, 29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1

def I73N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-107, -4, 2]] i)))

def SI73N2: IdealEqSpanCertificate' Table ![![-107, -4, 2]] 
 ![![73, 0, 0], ![41, 1, 0], ![65, 0, 1]] where
  M :=![![![-107, -4, 2], ![690, 23, -14], ![-984, -46, 15]]]
  hmulB := by decide  
  f := ![![![-299, -32, 10]], ![![-121, -13, 4]], ![![-391, -42, 13]]]
  g := ![![![-1, -4, 2], ![9, 23, -14], ![-1, -46, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N2 : Nat.card (O ⧸ I73N2) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N2)

lemma isPrimeI73N2 : Ideal.IsPrime I73N2 := prime_ideal_of_norm_prime hp73.out _ NI73N2
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![4, 1, 0]] ![![73, 0, 0], ![28, 1, 0]]
  ![![299, 32, -10]] where
 M := ![![![5329, 0, 0], ![2044, 73, 0]], ![![292, 73, 0], ![114, 31, 4]]]
 hmul := by decide  
 g := ![![![![7811, 292, -146]], ![![2306, 89, -42]]], ![![![-262, -7, 6]], ![![-72, -1, 2]]]]
 hle2 := by decide  

def MulI73N1 : IdealMulLeCertificate' Table 
  ![![299, 32, -10]] ![![-107, -4, 2]]
  ![![73, 0, 0]] where
 M := ![![![-73, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-3, 20, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-3, 20, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![76, 20, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-3, 20, 1], ![389, 40, 81], ![7186, 1363, 80]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-76, -20, 79]], ![![-1, 0, 1], ![-73, -20, 81], ![14, -3, 80]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [2, 33, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [46, 78], [0, 1]]
 g := ![![[56, 40], [15, 22], [74, 19], [27, 8], [62], [1]], ![[0, 39], [0, 57], [0, 60], [0, 71], [62], [1]]]
 h' := ![![[46, 78], [49, 35], [10, 41], [25, 63], [38, 61], [77, 46], [0, 1]], ![[0, 1], [0, 44], [0, 38], [0, 16], [0, 18], [60, 33], [46, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [76]]
 b := ![[], [74, 38]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [2, 33, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2256, 5007, 4860]
  a := ![-4, 3, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4704, -1167, 4860]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-2, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-2, 1, 0]] 
 ![![79, 0, 0], ![77, 1, 0], ![78, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-2, 1, 0], ![2, -3, 4], ![349, 63, -1]]]
  hmulB := by decide  
  f := ![![![3041, -4562, 6084], ![-79, -120159, 0]], ![![2963, -4445, 5928], ![-78, -117078, 0]], ![![3002, -4504, 6007], ![-98, -118638, 0]]]
  g := ![![![1, 0, 0], ![-77, 79, 0], ![-78, 0, 79]], ![![-1, 1, 0], ![-1, -3, 4], ![-56, 63, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-3, 20, 1]] ![![79, 0, 0], ![-2, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![-158, 79, 0]], ![![-237, 1580, 79], ![395, 0, 79]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![-2, 1, 0]]], ![![![-3, 20, 1]], ![![5, 0, 1]]]]
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


lemma PB207I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB207I1 : PrimesBelowBoundCertificateInterval O 31 79 207 where
  m := 11
  g := ![3, 3, 2, 3, 3, 2, 2, 3, 3, 3, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB207I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N0, I37N1]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1, I47N2]
    · exact ![I53N0, I53N1, I53N2]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1, I67N2]
    · exact ![I71N0, I71N1, I71N2]
    · exact ![I73N0, I73N1, I73N2]
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
    · exact ![41, 41, 41]
    · exact ![1849, 43]
    · exact ![47, 47, 47]
    · exact ![53, 53, 53]
    · exact ![3481, 59]
    · exact ![3721, 61]
    · exact ![67, 67, 67]
    · exact ![71, 71, 71]
    · exact ![73, 73, 73]
    · exact ![6241, 79]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N0
      exact NI37N1
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
      exact NI41N2
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
      exact NI47N2
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
      exact NI73N2
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I37N0, I37N1, I41N0, I41N1, I41N2, I43N1, I47N0, I47N1, I47N2, I53N0, I53N1, I53N2, I59N1, I61N1, I67N0, I67N1, I67N2, I71N0, I71N1, I71N2, I73N0, I73N1, I73N2, I79N1]
  Il := ![[I37N0, I37N0, I37N1], [I41N0, I41N1, I41N2], [I43N1], [I47N0, I47N1, I47N2], [I53N0, I53N1, I53N2], [I59N1], [I61N1], [I67N0, I67N1, I67N2], [I71N0, I71N1, I71N2], [I73N0, I73N1, I73N2], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
