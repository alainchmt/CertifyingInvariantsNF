
import IdealArithmetic.Examples.NF3_1_358280_1.RI3_1_358280_1
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [16, 33, 25, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 26, 11], [28, 10, 26], [0, 1]]
 g := ![![[1, 3, 1], [], [25], [12, 1], []], ![[22, 29, 4, 4], [26, 10], [25, 33, 34, 12], [16, 26], [26, 10]], ![[9, 19, 8, 3], [11, 10], [25, 7, 30, 25], [9, 10], [11, 10]]]
 h' := ![![[21, 26, 11], [12, 14, 1], [7, 1], [30, 32], [0, 0, 1], [0, 1]], ![[28, 10, 26], [35, 31, 16], [28, 26, 11], [36, 18, 19], [25, 0, 10], [21, 26, 11]], ![[0, 1], [13, 29, 20], [35, 10, 26], [1, 24, 18], [16, 0, 26], [28, 10, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 2], []]
 b := ![[], [31, 34, 20], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [16, 33, 25, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8362, 3441, 259]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-226, 93, 7]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-25, -15, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-25, -15, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![16, 26, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-25, -15, 1], ![-142, 5, -14], ![1988, -562, -9]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-16, -26, 41]], ![![-1, -1, 1], ![2, 9, -14], ![52, -8, -9]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [11, 27, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 40], [0, 1]]
 g := ![![[36, 1], [25], [8], [17, 32], [1]], ![[9, 40], [25], [8], [14, 9], [1]]]
 h' := ![![[14, 40], [30, 40], [31, 36], [18, 7], [30, 14], [0, 1]], ![[0, 1], [16, 1], [2, 5], [34, 34], [21, 27], [14, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [33, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [11, 27, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![411, -1418, 346]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-125, -254, 346]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![14, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![14, 1, 0]] 
 ![![41, 0, 0], ![14, 1, 0], ![9, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![14, 1, 0], ![0, 14, 1], ![-142, 30, 15]]]
  hmulB := by decide  
  f := ![![![15, 1, 0], ![-41, 0, 0]], ![![-14, -1, 0], ![42, 0, 0]], ![![-9, -1, 0], ![27, 1, 0]]]
  g := ![![![1, 0, 0], ![-14, 41, 0], ![-9, 0, 41]], ![![0, 1, 0], ![-5, 14, 1], ![-17, 30, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-25, -15, 1]] ![![41, 0, 0], ![14, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![574, 41, 0]], ![![-1025, -615, 41], ![-492, -205, 0]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![14, 1, 0]]], ![![![-25, -15, 1]], ![![-12, -5, 0]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-28, 1, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-28, 1, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![15, 1, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-28, 1, 1], ![-142, 2, 2], ![-284, -82, 4]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-15, -1, 43]], ![![-1, 0, 1], ![-4, 0, 2], ![-8, -2, 4]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [22, 14, 1] where
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
 g := ![![[28, 10], [6, 35], [21], [22, 24], [1]], ![[17, 33], [32, 8], [21], [30, 19], [1]]]
 h' := ![![[29, 42], [40, 15], [3, 11], [32, 35], [21, 29], [0, 1]], ![[0, 1], [2, 28], [21, 32], [15, 8], [2, 14], [29, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [15, 39]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [22, 14, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3364, -286, 144]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![28, -10, 144]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-2, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-2, 1, 0]] 
 ![![43, 0, 0], ![41, 1, 0], ![39, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-2, 1, 0], ![0, -2, 1], ![-142, 30, -1]]]
  hmulB := by decide  
  f := ![![![49, -24, 0], ![1032, 0, 0]], ![![47, -23, 0], ![990, 0, 0]], ![![45, -22, 0], ![948, 1, 0]]]
  g := ![![![1, 0, 0], ![-41, 43, 0], ![-39, 0, 43]], ![![-1, 1, 0], ![1, -2, 1], ![-31, 30, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-28, 1, 1]] ![![43, 0, 0], ![-2, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-86, 43, 0]], ![![-1204, 43, 43], ![-86, 0, 0]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-2, 1, 0]]], ![![![-28, 1, 1]], ![![-2, 0, 0]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![12293, -623, -369]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![12293, -623, -369]] 
 ![![47, 0, 0], ![10, 1, 0], ![41, 0, 1]] where
  M :=![![![12293, -623, -369], ![52398, 1223, -992], ![140864, 22638, 231]]]
  hmulB := by decide  
  f := ![![![22739409, -8209509, 1069303]], ![![1607512, -580353, 75592]], ![![41409043, -14949725, 1947228]]]
  g := ![![![716, -623, -369], ![1720, 1223, -992], ![-2021, 22638, 231]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N0 : Nat.card (O ⧸ I47N0) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N0)

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := prime_ideal_of_norm_prime hp47.out _ NI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![165, -2, -4]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![165, -2, -4]] 
 ![![47, 0, 0], ![15, 1, 0], ![10, 0, 1]] where
  M :=![![![165, -2, -4], ![568, 45, -6], ![852, 388, 39]]]
  hmulB := by decide  
  f := ![![![4083, -1474, 192]], ![![723, -261, 34]], ![![4742, -1712, 223]]]
  g := ![![![5, -2, -4], ![-1, 45, -6], ![-114, 388, 39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1

def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10879345865, -3927722475, 511592767]] i)))

def SI47N2: IdealEqSpanCertificate' Table ![![10879345865, -3927722475, 511592767]] 
 ![![47, 0, 0], ![21, 1, 0], ![29, 0, 1]] where
  M :=![![![10879345865, -3927722475, 511592767], ![-72646172914, 26227128875, -3416129708], ![485090418536, -175130064154, 22810999167]]]
  hmulB := by decide  
  f := ![![![1360093, -195793, -59825]], ![![788449, -96730, -32169]], ![![1611499, -103221, -51600]]]
  g := ![![![1670751651, -3927722475, 511592767], ![-11156342931, 26227128875, -3416129708], ![74495804041, -175130064154, 22810999167]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N2 : Nat.card (O ⧸ I47N2) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N2)

lemma isPrimeI47N2 : Ideal.IsPrime I47N2 := prime_ideal_of_norm_prime hp47.out _ NI47N2
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![12293, -623, -369]] ![![165, -2, -4]]
  ![![1360093, -195793, -59825]] where
 M := ![![![1360093, -195793, -59825]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![1360093, -195793, -59825]] ![![10879345865, -3927722475, 511592767]]
  ![![47, 0, 0]] where
 M := ![![![47, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![30261, -10925, 1423]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![30261, -10925, 1423]] 
 ![![53, 0, 0], ![31, 1, 0], ![46, 0, 1]] where
  M :=![![![30261, -10925, 1423], ![-202066, 72951, -9502], ![1349284, -487126, 63449]]]
  hmulB := by decide  
  f := ![![![-3253, 27, 77]], ![![-2109, -2, 47]], ![![-3102, -124, 51]]]
  g := ![![![5726, -10925, 1423], ![-38235, 72951, -9502], ![255312, -487126, 63449]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N0 : Nat.card (O ⧸ I53N0) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N0)

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := prime_ideal_of_norm_prime hp53.out _ NI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![172635, -13490, -5892]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![172635, -13490, -5892]] 
 ![![53, 0, 0], ![43, 1, 0], ![6, 0, 1]] where
  M :=![![![172635, -13490, -5892], ![836664, -4125, -19382], ![2752244, 255204, -23507]]]
  hmulB := by decide  
  f := ![![![5043330303, -1820771398, 237158680]], ![![3456352273, -1247831687, 162532274]], ![![4813829958, -1737915896, 226366605]]]
  g := ![![![14869, -13490, -5892], ![21327, -4125, -19382], ![-152462, 255204, -23507]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![30261, -10925, 1423]] ![![30261, -10925, 1423]]
  ![![5043330303, -1820771398, 237158680]] where
 M := ![![![5043330303, -1820771398, 237158680]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI53N1 : IdealMulLeCertificate' Table 
  ![![5043330303, -1820771398, 237158680]] ![![172635, -13490, -5892]]
  ![![53, 0, 0]] where
 M := ![![![53, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N0, I53N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N0
    exact isPrimeI53N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0 ⊙ MulI53N1)
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


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [3, 50, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [35, 5, 9], [22, 53, 50], [0, 1]]
 g := ![![[8, 45, 1], [1, 6, 53], [5, 3], [40, 15, 4], [1]], ![[8, 12, 58, 9], [4, 32, 52, 26], [53, 21], [10, 31, 31, 20], [5, 2, 52, 21]], ![[3, 13], [12, 45, 6, 43], [13, 28], [48, 41, 49, 47], [21, 55, 0, 38]]]
 h' := ![![[35, 5, 9], [56, 53, 1], [48, 38, 17], [57, 29, 48], [56, 9, 57], [0, 1]], ![[22, 53, 50], [48, 19, 58], [33, 20, 4], [30, 19, 32], [26, 6, 34], [35, 5, 9]], ![[0, 1], [39, 46], [7, 1, 38], [20, 11, 38], [24, 44, 27], [22, 53, 50]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23, 46], []]
 b := ![[], [52, 23, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [3, 50, 2, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-430346, 200895, -20355]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-7294, 3405, -345]
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


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [45, 25, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [36, 0, 57], [24, 60, 4], [0, 1]]
 g := ![![[48, 15, 15], [9, 34], [56, 28, 58], [31, 49, 1], [1]], ![[5, 0, 3, 25], [26, 36], [10, 3, 36, 58], [21, 21, 14, 5], [29, 31, 3, 58]], ![[28, 22, 30, 45], [29, 13], [9, 60, 40, 42], [37, 12, 11, 45], [33, 42, 10, 3]]]
 h' := ![![[36, 0, 57], [17, 25, 25], [42, 27, 20], [8, 21, 34], [16, 36, 60], [0, 1]], ![[24, 60, 4], [16, 52, 58], [37, 5, 55], [12, 39, 4], [28, 15, 40], [36, 0, 57]], ![[0, 1], [49, 45, 39], [16, 29, 47], [25, 1, 23], [17, 10, 22], [24, 60, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53, 23], []]
 b := ![[], [49, 29, 21], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [45, 25, 1, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1891, 4697, -549]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![31, 77, -9]
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


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [36, 51, 51, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 38, 37], [58, 28, 30], [0, 1]]
 g := ![![[57, 45, 17], [39, 60, 19], [44, 14], [6, 16], [16, 1], []], ![[64, 59, 59, 15], [27, 34, 47, 65], [49, 55], [11, 54], [5, 47], [60, 29]], ![[43, 59, 5, 61], [34, 13, 11, 38], [15, 22], [4, 24], [60, 37], [0, 29]]]
 h' := ![![[25, 38, 37], [3, 26, 33], [17, 8, 35], [44, 10, 58], [27, 19, 4], [0, 0, 1], [0, 1]], ![[58, 28, 30], [47, 13, 10], [25, 13, 3], [39, 49, 51], [57, 13, 11], [6, 7, 28], [25, 38, 37]], ![[0, 1], [30, 28, 24], [33, 46, 29], [29, 8, 25], [46, 35, 52], [14, 60, 38], [58, 28, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28, 22], []]
 b := ![[], [16, 51, 32], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [36, 51, 51, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1666089, 181034, 59898]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-24867, 2702, 894]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![0, 1, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![0, 1, 0]] 
 ![![71, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![0, 1, 0], ![0, 0, 1], ![-142, 30, 1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, 0], ![0, 1, 0]]]
  g := ![![![1, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![0, 1, 0], ![0, 0, 1], ![-2, 30, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N0 : Nat.card (O ⧸ I71N0) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N0)

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := prime_ideal_of_norm_prime hp71.out _ NI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![5, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![5, 1, 0]] 
 ![![71, 0, 0], ![5, 1, 0], ![46, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![5, 1, 0], ![0, 5, 1], ![-142, 30, 6]]]
  hmulB := by decide  
  f := ![![![246, 49, 0], ![-3479, 0, 0]], ![![10, 2, 0], ![-141, 0, 0]], ![![156, 31, 0], ![-2206, 1, 0]]]
  g := ![![![1, 0, 0], ![-5, 71, 0], ![-46, 0, 71]], ![![0, 1, 0], ![-1, 5, 1], ![-8, 30, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-6, 1, 0]] i)))

def SI71N2: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-6, 1, 0]] 
 ![![71, 0, 0], ![65, 1, 0], ![35, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-6, 1, 0], ![0, -6, 1], ![-142, 30, -5]]]
  hmulB := by decide  
  f := ![![![85, -14, 0], ![994, 0, 0]], ![![79, -13, 0], ![924, 0, 0]], ![![49, -8, 0], ![574, 1, 0]]]
  g := ![![![1, 0, 0], ![-65, 71, 0], ![-35, 0, 71]], ![![-1, 1, 0], ![5, -6, 1], ![-27, 30, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![0, 1, 0]] ![![71, 0, 0], ![5, 1, 0]]
  ![![71, 0, 0], ![0, 5, 1]] where
 M := ![![![5041, 0, 0], ![355, 71, 0]], ![![0, 71, 0], ![0, 5, 1]]]
 hmul := by decide  
 g := ![![![![71, 0, 0], ![0, 0, 0]], ![![5, -4, -1], ![71, 0, 0]]], ![![![0, -4, -1], ![71, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![0, 5, 1]] ![![71, 0, 0], ![-6, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-426, 71, 0]], ![![0, 355, 71], ![-142, 0, 0]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-6, 1, 0]]], ![![![0, 5, 1]], ![![-2, 0, 0]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2637, -952, 124]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![2637, -952, 124]] 
 ![![73, 0, 0], ![28, 1, 0], ![19, 0, 1]] where
  M :=![![![2637, -952, 124], ![-17608, 6357, -828], ![117576, -42448, 5529]]]
  hmulB := by decide  
  f := ![![![909, 56, -12]], ![![372, 29, -4]], ![![151, 56, 5]]]
  g := ![![![369, -952, 124], ![-2464, 6357, -828], ![16453, -42448, 5529]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N0 : Nat.card (O ⧸ I73N0) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N0)

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := prime_ideal_of_norm_prime hp73.out _ NI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-66580657007, 24037322296, -3130903546]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-66580657007, 24037322296, -3130903546]] 
 ![![73, 0, 0], ![55, 1, 0], ![41, 0, 1]] where
  M :=![![![-66580657007, 24037322296, -3130903546], ![444588303532, -160507763387, 20906418750], ![-2968711462500, 1071780866032, -139601344637]]]
  hmulB := by decide  
  f := ![![![5494481, -377080, -179698]], ![![4489227, -282683, -143016]], ![![4168989, -91048, -107135]]]
  g := ![![![-17263922437, 24037322296, -3130903546], ![115278796179, -160507763387, 20906418750], ![-769767177591, 1071780866032, -139601344637]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1

def I73N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-74995781, 6064832, 2590222]] i)))

def SI73N2: IdealEqSpanCertificate' Table ![![-74995781, 6064832, 2590222]] 
 ![![73, 0, 0], ![62, 1, 0], ![25, 0, 1]] where
  M :=![![![-74995781, 6064832, 2590222], ![-367811524, 2710879, 8655054], ![-1229017668, -108159904, 11365933]]]
  hmulB := by decide  
  f := ![![![966941478839923, -349090637026944, 45469670035790]], ![![732790117027302, -264555998845985, 34458884592162]], ![![921749510736191, -332775179184800, 43344552929003]]]
  g := ![![![-7065355, 6064832, 2590222], ![-10304964, 2710879, 8655054], ![71133535, -108159904, 11365933]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N2 : Nat.card (O ⧸ I73N2) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N2)

lemma isPrimeI73N2 : Ideal.IsPrime I73N2 := prime_ideal_of_norm_prime hp73.out _ NI73N2
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![2637, -952, 124]] ![![-66580657007, 24037322296, -3130903546]]
  ![![-966941478839923, 349090637026944, -45469670035790]] where
 M := ![![![-966941478839923, 349090637026944, -45469670035790]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI73N1 : IdealMulLeCertificate' Table 
  ![![-966941478839923, 349090637026944, -45469670035790]] ![![-74995781, 6064832, 2590222]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0]] 
 ![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [8, 3, 61, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [29, 68, 25], [68, 10, 54], [0, 1]]
 g := ![![[26, 43, 76], [40, 28, 45], [28, 17, 13], [59, 67, 25], [18, 1], []], ![[10, 7, 25, 73], [20, 54, 42, 5], [65, 61, 34, 62], [28, 46, 12, 25], [68, 21], [35, 72]], ![[17, 46, 37, 48], [54, 21, 52, 47], [76, 12, 43, 47], [63, 63, 29, 48], [20, 42], [6, 72]]]
 h' := ![![[29, 68, 25], [75, 62, 32], [13, 21, 19], [2, 36, 31], [14, 17, 5], [0, 0, 1], [0, 1]], ![[68, 10, 54], [75, 7, 53], [63, 67, 4], [30, 32, 25], [73, 12, 1], [8, 24, 10], [29, 68, 25]], ![[0, 1], [70, 10, 73], [63, 70, 56], [52, 11, 23], [34, 50, 73], [73, 55, 68], [68, 10, 54]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [74, 65], []]
 b := ![[], [45, 23, 29], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [8, 3, 61, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9875, 474, -158]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-125, 6, -2]
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



lemma PB170I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB170I1 : PrimesBelowBoundCertificateInterval O 31 79 170 where
  m := 11
  g := ![1, 2, 2, 3, 3, 1, 1, 1, 3, 3, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB170I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1, I47N2]
    · exact ![I53N0, I53N0, I53N1]
    · exact ![I59N0]
    · exact ![I61N0]
    · exact ![I67N0]
    · exact ![I71N0, I71N1, I71N2]
    · exact ![I73N0, I73N1, I73N2]
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
    · exact ![47, 47, 47]
    · exact ![53, 53, 53]
    · exact ![205379]
    · exact ![226981]
    · exact ![300763]
    · exact ![71, 71, 71]
    · exact ![73, 73, 73]
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
      exact NI47N2
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N0
      exact NI53N1
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
  β := ![I41N1, I43N1, I47N0, I47N1, I47N2, I53N0, I53N1, I71N0, I71N1, I71N2, I73N0, I73N1, I73N2]
  Il := ![[], [I41N1], [I43N1], [I47N0, I47N1, I47N2], [I53N0, I53N0, I53N1], [], [], [], [I71N0, I71N1, I71N2], [I73N0, I73N1, I73N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
