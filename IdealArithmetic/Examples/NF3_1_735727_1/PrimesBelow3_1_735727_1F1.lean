
import IdealArithmetic.Examples.NF3_1_735727_1.RI3_1_735727_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-280, 365, -64]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![-280, 365, -64]] 
 ![![37, 0, 0], ![0, 37, 0], ![9, 18, 1]] where
  M :=![![![-280, 365, -64], ![-3264, 3240, 365], ![18615, -23339, 3240]]]
  hmulB := by decide  
  f := ![![![-513955, -8408, -9205]], ![![-469455, -7680, -8408]], ![![-364989, -5971, -6537]]]
  g := ![![![8, 41, -64], ![-177, -90, 365], ![-285, -2207, 3240]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [2, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 36], [0, 1]]
 g := ![![[33, 27], [25], [34, 1], [27], [1]], ![[27, 10], [25], [5, 36], [27], [1]]]
 h' := ![![[8, 36], [23, 29], [6, 32], [24, 36], [35, 8], [0, 1]], ![[0, 1], [33, 8], [3, 5], [16, 1], [25, 29], [8, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [16, 33]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [2, 29, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![104, -88, -83]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![23, 38, -83]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-513955, -8408, -9205]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-513955, -8408, -9205]] 
 ![![37, 0, 0], ![19, 1, 0], ![9, 0, 1]] where
  M :=![![![-513955, -8408, -9205], ![-469455, -7680, -8408], ![-428808, -7015, -7680]]]
  hmulB := by decide  
  f := ![![![-280, 365, -64]], ![![-232, 275, -23]], ![![435, -542, 72]]]
  g := ![![![-7334, -8408, -9205], ![-6699, -7680, -8408], ![-6119, -7015, -7680]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![-280, 365, -64]] ![![-513955, -8408, -9205]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5992293714997070, -98030372743675, -107322748211831]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![-5992293714997070, -98030372743675, -107322748211831]] 
 ![![41, 0, 0], ![5, 1, 0], ![16, 0, 1]] where
  M :=![![![-5992293714997070, -98030372743675, -107322748211831], ![-5473460158803381, -89542563346365, -98030372743675], ![-4999549009927425, -81789657901256, -89542563346365]]]
  hmulB := by decide  
  f := ![![![-10157425, 19031639, -8661310]], ![![-12012535, 13692020, -592071]], ![![19709629, -28877091, 7991065]]]
  g := ![![![-92316533655839, -98030372743675, -107322748211831], ![-84323448248116, -89542563346365, -98030372743675], ![-77022431875105, -81789657901256, -89542563346365]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N0)

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := prime_ideal_of_norm_prime hp41.out _ NI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-22, 25, -1]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-22, 25, -1]] 
 ![![41, 0, 0], ![7, 1, 0], ![33, 0, 1]] where
  M :=![![![-22, 25, -1], ![-51, 33, 25], ![1275, -1426, 33]]]
  hmulB := by decide  
  f := ![![![36739, 601, 658]], ![![7091, 116, 127]], ![![30318, 496, 543]]]
  g := ![![![-4, 25, -1], ![-27, 33, 25], ![248, -1426, 33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-299797, 314184, 15361]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![-299797, 314184, 15361]] 
 ![![41, 0, 0], ![29, 1, 0], ![20, 0, 1]] where
  M :=![![![-299797, 314184, 15361], ![783411, -1144652, 314184], ![16023384, -16496709, -1144652]]]
  hmulB := by decide  
  f := ![![![6493230221560, 106225397019, 116294585228]], ![![4737431713948, 77501574331, 84848008991]], ![![3299563406809, 53978901243, 59095603380]]]
  g := ![![![-237033, 314184, 15361], ![675479, -1144652, 314184], ![12617585, -16496709, -1144652]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![-5992293714997070, -98030372743675, -107322748211831]] ![![-22, 25, -1]]
  ![![-6493230221560, -106225397019, -116294585228]] where
 M := ![![![-6493230221560, -106225397019, -116294585228]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![-6493230221560, -106225397019, -116294585228]] ![![-299797, 314184, 15361]]
  ![![41, 0, 0]] where
 M := ![![![-41, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![96091, 1572, 1721]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![96091, 1572, 1721]] 
 ![![43, 0, 0], ![0, 43, 0], ![29, 24, 1]] where
  M :=![![![96091, 1572, 1721], ![87771, 1436, 1572], ![80172, 1311, 1436]]]
  hmulB := by decide  
  f := ![![![28, -27, -4]], ![![-204, 248, -27]], ![![-127, 150, -12]]]
  g := ![![![1074, -924, 1721], ![981, -844, 1572], ![896, -771, 1436]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [26, 34, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 42], [0, 1]]
 g := ![![[41, 31], [35, 13], [41], [3, 38], [1]], ![[19, 12], [23, 30], [41], [1, 5], [1]]]
 h' := ![![[9, 42], [36, 17], [30, 23], [8, 16], [17, 9], [0, 1]], ![[0, 1], [17, 26], [22, 20], [23, 27], [12, 34], [9, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [37, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [26, 34, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-619, 1055, -395]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![252, 245, -395]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![28, -27, -4]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![28, -27, -4]] 
 ![![43, 0, 0], ![19, 1, 0], ![26, 0, 1]] where
  M :=![![![28, -27, -4], ![-204, 248, -27], ![-1377, 1281, 248]]]
  hmulB := by decide  
  f := ![![![96091, 1572, 1721]], ![![44500, 728, 797]], ![![59966, 981, 1074]]]
  g := ![![![15, -27, -4], ![-98, 248, -27], ![-748, 1281, 248]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![96091, 1572, 1721]] ![![28, -27, -4]]
  ![![43, 0, 0]] where
 M := ![![![43, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5415523625, 88594756, 96992722]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![5415523625, 88594756, 96992722]] 
 ![![47, 0, 0], ![0, 47, 0], ![17, 3, 1]] where
  M :=![![![5415523625, 88594756, 96992722], ![4946628822, 80923915, 88594756], ![4518332556, 73917242, 80923915]]]
  hmulB := by decide  
  f := ![![![-5441, 6872, -1002]], ![![-51102, 49669, 6872]], ![![2227, -3473, 1133]]]
  g := ![![![80141433, -4306030, 96992722], ![73202510, -3933199, 88594756], ![66864383, -3592649, 80923915]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [37, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [35, 46], [0, 1]]
 g := ![![[27, 14], [30, 4], [9, 27], [6, 3], [1]], ![[0, 33], [29, 43], [14, 20], [17, 44], [1]]]
 h' := ![![[35, 46], [18, 25], [43, 2], [13, 11], [10, 35], [0, 1]], ![[0, 1], [0, 22], [19, 45], [22, 36], [13, 12], [35, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [3, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [37, 12, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3263, 45, 62]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![47, -3, 62]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5441, 6872, -1002]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-5441, 6872, -1002]] 
 ![![47, 0, 0], ![44, 1, 0], ![38, 0, 1]] where
  M :=![![![-5441, 6872, -1002], ![-51102, 49669, 6872], ![350472, -429062, 49669]]]
  hmulB := by decide  
  f := ![![![5415523625, 88594756, 96992722]], ![![5175099326, 84661557, 92686692]], ![![4474643198, 73202510, 80141433]]]
  g := ![![![-5739, 6872, -1002], ![-53142, 49669, 6872], ![368974, -429062, 49669]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![5415523625, 88594756, 96992722]] ![![-5441, 6872, -1002]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-301, 198, 144]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-301, 198, 144]] 
 ![![53, 0, 0], ![0, 53, 0], ![13, 8, 1]] where
  M :=![![![-301, 198, 144], ![7344, -8221, 198], ![10098, -3546, -8221]]]
  hmulB := by decide  
  f := ![![![-1288433, -21078, -23076]], ![![-1176876, -19253, -21078]], ![![-513955, -8408, -9205]]]
  g := ![![![-41, -18, 144], ![90, -185, 198], ![2207, 1174, -8221]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [29, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [39, 52], [0, 1]]
 g := ![![[48, 11], [16], [1, 6], [11], [39, 1]], ![[0, 42], [16], [23, 47], [11], [25, 52]]]
 h' := ![![[39, 52], [6, 8], [24, 49], [5, 35], [35, 8], [0, 1]], ![[0, 1], [0, 45], [27, 4], [45, 18], [29, 45], [39, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45]]
 b := ![[], [25, 49]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [29, 14, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-262, 805, -542]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![128, 97, -542]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1288433, -21078, -23076]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-1288433, -21078, -23076]] 
 ![![53, 0, 0], ![45, 1, 0], ![42, 0, 1]] where
  M :=![![![-1288433, -21078, -23076], ![-1176876, -19253, -21078], ![-1074978, -17586, -19253]]]
  hmulB := by decide  
  f := ![![![-301, 198, 144]], ![![-117, 13, 126]], ![![-48, 90, -41]]]
  g := ![![![11873, -21078, -23076], ![10845, -19253, -21078], ![9906, -17586, -19253]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-301, 198, 144]] ![![-1288433, -21078, -23076]]
  ![![53, 0, 0]] where
 M := ![![![53, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2460331, -3846568, 1262316]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![2460331, -3846568, 1262316]] 
 ![![59, 0, 0], ![8, 1, 0], ![54, 0, 1]] where
  M :=![![![2460331, -3846568, 1262316], ![64378116, -66967049, -3846568], ![-196174968, 275939356, -66967049]]]
  hmulB := by decide  
  f := ![![![5546005148498609, 90729356370664, 99329662804108]], ![![837861932050820, 13706924495559, 15006214555992]], ![![5154431782946250, 84323448248116, 92316533655839]]]
  g := ![![![-592071, -3846568, 1262316], ![13692020, -66967049, -3846568], ![20551370, 275939356, -66967049]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N0 : Nat.card (O ⧸ I59N0) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N0)

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := prime_ideal_of_norm_prime hp59.out _ NI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8036995120757, -131480475574, -143943612371]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![-8036995120757, -131480475574, -143943612371]] 
 ![![59, 0, 0], ![25, 1, 0], ![24, 0, 1]] where
  M :=![![![-8036995120757, -131480475574, -143943612371], ![-7341124230921, -120096440352, -131480475574], ![-6705504254274, -109698074351, -120096440352]]]
  hmulB := by decide  
  f := ![![![-2481430, 2565827, 165116]], ![![-908726, 891235, 113453]], ![![1208523, -1205419, -128814]]]
  g := ![![![-21954856517, -131480475574, -143943612371], ![-20053928955, -120096440352, -131480475574], ![-18317590289, -109698074351, -120096440352]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![670, 11, 12]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![670, 11, 12]] 
 ![![59, 0, 0], ![26, 1, 0], ![32, 0, 1]] where
  M :=![![![670, 11, 12], ![612, 10, 11], ![561, 7, 10]]]
  hmulB := by decide  
  f := ![![![23, -26, 1]], ![![11, -12, 0]], ![![-10, 11, 0]]]
  g := ![![![0, 11, 12], ![0, 10, 11], ![1, 7, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![2460331, -3846568, 1262316]] ![![-8036995120757, -131480475574, -143943612371]]
  ![![-23, 26, -1]] where
 M := ![![![-23, 26, -1]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![-23, 26, -1]] ![![670, 11, 12]]
  ![![59, 0, 0]] where
 M := ![![![-59, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-454325561619218, -7432496848585, -8137029020094]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![-454325561619218, -7432496848585, -8137029020094]] 
 ![![61, 0, 0], ![0, 61, 0], ![13, 18, 1]] where
  M :=![![![-454325561619218, -7432496848585, -8137029020094], ![-414988480024794, -6788965514048, -7432496848585], ![-379057339277835, -6201153352619, -6788965514048]]]
  hmulB := by decide  
  f := ![![![-2117249, 2096654, 242267]], ![![12355617, -15441934, 2096654]], ![![4947643, -5797683, 417169]]]
  g := ![![![-5713839087836, 2279246319887, -8137029020094], ![-5219115098249, 2081901274762, -7432496848585], ![-4767226026151, 1901643047545, -6788965514048]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [9, 36, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [25, 60], [0, 1]]
 g := ![![[4, 34], [46], [53, 36], [30, 36], [25, 1]], ![[0, 27], [46], [38, 25], [15, 25], [50, 60]]]
 h' := ![![[25, 60], [12, 41], [11, 30], [35, 55], [19, 6], [0, 1]], ![[0, 1], [0, 20], [29, 31], [7, 6], [47, 55], [25, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [54, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [9, 36, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![111, -95, -90]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![21, 25, -90]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2117249, 2096654, 242267]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![-2117249, 2096654, 242267]] 
 ![![61, 0, 0], ![43, 1, 0], ![42, 0, 1]] where
  M :=![![![-2117249, 2096654, 242267], ![12355617, -15441934, 2096654], ![106929354, -102960353, -15441934]]]
  hmulB := by decide  
  f := ![![![-454325561619218, -7432496848585, -8137029020094]], ![![-327065370977888, -5350595573823, -5857782700207]], ![![-319028375857131, -5219115098249, -5713839087836]]]
  g := ![![![-1679485, 2096654, 242267], ![9644251, -15441934, 2096654], ![84963701, -102960353, -15441934]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![-454325561619218, -7432496848585, -8137029020094]] ![![-2117249, 2096654, 242267]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![55, 1, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![55, 1, 1]] 
 ![![67, 0, 0], ![4, 1, 0], ![51, 0, 1]] where
  M :=![![![55, 1, 1], ![51, 0, 1], ![51, -4, 0]]]
  hmulB := by decide  
  f := ![![![4, -4, 1]], ![![1, -1, 0]], ![![0, 1, 0]]]
  g := ![![![0, 1, 1], ![0, 0, 1], ![1, -4, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N0 : Nat.card (O ⧸ I67N0) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N0)

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := prime_ideal_of_norm_prime hp67.out _ NI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![-2, 1, 0]] 
 ![![67, 0, 0], ![65, 1, 0], ![63, 0, 1]] where
  M :=![![![-2, 1, 0], ![0, -2, 1], ![51, -55, -2]]]
  hmulB := by decide  
  f := ![![![-59, -2, -1]], ![![-58, -2, -1]], ![![-57, -1, -1]]]
  g := ![![![-1, 1, 0], ![1, -2, 1], ![56, -55, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![55, 1, 1]] ![![-2, 1, 0]]
  ![![-59, -2, -1]] where
 M := ![![![-59, -2, -1]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![-59, -2, -1]] ![![-2, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![67, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1, I67N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
    exact isPrimeI67N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0 ⊙ MulI67N1)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-90900708400381902230, -1487081700426612731, -1628043334310429095]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-90900708400381902230, -1487081700426612731, -1628043334310429095]] 
 ![![71, 0, 0], ![0, 71, 0], ![8, 33, 1]] where
  M :=![![![-90900708400381902230, -1487081700426612731, -1628043334310429095], ![-83030210049831883845, -1358325013308302005, -1487081700426612731], ![-75841166721757249281, -1240716526368183640, -1358325013308302005]]]
  hmulB := by decide  
  f := ![![![1096942265, -1138495495, -68344266]], ![![-3485557566, 4855876895, -1138495495]], ![![-2314241293, 2961516454, -468468008]]]
  g := ![![![-1096850165153499570, 735751384955176724, -1628043334310429095], ![-1001881076710126507, 672047480292534058, -1487081700426612731], ![-915134741060434271, 613859280462053275, -1358325013308302005]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [16, 49, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 70], [0, 1]]
 g := ![![[43, 40], [64, 10], [32, 5], [16], [58], [1]], ![[0, 31], [0, 61], [0, 66], [16], [58], [1]]]
 h' := ![![[22, 70], [41, 53], [56, 62], [52, 17], [38, 4], [55, 22], [0, 1]], ![[0, 1], [0, 18], [0, 9], [0, 54], [55, 67], [42, 49], [22, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48]]
 b := ![[], [20, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [16, 49, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2004, -1070, 357]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-12, -181, 357]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1096942265, -1138495495, -68344266]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![1096942265, -1138495495, -68344266]] 
 ![![71, 0, 0], ![38, 1, 0], ![47, 0, 1]] where
  M :=![![![1096942265, -1138495495, -68344266], ![-3485557566, 4855876895, -1138495495], ![-58063270245, 59131694659, 4855876895]]]
  hmulB := by decide  
  f := ![![![-90900708400381902230, -1487081700426612731, -1628043334310429095]], ![![-49820522947385129135, -815034220134078673, -892291949355252371]], ![![-61241893824502910621, -1001881076710126507, -1096850165153499570]]]
  g := ![![![670027487, -1138495495, -68344266], ![-1894360441, 4855876895, -1138495495], ![-35680195512, 59131694659, 4855876895]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-90900708400381902230, -1487081700426612731, -1628043334310429095]] ![![1096942265, -1138495495, -68344266]]
  ![![71, 0, 0]] where
 M := ![![![71, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-314828401, -5150406, -5638617]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![-314828401, -5150406, -5638617]] 
 ![![73, 0, 0], ![0, 73, 0], ![39, 35, 1]] where
  M :=![![![-314828401, -5150406, -5638617], ![-287569467, -4704466, -5150406], ![-262670706, -4297137, -4704466]]]
  hmulB := by decide  
  f := ![![![-2158, 2379, -18]], ![![-918, -1168, 2379]], ![![69, -1094, 1115]]]
  g := ![![![-1300306, 2632893, -5638617], ![-1187721, 2404928, -5150406], ![-1084884, 2196701, -4704466]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [66, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [60, 72], [0, 1]]
 g := ![![[19, 12], [37], [27], [24, 24], [23], [1]], ![[9, 61], [37], [27], [4, 49], [23], [1]]]
 h' := ![![[60, 72], [4, 31], [16, 16], [22, 10], [64, 30], [7, 60], [0, 1]], ![[0, 1], [39, 42], [27, 57], [38, 63], [39, 43], [30, 13], [60, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40]]
 b := ![[], [57, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [66, 13, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-252, 414, -57]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![27, 33, -57]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2158, 2379, -18]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-2158, 2379, -18]] 
 ![![73, 0, 0], ![38, 1, 0], ![16, 0, 1]] where
  M :=![![![-2158, 2379, -18], ![-918, -1168, 2379], ![121329, -131763, -1168]]]
  hmulB := by decide  
  f := ![![![-314828401, -5150406, -5638617]], ![![-167822585, -2745478, -3005724]], ![![-72601714, -1187721, -1300306]]]
  g := ![![![-1264, 2379, -18], ![74, -1168, 2379], ![70507, -131763, -1168]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![-314828401, -5150406, -5638617]] ![![-2158, 2379, -18]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-529963808888, -8669893733, -9491719720]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![-529963808888, -8669893733, -9491719720]] 
 ![![79, 0, 0], ![18, 1, 0], ![71, 0, 1]] where
  M :=![![![-529963808888, -8669893733, -9491719720], ![-484077705720, -7919224288, -8669893733], ![-442164580383, -7233550405, -7919224288]]]
  hmulB := by decide  
  f := ![![![4921, 100504, -115929]], ![![-73719, 103672, -25142]], ![![69305, -54485, -23417]]]
  g := ![![![3797549094, -8669893733, -9491719720], ![3468744133, -7919224288, -8669893733], ![3168408245, -7233550405, -7919224288]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N0 : Nat.card (O ⧸ I79N0) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N0)

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := prime_ideal_of_norm_prime hp79.out _ NI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61241893824502910621, 1001881076710126507, 1096850165153499570]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![61241893824502910621, 1001881076710126507, 1096850165153499570]] 
 ![![79, 0, 0], ![43, 1, 0], ![47, 0, 1]] where
  M :=![![![61241893824502910621, 1001881076710126507, 1096850165153499570], ![55939358422828478070, 915134741060434271, 1001881076710126507], ![51095934912216451857, 835899203771520185, 915134741060434271]]]
  hmulB := by decide  
  f := ![![![8057257646, -9124500947, 332257579]], ![![4600091333, -5095828480, 65349050]], ![![-1096942265, 1138495495, 68344266]]]
  g := ![![![-422670256155025430, 1001881076710126507, 1096850165153499570], ![-386074000609444828, 915134741060434271, 1001881076710126507], ![-352646375693662365, 835899203771520185, 915134741060434271]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![-529963808888, -8669893733, -9491719720]] ![![-529963808888, -8669893733, -9491719720]]
  ![![289255443265290280302064, 4732047571444385972608, 5180602050391566106009]] where
 M := ![![![289255443265290280302064, 4732047571444385972608, 5180602050391566106009]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI79N1 : IdealMulLeCertificate' Table 
  ![![289255443265290280302064, 4732047571444385972608, 5180602050391566106009]] ![![61241893824502910621, 1001881076710126507, 1096850165153499570]]
  ![![79, 0, 0]] where
 M := ![![![18243966554958237958999512374919200329437017, 298460477200852767034619180506019596950881, 326751778548926850294123490834636173467175]]]
 hmul := by decide  
 g := ![![![![230936285505800480493664713606572156068823, 3777980724061427430817964310202779708239, 4136098462644643674609158111830837638825]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N0, I79N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N0
    exact isPrimeI79N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0 ⊙ MulI79N1)


lemma PB243I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB243I1 : PrimesBelowBoundCertificateInterval O 31 79 243 where
  m := 11
  g := ![2, 3, 2, 2, 2, 3, 2, 3, 2, 2, 3]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB243I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1, I59N2]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1, I67N1]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1]
    · exact ![I79N0, I79N0, I79N1]
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
    · exact ![41, 41, 41]
    · exact ![1849, 43]
    · exact ![2209, 47]
    · exact ![2809, 53]
    · exact ![59, 59, 59]
    · exact ![3721, 61]
    · exact ![67, 67, 67]
    · exact ![5041, 71]
    · exact ![5329, 73]
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
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
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
      exact NI79N0
      exact NI79N1
  β := ![I37N1, I41N0, I41N1, I41N2, I43N1, I47N1, I53N1, I59N0, I59N1, I59N2, I61N1, I67N0, I67N1, I71N1, I73N1, I79N0, I79N1]
  Il := ![[I37N1], [I41N0, I41N1, I41N2], [I43N1], [I47N1], [I53N1], [I59N0, I59N1, I59N2], [I61N1], [I67N0, I67N1, I67N1], [I71N1], [I73N1], [I79N0, I79N0, I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
