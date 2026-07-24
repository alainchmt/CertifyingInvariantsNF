
import IdealArithmetic.Examples.NF3_3_653844_1.RI3_3_653844_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0]] 
 ![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [136, 35, 92, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 73, 105], [7, 65, 34], [0, 1]]
 g := ![![[106, 132, 24], [57, 41, 38], [129, 29], [69, 61, 1], [86, 137], [47, 1], []], ![[117, 55, 42, 92], [25, 30, 12, 17], [24, 11], [28, 119, 135, 33], [107, 45], [6, 55], [23, 44]], ![[120, 60, 135, 91], [42, 63, 126, 124], [2, 35], [80, 99, 117, 52], [60, 57], [95, 47], [94, 44]]]
 h' := ![![[40, 73, 105], [32, 123, 118], [7, 110, 90], [68, 109, 53], [123, 7, 1], [2, 26, 89], [0, 0, 1], [0, 1]], ![[7, 65, 34], [66, 135, 13], [49, 43, 25], [33, 55, 17], [126, 118, 105], [19, 3, 36], [1, 24, 65], [40, 73, 105]], ![[0, 1], [58, 20, 8], [126, 125, 24], [26, 114, 69], [86, 14, 33], [36, 110, 14], [53, 115, 73], [7, 65, 34]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [100, 12], []]
 b := ![[], [11, 116, 123], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [136, 35, 92, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-278, 1529, 1529]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2, 11, 11]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 2685619 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def PBC139 : ContainsPrimesAboveP 139 ![I139N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![139, 0, 0]]) timesTableT_eq_Table B_one_repr 139 (by decide) 𝕀

instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![659, 19, -16]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![659, 19, -16]] 
 ![![149, 0, 0], ![0, 149, 0], ![24, 64, 1]] where
  M :=![![![659, 19, -16], ![-2208, -77, 57], ![2622, 138, -77]]]
  hmulB := by decide  
  f := ![![![13, 5, 1]], ![![138, 59, 15]], ![![66, 28, 7]]]
  g := ![![![7, 7, -16], ![-24, -25, 57], ![30, 34, -77]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [40, 148, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 148], [0, 1]]
 g := ![![[108, 130], [96], [148, 129], [107], [98, 132], [1], [1]], ![[89, 19], [96], [128, 20], [107], [81, 17], [1], [1]]]
 h' := ![![[1, 148], [144, 32], [40, 29], [71, 125], [103, 16], [70, 70], [109, 1], [0, 1]], ![[0, 1], [27, 117], [69, 120], [47, 24], [119, 133], [140, 79], [110, 148], [1, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60]]
 b := ![[], [134, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [40, 148, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1763, -430, 864]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-151, -374, 864]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 5, 1]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![13, 5, 1]] 
 ![![149, 0, 0], ![106, 1, 0], ![79, 0, 1]] where
  M :=![![![13, 5, 1], ![138, 59, 15], ![690, 276, 59]]]
  hmulB := by decide  
  f := ![![![659, 19, -16]], ![![454, 13, -11]], ![![367, 11, -9]]]
  g := ![![![-4, 5, 1], ![-49, 59, 15], ![-223, 276, 59]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![659, 19, -16]] ![![13, 5, 1]]
  ![![149, 0, 0]] where
 M := ![![![149, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC149 : ContainsPrimesAboveP 149 ![I149N0, I149N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
    exact isPrimeI149N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 149 (by decide) (𝕀 ⊙ MulI149N0)
instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-113, -5, 3]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![-113, -5, 3]] 
 ![![151, 0, 0], ![0, 151, 0], ![63, 99, 1]] where
  M :=![![![-113, -5, 3], ![414, 25, -15], ![-690, -92, 25]]]
  hmulB := by decide  
  f := ![![![-5, -1, 0]], ![![0, -5, -3]], ![![-3, -4, -2]]]
  g := ![![![-2, -2, 3], ![9, 10, -15], ![-15, -17, 25]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [38, 106, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [45, 150], [0, 1]]
 g := ![![[122, 4], [58, 29], [8, 16], [34], [79, 72], [62], [1]], ![[0, 147], [4, 122], [124, 135], [34], [148, 79], [62], [1]]]
 h' := ![![[45, 150], [61, 2], [149, 123], [89, 147], [18, 100], [145, 125], [113, 45], [0, 1]], ![[0, 1], [0, 149], [97, 28], [60, 4], [139, 51], [32, 26], [24, 106], [45, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [94]]
 b := ![[], [75, 47]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [38, 106, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2926, -68, 71]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-49, -47, 71]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![5, 1, 0]] 
 ![![151, 0, 0], ![5, 1, 0], ![42, 0, 1]] where
  M :=![![![5, 1, 0], ![0, 5, 3], ![138, 46, 5]]]
  hmulB := by decide  
  f := ![![![113, 5, -3]], ![![1, 0, 0]], ![![36, 2, -1]]]
  g := ![![![0, 1, 0], ![-1, 5, 3], ![-2, 46, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![-113, -5, 3]] ![![5, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![-151, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC151 : ContainsPrimesAboveP 151 ![I151N0, I151N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
    exact isPrimeI151N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 151 (by decide) (𝕀 ⊙ MulI151N0)
instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-46423, -19037, -4383]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![-46423, -19037, -4383]] 
 ![![157, 0, 0], ![0, 157, 0], ![40, 9, 1]] where
  M :=![![![-46423, -19037, -4383], ![-604854, -248041, -57111], ![-2627106, -1077320, -248041]]]
  hmulB := by decide  
  f := ![![![15827, 401, -372]], ![![-51336, -1285, 1203]], ![![1442, 37, -34]]]
  g := ![![![821, 130, -4383], ![10698, 1694, -57111], ![46462, 7357, -248041]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [132, 43, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [114, 156], [0, 1]]
 g := ![![[149, 113], [118], [56, 147], [117, 90], [155, 132], [122], [1]], ![[0, 44], [118], [15, 10], [15, 67], [131, 25], [122], [1]]]
 h' := ![![[114, 156], [136, 120], [144, 78], [99, 33], [107, 103], [64, 140], [25, 114], [0, 1]], ![[0, 1], [0, 37], [87, 79], [93, 124], [74, 54], [10, 17], [147, 43], [114, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41]]
 b := ![[], [9, 99]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [132, 43, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-652, 183, 282]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-76, -15, 282]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15827, 401, -372]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![15827, 401, -372]] 
 ![![157, 0, 0], ![130, 1, 0], ![71, 0, 1]] where
  M :=![![![15827, 401, -372], ![-51336, -1285, 1203], ![55338, 1334, -1285]]]
  hmulB := by decide  
  f := ![![![-46423, -19037, -4383]], ![![-42292, -17343, -3993]], ![![-37727, -15471, -3562]]]
  g := ![![![-63, 401, -372], ![193, -1285, 1203], ![-171, 1334, -1285]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![-46423, -19037, -4383]] ![![15827, 401, -372]]
  ![![157, 0, 0]] where
 M := ![![![157, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC157 : ContainsPrimesAboveP 157 ![I157N0, I157N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
    exact isPrimeI157N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 157 (by decide) (𝕀 ⊙ MulI157N0)
instance hp163 : Fact (Nat.Prime 163) := {out := by norm_num}

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-499, -92, 30]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![-499, -92, 30]] 
 ![![163, 0, 0], ![68, 1, 0], ![143, 0, 1]] where
  M :=![![![-499, -92, 30], ![4140, 881, -276], ![-12696, -2852, 881]]]
  hmulB := by decide  
  f := ![![![10991, 4508, 1038]], ![![5464, 2241, 516]], ![![13459, 5520, 1271]]]
  g := ![![![9, -92, 30], ![-100, 881, -276], ![339, -2852, 881]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N0 : Nat.card (O ⧸ I163N0) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N0)

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := prime_ideal_of_norm_prime hp163.out _ NI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![605, -3, -10]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![605, -3, -10]] 
 ![![163, 0, 0], ![113, 1, 0], ![36, 0, 1]] where
  M :=![![![605, -3, -10], ![-1380, 145, -9], ![-414, -598, 145]]]
  hmulB := by decide  
  f := ![![![-15643, -6415, -1477]], ![![-12095, -4960, -1142]], ![![-8886, -3644, -839]]]
  g := ![![![8, -3, -10], ![-107, 145, -9], ![380, -598, 145]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1

def I163N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 12, -4]] i)))

def SI163N2: IdealEqSpanCertificate' Table ![![53, 12, -4]] 
 ![![163, 0, 0], ![145, 1, 0], ![55, 0, 1]] where
  M :=![![![53, 12, -4], ![-552, -131, 36], ![1656, 368, -131]]]
  hmulB := by decide  
  f := ![![![-3913, -100, 92]], ![![-3403, -87, 80]], ![![-1405, -36, 33]]]
  g := ![![![-9, 12, -4], ![101, -131, 36], ![-273, 368, -131]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N2 : Nat.card (O ⧸ I163N2) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N2)

lemma isPrimeI163N2 : Ideal.IsPrime I163N2 := prime_ideal_of_norm_prime hp163.out _ NI163N2
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![-499, -92, 30]] ![![605, -3, -10]]
  ![![-187355, -29783, 10168]] where
 M := ![![![-187355, -29783, 10168]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI163N1 : IdealMulLeCertificate' Table 
  ![![-187355, -29783, 10168]] ![![53, 12, -4]]
  ![![163, 0, 0]] where
 M := ![![![23348609, 5395137, -1654776]]]
 hmul := by decide  
 g := ![![![![143243, 33099, -10152]]]]
 hle2 := by decide  


def PBC163 : ContainsPrimesAboveP 163 ![I163N0, I163N1, I163N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI163N0
    exact isPrimeI163N1
    exact isPrimeI163N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 163 (by decide) (𝕀 ⊙ MulI163N0 ⊙ MulI163N1)
instance hp167 : Fact (Nat.Prime 167) := {out := by norm_num}

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![133, 68, 25]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![133, 68, 25]] 
 ![![167, 0, 0], ![0, 167, 0], ![12, 143, 1]] where
  M :=![![![133, 68, 25], ![3450, 1283, 204], ![9384, 4278, 1283]]]
  hmulB := by decide  
  f := ![![![4631, 118, -109]], ![![-15042, -383, 354]], ![![-12450, -317, 293]]]
  g := ![![![-1, -21, 25], ![6, -167, 204], ![-36, -1073, 1283]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [42, 106, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [61, 166], [0, 1]]
 g := ![![[90, 4], [13, 8], [165, 63], [122], [19], [81, 47], [1]], ![[0, 163], [0, 159], [0, 104], [122], [19], [109, 120], [1]]]
 h' := ![![[61, 166], [122, 165], [84, 26], [150, 118], [40, 17], [105, 55], [125, 61], [0, 1]], ![[0, 1], [0, 2], [0, 141], [0, 49], [75, 150], [120, 112], [5, 106], [61, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58]]
 b := ![[], [34, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [42, 106, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![318, 32, -57]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![6, 49, -57]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4631, 118, -109]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![4631, 118, -109]] 
 ![![167, 0, 0], ![72, 1, 0], ![109, 0, 1]] where
  M :=![![![4631, 118, -109], ![-15042, -383, 354], ![16284, 414, -383]]]
  hmulB := by decide  
  f := ![![![133, 68, 25]], ![![78, 37, 12]], ![![143, 70, 24]]]
  g := ![![![48, 118, -109], ![-156, -383, 354], ![169, 414, -383]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![133, 68, 25]] ![![4631, 118, -109]]
  ![![167, 0, 0]] where
 M := ![![![167, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC167 : ContainsPrimesAboveP 167 ![I167N0, I167N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI167N0
    exact isPrimeI167N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 167 (by decide) (𝕀 ⊙ MulI167N0)
instance hp173 : Fact (Nat.Prime 173) := {out := by norm_num}

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0]] 
 ![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [22, 152, 78, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [50, 109, 41], [45, 63, 132], [0, 1]]
 g := ![![[155, 157, 148], [34, 83], [91, 77, 81], [97, 60, 167], [148, 57], [50, 95, 1], []], ![[65, 11, 36, 96], [54, 157], [114, 80, 29, 159], [99, 166, 105, 60], [68, 158], [4, 96, 39, 109], [131, 124]], ![[61, 105, 159, 10], [80, 34], [146, 21, 7, 73], [67, 86, 166, 118], [115, 88], [132, 61, 64, 47], [40, 124]]]
 h' := ![![[50, 109, 41], [57, 15, 119], [74, 121, 157], [115, 115, 9], [69, 26, 72], [111, 171, 149], [0, 0, 1], [0, 1]], ![[45, 63, 132], [156, 166, 154], [126, 3, 147], [5, 122, 92], [161, 64, 66], [10, 71, 136], [137, 24, 63], [50, 109, 41]], ![[0, 1], [144, 165, 73], [1, 49, 42], [25, 109, 72], [120, 83, 35], [48, 104, 61], [107, 149, 109], [45, 63, 132]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [145, 109], []]
 b := ![[], [85, 75, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [22, 152, 78, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3632827, 1372063, 251196]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![20999, 7931, 1452]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 5177717 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def PBC173 : ContainsPrimesAboveP 173 ![I173N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI173N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![173, 0, 0]]) timesTableT_eq_Table B_one_repr 173 (by decide) 𝕀

instance hp179 : Fact (Nat.Prime 179) := {out := by norm_num}

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2017, -842, -195]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![-2017, -842, -195]] 
 ![![179, 0, 0], ![0, 179, 0], ![3, 75, 1]] where
  M :=![![![-2017, -842, -195], ![-26910, -10987, -2526], ![-116196, -47702, -10987]]]
  hmulB := by decide  
  f := ![![![-1223, -284, 87]], ![![12006, 2779, -852]], ![![4791, 1109, -340]]]
  g := ![![![-8, 77, -195], ![-108, 997, -2526], ![-465, 4337, -10987]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [149, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [175, 178], [0, 1]]
 g := ![![[155, 173], [53, 70], [66], [15], [8, 45], [54, 16], [1]], ![[0, 6], [131, 109], [66], [15], [7, 134], [169, 163], [1]]]
 h' := ![![[175, 178], [158, 129], [63, 41], [54, 31], [61, 146], [9, 90], [30, 175], [0, 1]], ![[0, 1], [0, 50], [78, 138], [109, 148], [14, 33], [7, 89], [46, 4], [175, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [100]]
 b := ![[], [100, 50]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [149, 4, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-682, -224, 71]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5, -31, 71]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1223, 284, -87]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![1223, 284, -87]] 
 ![![179, 0, 0], ![133, 1, 0], ![130, 0, 1]] where
  M :=![![![1223, 284, -87], ![-12006, -2779, 852], ![39192, 9062, -2779]]]
  hmulB := by decide  
  f := ![![![2017, 842, 195]], ![![1649, 687, 159]], ![![2114, 878, 203]]]
  g := ![![![-141, 284, -87], ![1379, -2779, 852], ![-4496, 9062, -2779]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![-2017, -842, -195]] ![![1223, 284, -87]]
  ![![179, 0, 0]] where
 M := ![![![-179, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC179 : ContainsPrimesAboveP 179 ![I179N0, I179N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI179N0
    exact isPrimeI179N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 179 (by decide) (𝕀 ⊙ MulI179N0)


lemma PB180I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 179 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 179 (by omega)

def PB180I3 : PrimesBelowBoundCertificateInterval O 137 179 180 where
  m := 8
  g := ![1, 2, 2, 2, 3, 2, 1, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179]
  hP := PB180I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0]
    · exact ![I149N0, I149N1]
    · exact ![I151N0, I151N1]
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1, I163N2]
    · exact ![I167N0, I167N1]
    · exact ![I173N0]
    · exact ![I179N0, I179N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC139
    · exact PBC149
    · exact PBC151
    · exact PBC157
    · exact PBC163
    · exact PBC167
    · exact PBC173
    · exact PBC179
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2685619]
    · exact ![22201, 149]
    · exact ![22801, 151]
    · exact ![24649, 157]
    · exact ![163, 163, 163]
    · exact ![27889, 167]
    · exact ![5177717]
    · exact ![32041, 179]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
      exact NI157N1
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
      exact NI163N1
      exact NI163N2
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
      exact NI179N1
  β := ![I149N1, I151N1, I157N1, I163N0, I163N1, I163N2, I167N1, I179N1]
  Il := ![[], [I149N1], [I151N1], [I157N1], [I163N0, I163N1, I163N2], [I167N1], [], [I179N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
