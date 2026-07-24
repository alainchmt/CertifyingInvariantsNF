
import IdealArithmetic.Examples.NF3_1_132328_2.RI3_1_132328_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 1, 0]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0], ![0, 1, 0]] 
 ![![2, 0, 0], ![0, 1, 0], ![1, 0, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![0, 1, 0], ![0, 1, 2], ![55, -19, -1]]]
  hmulB := by decide  
  f := ![![![56, -16, -1], ![-6, 0, -2]], ![![0, 0, 0], ![1, 0, 0]], ![![28, -8, 0], ![-3, 0, -1]]]
  g := ![![![1, 0, 0], ![0, 2, 0], ![-1, 0, 2]], ![![0, 1, 0], ![-1, 1, 2], ![28, -19, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![12, 2, 1]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![2, 0, 0], ![12, 2, 1]] 
 ![![2, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![12, 2, 1], ![55, -5, 3], ![55, -1, -8]]]
  hmulB := by decide  
  f := ![![![-4, -15, -2], ![10, -2, 0]], ![![-2, -7, -1], ![5, -1, 0]], ![![-6, -1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![-1, 2, 0], ![0, 0, 2]], ![![5, 2, 1], ![30, -5, 3], ![28, -1, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![2, 0, 0], ![0, 1, 0]] ![![2, 0, 0], ![12, 2, 1]]
  ![![2, 0, 0], ![13, 1, 1]] where
 M := ![![![4, 0, 0], ![24, 4, 2]], ![![0, 2, 0], ![55, -5, 3]]]
 hmul := by decide  
 g := ![![![![-11, -1, -1], ![2, 0, 0]], ![![-1, 1, 0], ![2, 0, 0]]], ![![![0, 1, 0], ![0, 0, 0]], ![![-5, -5, -1], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![2, 0, 0], ![13, 1, 1]] ![![2, 0, 0], ![12, 2, 1]]
  ![![2, 0, 0]] where
 M := ![![![4, 0, 0], ![24, 4, 2]], ![![26, 2, 2], ![266, 20, 8]]]
 hmul := by decide  
 g := ![![![![2, 0, 0]], ![![12, 2, 1]]], ![![![13, 1, 1]], ![![133, 10, 4]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N1, I2N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
    exact isPrimeI2N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1)
instance hp3 : Fact (Nat.Prime 3) := {out := by norm_num}

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, -46, 8]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![101, -46, 8]] 
 ![![3, 0, 0], ![0, 3, 0], ![1, 1, 1]] where
  M :=![![![101, -46, 8], ![440, -97, -100], ![-2970, 1170, 3]]]
  hmulB := by decide  
  f := ![![![38903, 3166, 1792]], ![![98560, 8021, 4540]], ![![71011, 5779, 3271]]]
  g := ![![![31, -18, 8], ![180, 1, -100], ![-991, 389, 3]]]
  hle1 := by decide   
  hle2 := by decide  


def P3P0 : CertificateIrreducibleZModOfList' 3 2 2 1 [2, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 2], [0, 1]]
 g := ![![[2, 1]], ![[1, 2]]]
 h' := ![![[2, 2], [0, 1]], ![[0, 1], [2, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [1, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : CertifiedPrimeIdeal' SI3N0 3 where
  n := 2
  hpos := by decide
  P := [2, 1, 1]
  hirr := P3P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![167, 107, -169]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![112, 92, -169]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N0 B_one_repr
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 9 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![38903, 3166, 1792]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![38903, 3166, 1792]] 
 ![![3, 0, 0], ![2, 1, 0], ![0, 0, 1]] where
  M :=![![![38903, 3166, 1792], ![98560, 8021, 4540], ![75570, 6150, 3481]]]
  hmulB := by decide  
  f := ![![![101, -46, 8]], ![![214, -63, -28]], ![![-990, 390, 1]]]
  g := ![![![10857, 3166, 1792], ![27506, 8021, 4540], ![21090, 6150, 3481]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![101, -46, 8]] ![![38903, 3166, 1792]]
  ![![3, 0, 0]] where
 M := ![![![3, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0)
instance hp5 : Fact (Nat.Prime 5) := {out := by norm_num}

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![125, 12, -80]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![125, 12, -80]] 
 ![![5, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![125, 12, -80], ![-4400, 1657, 104], ![5060, -3188, 1553]]]
  hmulB := by decide  
  f := ![![![2904873, 236404, 133808]], ![![1471888, 119785, 67800]], ![![1128556, 91844, 51985]]]
  g := ![![![25, 12, -80], ![-880, 1657, 104], ![1012, -3188, 1553]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2904873, -236404, -133808]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![-2904873, -236404, -133808]] 
 ![![5, 0, 0], ![0, 5, 0], ![1, 3, 1]] where
  M :=![![![-2904873, -236404, -133808], ![-7359440, -598925, -339000], ![-5642780, -459220, -259925]]]
  hmulB := by decide  
  f := ![![![-125, -12, 80]], ![![4400, -1657, -104]], ![![1603, -359, -357]]]
  g := ![![![-554213, 33004, -133808], ![-1404088, 83615, -339000], ![-1076571, 64111, -259925]]]
  hle1 := by decide   
  hle2 := by decide  


def P5P1 : CertificateIrreducibleZModOfList' 5 2 2 2 [2, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 4], [0, 1]]
 g := ![![[], [1]], ![[], [1]]]
 h' := ![![[0, 4], [3], [0, 1]], ![[0, 1], [3], [0, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [0, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N1 : CertifiedPrimeIdeal' SI5N1 5 where
  n := 2
  hpos := by decide
  P := [2, 0, 1]
  hirr := P5P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-437, 439, -302]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-27, 269, -302]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI5N1 B_one_repr
lemma NI5N1 : Nat.card (O ⧸ I5N1) = 25 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI5N1
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![125, 12, -80]] ![![-2904873, -236404, -133808]]
  ![![5, 0, 0]] where
 M := ![![![-5, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0)

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![-3, 1, 0]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0], ![-3, 1, 0]] 
 ![![7, 0, 0], ![4, 1, 0], ![4, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![-3, 1, 0], ![0, -2, 2], ![55, -19, -4]]]
  hmulB := by decide  
  f := ![![![22, -7, 0], ![49, 0, 0]], ![![10, -3, 0], ![22, 0, 0]], ![![10, -2, -1], ![22, 4, 0]]]
  g := ![![![1, 0, 0], ![-4, 7, 0], ![-4, 0, 7]], ![![-1, 1, 0], ![0, -2, 2], ![21, -19, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N0)

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := prime_ideal_of_norm_prime hp7.out _ NI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![-2, 1, 0]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![7, 0, 0], ![-2, 1, 0]] 
 ![![7, 0, 0], ![5, 1, 0], ![6, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![-2, 1, 0], ![0, -1, 2], ![55, -19, -3]]]
  hmulB := by decide  
  f := ![![![3, 2, -6], ![7, 21, 0]], ![![1, 2, -4], ![1, 14, 0]], ![![2, 2, -5], ![4, 18, 0]]]
  g := ![![![1, 0, 0], ![-5, 7, 0], ![-6, 0, 7]], ![![-1, 1, 0], ![-1, -1, 2], ![24, -19, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![7, 0, 0], ![-3, 1, 0]] ![![7, 0, 0], ![-2, 1, 0]]
  ![![7, 0, 0], ![10, -2, 1]] where
 M := ![![![49, 0, 0], ![-14, 7, 0]], ![![-21, 7, 0], ![6, -4, 2]]]
 hmul := by decide  
 g := ![![![![-3, 2, -1], ![7, 0, 0]], ![![-2, 1, 0], ![0, 0, 0]]], ![![![-3, 1, 0], ![0, 0, 0]], ![![-2, 0, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI7N1 : IdealMulLeCertificate' Table 
  ![![7, 0, 0], ![10, -2, 1]] ![![7, 0, 0], ![-2, 1, 0]]
  ![![7, 0, 0]] where
 M := ![![![49, 0, 0], ![-14, 7, 0]], ![![70, -14, 7], ![35, -7, -7]]]
 hmul := by decide  
 g := ![![![![7, 0, 0]], ![![-2, 1, 0]]], ![![![10, -2, 1]], ![![5, -1, -1]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N1, I7N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N1
    exact isPrimeI7N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0 ⊙ MulI7N1)
instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![13, 6, 1]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0], ![13, 6, 1]] 
 ![![11, 0, 0], ![0, 11, 0], ![2, 6, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![13, 6, 1], ![55, 0, 11], ![275, -77, -11]]]
  hmulB := by decide  
  f := ![![![-12, -6, -1], ![11, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![-1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-2, -6, 11]], ![![1, 0, 1], ![3, -6, 11], ![27, -1, -11]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [6, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 10], [0, 1]]
 g := ![![[6, 1], [9, 9], [1]], ![[3, 10], [4, 2], [1]]]
 h' := ![![[8, 10], [1, 10], [5, 8], [0, 1]], ![[0, 1], [4, 1], [3, 3], [8, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [9, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 2
  hpos := by decide
  P := [6, 3, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3855, 37, 107]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![331, -55, 107]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![0, 1, 0]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![11, 0, 0], ![0, 1, 0]] 
 ![![11, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![0, 1, 0], ![0, 1, 2], ![55, -19, -1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, -1, -1], ![5, 6, 0]]]
  g := ![![![1, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![0, 1, 0], ![0, 1, 2], ![5, -19, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![11, 0, 0], ![13, 6, 1]] ![![11, 0, 0], ![0, 1, 0]]
  ![![11, 0, 0]] where
 M := ![![![121, 0, 0], ![0, 11, 0]], ![![143, 66, 11], ![55, 0, 11]]]
 hmul := by decide  
 g := ![![![![11, 0, 0]], ![![0, 1, 0]]], ![![![13, 6, 1]], ![![5, 0, 1]]]]
 hle2 := by decide  


def PBC11 : ContainsPrimesAboveP 11 ![I11N0, I11N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
    exact isPrimeI11N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 11 (by decide) (𝕀 ⊙ MulI11N0)
instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0]] 
 ![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [12, 4, 7, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 6, 12], [11, 6, 1], [0, 1]]
 g := ![![[8, 12, 12], [12, 10], [1]], ![[6, 4, 8, 4], [6, 1], [0, 5, 12, 12]], ![[11, 10, 12, 4], [4, 10], [6, 8, 11, 1]]]
 h' := ![![[8, 6, 12], [0, 6, 8], [1, 9, 6], [0, 1]], ![[11, 6, 1], [5, 3, 3], [5, 0, 1], [8, 6, 12]], ![[0, 1], [8, 4, 2], [11, 4, 6], [11, 6, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 10], []]
 b := ![[], [5, 3, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [12, 4, 7, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-229931, 124969, -45305]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-17687, 9613, -3485]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 2197 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def PBC13 : ContainsPrimesAboveP 13 ![I13N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![13, 0, 0]]) timesTableT_eq_Table B_one_repr 13 (by decide) 𝕀


def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![8, 1, 0]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0], ![8, 1, 0]] 
 ![![17, 0, 0], ![8, 1, 0], ![15, 0, 1]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]], ![![8, 1, 0], ![0, 9, 2], ![55, -19, 7]]]
  hmulB := by decide  
  f := ![![![105, 13, 0], ![-221, 0, 0]], ![![40, 5, 0], ![-84, 0, 0]], ![![87, 6, -1], ![-183, 9, 0]]]
  g := ![![![1, 0, 0], ![-8, 17, 0], ![-15, 0, 17]], ![![0, 1, 0], ![-6, 9, 2], ![6, -19, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N0 : Nat.card (O ⧸ I17N0) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N0)

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := prime_ideal_of_norm_prime hp17.out _ NI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![-4, 1, 0]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![17, 0, 0], ![-4, 1, 0]] 
 ![![17, 0, 0], ![13, 1, 0], ![11, 0, 1]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]], ![![-4, 1, 0], ![0, -3, 2], ![55, -19, -5]]]
  hmulB := by decide  
  f := ![![![61, -15, 0], ![255, 0, 0]], ![![49, -12, 0], ![205, 0, 0]], ![![39, -8, -1], ![163, 9, 0]]]
  g := ![![![1, 0, 0], ![-13, 17, 0], ![-11, 0, 17]], ![![-1, 1, 0], ![1, -3, 2], ![21, -19, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![17, 0, 0], ![8, 1, 0]] ![![17, 0, 0], ![-4, 1, 0]]
  ![![17, 0, 0], ![18, -6, 1]] where
 M := ![![![289, 0, 0], ![-68, 17, 0]], ![![136, 17, 0], ![-32, 5, 2]]]
 hmul := by decide  
 g := ![![![![-1, 6, -1], ![17, 0, 0]], ![![-4, 1, 0], ![0, 0, 0]]], ![![![-10, 7, -1], ![17, 0, 0]], ![![-4, 1, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI17N1 : IdealMulLeCertificate' Table 
  ![![17, 0, 0], ![18, -6, 1]] ![![17, 0, 0], ![-4, 1, 0]]
  ![![17, 0, 0]] where
 M := ![![![289, 0, 0], ![-68, 17, 0]], ![![306, -102, 17], ![-17, 17, -17]]]
 hmul := by decide  
 g := ![![![![17, 0, 0]], ![![-4, 1, 0]]], ![![![18, -6, 1]], ![![-1, 1, -1]]]]
 hle2 := by decide  


def PBC17 : ContainsPrimesAboveP 17 ![I17N0, I17N1, I17N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N1
    exact isPrimeI17N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 17 (by decide) (𝕀 ⊙ MulI17N0 ⊙ MulI17N1)
instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0]] 
 ![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 3 2 4 [1, 11, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 12, 9], [4, 6, 10], [0, 1]]
 g := ![![[7, 7, 16], [1, 12, 4], [16, 1], []], ![[6, 5, 14, 17], [16, 3, 9, 7], [12, 17], [11, 5]], ![[5, 11, 6, 2], [10, 14, 17, 13], [12, 11], [10, 5]]]
 h' := ![![[12, 12, 9], [18, 5, 15], [3, 13, 17], [0, 0, 1], [0, 1]], ![[4, 6, 10], [2, 1, 2], [7, 3, 10], [0, 10, 6], [12, 12, 9]], ![[0, 1], [14, 13, 2], [5, 3, 11], [6, 9, 12], [4, 6, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 18], []]
 b := ![[], [8, 7, 17], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 3
  hpos := by decide
  P := [1, 11, 3, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-26619, 18088, -10431]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1401, 952, -549]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 6859 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def PBC19 : ContainsPrimesAboveP 19 ![I19N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![19, 0, 0]]) timesTableT_eq_Table B_one_repr 19 (by decide) 𝕀

instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![15, 10, 1]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0], ![15, 10, 1]] 
 ![![23, 0, 0], ![0, 23, 0], ![15, 10, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![15, 10, 1], ![55, 6, 19], ![495, -153, -13]]]
  hmulB := by decide  
  f := ![![![-14, -10, -1], ![23, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-15, -10, 23]], ![![0, 0, 1], ![-10, -8, 19], ![30, -1, -13]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [9, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 22], [0, 1]]
 g := ![![[6, 18], [21, 6], [0, 18], [1]], ![[0, 5], [19, 17], [17, 5], [1]]]
 h' := ![![[15, 22], [18, 8], [0, 11], [14, 15], [0, 1]], ![[0, 1], [0, 15], [4, 12], [9, 8], [15, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [3, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 2
  hpos := by decide
  P := [9, 8, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![21963, 957, -7768]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![6021, 3419, -7768]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![4, 1, 0]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![23, 0, 0], ![4, 1, 0]] 
 ![![23, 0, 0], ![4, 1, 0], ![13, 0, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![4, 1, 0], ![0, 5, 2], ![55, -19, 3]]]
  hmulB := by decide  
  f := ![![![17, 4, 0], ![-92, 0, 0]], ![![-4, -1, 0], ![24, 0, 0]], ![![3, -2, -1], ![-14, 12, 0]]]
  g := ![![![1, 0, 0], ![-4, 23, 0], ![-13, 0, 23]], ![![0, 1, 0], ![-2, 5, 2], ![4, -19, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![23, 0, 0], ![15, 10, 1]] ![![23, 0, 0], ![4, 1, 0]]
  ![![23, 0, 0]] where
 M := ![![![529, 0, 0], ![92, 23, 0]], ![![345, 230, 23], ![115, 46, 23]]]
 hmul := by decide  
 g := ![![![![23, 0, 0]], ![![4, 1, 0]]], ![![![15, 10, 1]], ![![5, 2, 1]]]]
 hle2 := by decide  


def PBC23 : ContainsPrimesAboveP 23 ![I23N0, I23N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
    exact isPrimeI23N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 23 (by decide) (𝕀 ⊙ MulI23N0)
instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0]] 
 ![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 3 2 4 [25, 23, 11, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 2, 2], [16, 26, 27], [0, 1]]
 g := ![![[15, 14, 23], [9, 20], [5, 16, 5], [1]], ![[1, 7, 9, 11], [1, 23], [23, 14, 26, 19], [10, 17, 23, 8]], ![[5, 10, 1, 21], [11, 4], [11, 21, 12, 8], [12, 11, 23, 21]]]
 h' := ![![[2, 2, 2], [1, 10, 9], [20, 23, 22], [4, 6, 18], [0, 1]], ![[16, 26, 27], [8, 3, 22], [2, 27, 9], [19, 7, 16], [2, 2, 2]], ![[0, 1], [8, 16, 27], [14, 8, 27], [26, 16, 24], [16, 26, 27]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 6], []]
 b := ![[], [21, 25, 26], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 3
  hpos := by decide
  P := [25, 23, 11, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1363, 667, 232]
  a := ![-1, 2, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-47, 23, 8]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 24389 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def PBC29 : ContainsPrimesAboveP 29 ![I29N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![29, 0, 0]]) timesTableT_eq_Table B_one_repr 29 (by decide) 𝕀

instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19728, 9007, -21903]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![19728, 9007, -21903]] 
 ![![31, 0, 0], ![0, 31, 0], ![23, 30, 1]] where
  M :=![![![19728, 9007, -21903], ![-1204665, 444892, 39917], ![1700050, -981544, 404975]]]
  hmulB := by decide  
  f := ![![![-7075820308, -575843497, -325935545]], ![![-17926454975, -1458888450, -825751449]], ![![-23041369474, -1875149763, -1061361226]]]
  g := ![![![16887, 21487, -21903], ![-68476, -24278, 39917], ![-245625, -423574, 404975]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [17, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 30], [0, 1]]
 g := ![![[3, 14], [15, 25], [7, 28], [11, 1]], ![[2, 17], [11, 6], [5, 3], [22, 30]]]
 h' := ![![[11, 30], [24, 13], [5, 5], [30, 11], [0, 1]], ![[0, 1], [12, 18], [29, 26], [27, 20], [11, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [16, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [17, 20, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![292, 424, -362]
  a := ![0, 3, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![278, 364, -362]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7075820308, -575843497, -325935545]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![-7075820308, -575843497, -325935545]] 
 ![![31, 0, 0], ![3, 1, 0], ![25, 0, 1]] where
  M :=![![![-7075820308, -575843497, -325935545], ![-17926454975, -1458888450, -825751449], ![-13744937360, -1118588722, -633137001]]]
  hmulB := by decide  
  f := ![![![19728, 9007, -21903]], ![![-36951, 15223, -832]], ![![70750, -24399, -4600]]]
  g := ![![![90325768, -575843497, -325935545], ![228838600, -1458888450, -825751449], ![175459801, -1118588722, -633137001]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![19728, 9007, -21903]] ![![-7075820308, -575843497, -325935545]]
  ![![31, 0, 0]] where
 M := ![![![31, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0)


lemma PB103I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB103I0 : PrimesBelowBoundCertificateInterval O 1 31 103 where
  m := 11
  g := ![3, 2, 2, 3, 2, 1, 3, 1, 2, 1, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB103I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1]
    · exact ![I3N0, I3N1]
    · exact ![I5N0, I5N1]
    · exact ![I7N0, I7N1, I7N1]
    · exact ![I11N0, I11N1]
    · exact ![I13N0]
    · exact ![I17N0, I17N1, I17N1]
    · exact ![I19N0]
    · exact ![I23N0, I23N1]
    · exact ![I29N0]
    · exact ![I31N0, I31N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC2
    · exact PBC3
    · exact PBC5
    · exact PBC7
    · exact PBC11
    · exact PBC13
    · exact PBC17
    · exact PBC19
    · exact PBC23
    · exact PBC29
    · exact PBC31
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2, 2, 2]
    · exact ![9, 3]
    · exact ![5, 25]
    · exact ![7, 7, 7]
    · exact ![121, 11]
    · exact ![2197]
    · exact ![17, 17, 17]
    · exact ![6859]
    · exact ![529, 23]
    · exact ![24389]
    · exact ![961, 31]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N1
      exact NI2N1
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N1
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N1
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N1
      exact NI7N1
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
      exact NI17N1
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
  β := ![I2N0, I2N1, I3N0, I3N1, I5N0, I5N1, I7N0, I7N1, I11N1, I17N0, I17N1, I23N1, I31N1]
  Il := ![[I2N0, I2N1, I2N1], [I3N0, I3N1], [I5N0, I5N1], [I7N0, I7N1, I7N1], [I11N1], [], [I17N0, I17N1, I17N1], [], [I23N1], [], [I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
