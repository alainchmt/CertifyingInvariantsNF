
import IdealArithmetic.Examples.NF3_1_406700_2.RI3_1_406700_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![1, 1, 0]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0], ![1, 1, 0]] 
 ![![2, 0, 0], ![1, 1, 0], ![1, 0, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![1, 1, 0], ![1, 0, 5], ![-67, -24, 3]]]
  hmulB := by decide  
  f := ![![![0, 0, -5], ![0, 2, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, -2], ![0, 1, 0]]]
  g := ![![![1, 0, 0], ![-1, 2, 0], ![-1, 0, 2]], ![![0, 1, 0], ![-2, 0, 5], ![-23, -24, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![2, 0, 0], ![1, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![2, 0, 0], ![16, -1, 1]] where
 M := ![![![4, 0, 0], ![2, 2, 0]], ![![2, 2, 0], ![2, 1, 5]]]
 hmul := by decide  
 g := ![![![![2, 0, 0], ![0, 0, 0]], ![![-15, 2, -1], ![2, 0, 0]]], ![![![-15, 2, -1], ![2, 0, 0]], ![![-7, 1, 2], ![1, 0, 0]]]]
 hle2 := by decide  
def MulI2N1 : IdealMulLeCertificate' Table 
  ![![2, 0, 0], ![16, -1, 1]] ![![2, 0, 0], ![1, 1, 0]]
  ![![2, 0, 0]] where
 M := ![![![4, 0, 0], ![2, 2, 0]], ![![32, -2, 2], ![-52, -8, -2]]]
 hmul := by decide  
 g := ![![![![2, 0, 0]], ![![1, 1, 0]]], ![![![16, -1, 1]], ![![-26, -4, -1]]]]
 hle2 := by decide  

def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N0, I2N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N0
    exact isPrimeI2N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1)
instance hp3 : Fact (Nat.Prime 3) := {out := by norm_num}

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0]] 
 ![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P3P0 : CertificateIrreducibleZModOfList' 3 3 2 1 [2, 2, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 1, 1], [0, 1, 2], [0, 1]]
 g := ![![[1]], ![[2, 2, 1, 1]], ![[0, 1, 2, 2]]]
 h' := ![![[1, 1, 1], [0, 1]], ![[0, 1, 2], [1, 1, 1]], ![[0, 1], [0, 1, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 2], []]
 b := ![[], [1, 2, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : CertifiedPrimeIdeal' SI3N0 3 where
  n := 3
  hpos := by decide
  P := [2, 2, 2, 1]
  hirr := P3P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-320874, -134550, -54180]
  a := ![-1, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-106958, -44850, -18060]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N0 B_one_repr
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 27 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N0

def PBC3 : ContainsPrimesAboveP 3 ![I3N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![3, 0, 0]]) timesTableT_eq_Table B_one_repr 3 (by decide) 𝕀


def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![16, -1, 1]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![5, 0, 0], ![16, -1, 1]] 
 ![![5, 0, 0], ![3, 1, 0], ![4, 0, 1]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![16, -1, 1], ![-68, -7, -3], ![22, 1, -9]]]
  hmulB := by decide  
  f := ![![![17, 18, -82], ![50, 0, -40]], ![![11, 10, -45], ![27, 0, -22]], ![![4, 15, -66], ![43, 0, -32]]]
  g := ![![![1, 0, 0], ![-3, 5, 0], ![-4, 0, 5]], ![![3, -1, 1], ![-7, -7, -3], ![11, 1, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![5, 0, 0], ![16, -1, 1]] ![![5, 0, 0], ![16, -1, 1]]
  ![![5, 0, 0], ![-2, 1, 0]] where
 M := ![![![25, 0, 0], ![80, -5, 5]], ![![80, -5, 5], ![346, -8, 10]]]
 hmul := by decide  
 g := ![![![![5, 0, 0], ![0, 0, 0]], ![![14, 0, 1], ![-5, 0, 0]]], ![![![14, 0, 1], ![-5, 0, 0]], ![![60, 3, 2], ![-23, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![5, 0, 0], ![-2, 1, 0]] ![![5, 0, 0], ![16, -1, 1]]
  ![![5, 0, 0]] where
 M := ![![![25, 0, 0], ![80, -5, 5]], ![![-10, 5, 0], ![-100, -5, -5]]]
 hmul := by decide  
 g := ![![![![5, 0, 0]], ![![16, -1, 1]]], ![![![-2, 1, 0]], ![![-20, -1, -1]]]]
 hle2 := by decide  

def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N0, I5N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0 ⊙ MulI5N1)

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![2, 1, 0]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0], ![2, 1, 0]] 
 ![![7, 0, 0], ![2, 1, 0], ![4, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![2, 1, 0], ![1, 1, 5], ![-67, -24, 4]]]
  hmulB := by decide  
  f := ![![![-17, -19, -100], ![-7, 140, 0]], ![![-5, -5, -25], ![1, 35, 0]], ![![-10, -11, -57], ![-3, 80, 0]]]
  g := ![![![1, 0, 0], ![-2, 7, 0], ![-4, 0, 7]], ![![0, 1, 0], ![-3, 1, 5], ![-5, -24, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N0)

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := prime_ideal_of_norm_prime hp7.out _ NI7N0
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![7, 0, 0], ![2, 1, 0]] ![![7, 0, 0], ![2, 1, 0]]
  ![![7, 0, 0], ![15, 2, 1]] where
 M := ![![![49, 0, 0], ![14, 7, 0]], ![![14, 7, 0], ![5, 3, 5]]]
 hmul := by decide  
 g := ![![![![-8, -2, -1], ![7, 0, 0]], ![![-13, -1, -1], ![7, 0, 0]]], ![![![-13, -1, -1], ![7, 0, 0]], ![![-10, -1, 0], ![5, 0, 0]]]]
 hle2 := by decide  
def MulI7N1 : IdealMulLeCertificate' Table 
  ![![7, 0, 0], ![15, 2, 1]] ![![7, 0, 0], ![2, 1, 0]]
  ![![7, 0, 0]] where
 M := ![![![49, 0, 0], ![14, 7, 0]], ![![105, 14, 7], ![-35, -7, 14]]]
 hmul := by decide  
 g := ![![![![7, 0, 0]], ![![2, 1, 0]]], ![![![15, 2, 1]], ![![-5, -1, 2]]]]
 hle2 := by decide  

def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N0, I7N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N0
    exact isPrimeI7N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0 ⊙ MulI7N1)
instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0]] 
 ![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [8, 2, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 3, 6], [3, 7, 5], [0, 1]]
 g := ![![[3], [10, 1, 1], []], ![[0, 6, 3, 10], [3, 7, 6, 8], [6, 3]], ![[10, 8, 3, 1], [6, 4, 8, 1], [7, 3]]]
 h' := ![![[9, 3, 6], [8, 5], [0, 0, 1], [0, 1]], ![[3, 7, 5], [9, 4, 8], [0, 7, 7], [9, 3, 6]], ![[0, 1], [1, 2, 3], [8, 4, 3], [3, 7, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 5], []]
 b := ![[], [2, 2, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [8, 2, 10, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![616396, 413578, 733414]
  a := ![2, -5, 11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![56036, 37598, 66674]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 1331 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def PBC11 : ContainsPrimesAboveP 11 ![I11N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![11, 0, 0]]) timesTableT_eq_Table B_one_repr 11 (by decide) 𝕀

instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![17, -6, 1]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0], ![17, -6, 1]] 
 ![![13, 0, 0], ![0, 13, 0], ![4, 7, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![17, -6, 1], ![-73, -1, -28], ![357, 121, -18]]]
  hmulB := by decide  
  f := ![![![-16, 6, -1], ![13, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![-1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-4, -7, 13]], ![![1, -1, 1], ![3, 15, -28], ![33, 19, -18]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [12, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 12], [0, 1]]
 g := ![![[9, 12], [3], [9, 1]], ![[0, 1], [3], [5, 12]]]
 h' := ![![[9, 12], [6, 8], [9, 4], [0, 1]], ![[0, 1], [0, 5], [6, 9], [9, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [5, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 2
  hpos := by decide
  P := [12, 4, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2991516, -1541983, -1535965]
  a := ![-65, 2, -261]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![242488, 708444, -1535965]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![2, 1, 0]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![13, 0, 0], ![2, 1, 0]] 
 ![![13, 0, 0], ![2, 1, 0], ![5, 0, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![2, 1, 0], ![1, 1, 5], ![-67, -24, 4]]]
  hmulB := by decide  
  f := ![![![-74, -76, -385], ![-13, 1001, 0]], ![![-11, -11, -55], ![1, 143, 0]], ![![-30, -30, -148], ![5, 385, 0]]]
  g := ![![![1, 0, 0], ![-2, 13, 0], ![-5, 0, 13]], ![![0, 1, 0], ![-2, 1, 5], ![-3, -24, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![13, 0, 0], ![17, -6, 1]] ![![13, 0, 0], ![2, 1, 0]]
  ![![13, 0, 0]] where
 M := ![![![169, 0, 0], ![26, 13, 0]], ![![221, -78, 13], ![-39, -13, -26]]]
 hmul := by decide  
 g := ![![![![13, 0, 0]], ![![2, 1, 0]]], ![![![17, -6, 1]], ![![-3, -1, -2]]]]
 hle2 := by decide  


def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 13 (by decide) (𝕀 ⊙ MulI13N0)
instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0]] 
 ![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [14, 15, 12, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 9, 13], [8, 7, 4], [0, 1]]
 g := ![![[16, 3, 4], [12, 15], [5, 1], []], ![[10, 5, 7, 15], [14, 1], [11, 15], [8, 16]], ![[10, 15, 3, 4], [4, 2], [4, 13], [0, 16]]]
 h' := ![![[14, 9, 13], [6, 0, 15], [15, 13, 10], [0, 0, 1], [0, 1]], ![[8, 7, 4], [8, 14, 3], [0, 13, 1], [16, 10, 7], [14, 9, 13]], ![[0, 1], [14, 3, 16], [11, 8, 6], [13, 7, 9], [8, 7, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 7], []]
 b := ![[], [12, 3, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [14, 15, 12, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1159774, -632961, -772225]
  a := ![-2, 4, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-68222, -37233, -45425]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 4913 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def PBC17 : ContainsPrimesAboveP 17 ![I17N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![17, 0, 0]]) timesTableT_eq_Table B_one_repr 17 (by decide) 𝕀

instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![12, 2, 1]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0], ![12, 2, 1]] 
 ![![19, 0, 0], ![0, 19, 0], ![12, 2, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![12, 2, 1], ![-65, -14, 12], ![-179, -71, -7]]]
  hmulB := by decide  
  f := ![![![-11, -2, -1], ![19, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-12, -2, 19]], ![![0, 0, 1], ![-11, -2, 12], ![-5, -3, -7]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [3, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 18], [0, 1]]
 g := ![![[10, 16], [16, 7], [7], [1]], ![[5, 3], [15, 12], [7], [1]]]
 h' := ![![[8, 18], [9, 4], [7, 8], [16, 8], [0, 1]], ![[0, 1], [3, 15], [14, 11], [4, 11], [8, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [6, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [3, 11, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1132, -575, -620]
  a := ![-1, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![332, 35, -620]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![7, 1, 0]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![19, 0, 0], ![7, 1, 0]] 
 ![![19, 0, 0], ![7, 1, 0], ![7, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![7, 1, 0], ![1, 6, 5], ![-67, -24, 9]]]
  hmulB := by decide  
  f := ![![![-36, -263, -220], ![-19, 836, 0]], ![![-16, -96, -80], ![1, 304, 0]], ![![-14, -97, -81], ![-5, 308, 0]]]
  g := ![![![1, 0, 0], ![-7, 19, 0], ![-7, 0, 19]], ![![0, 1, 0], ![-4, 6, 5], ![2, -24, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![19, 0, 0], ![12, 2, 1]] ![![19, 0, 0], ![7, 1, 0]]
  ![![19, 0, 0]] where
 M := ![![![361, 0, 0], ![133, 19, 0]], ![![228, 38, 19], ![19, 0, 19]]]
 hmul := by decide  
 g := ![![![![19, 0, 0]], ![![7, 1, 0]]], ![![![12, 2, 1]], ![![1, 0, 1]]]]
 hle2 := by decide  


def PBC19 : ContainsPrimesAboveP 19 ![I19N0, I19N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 19 (by decide) (𝕀 ⊙ MulI19N0)
instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![7, 1, 0]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0], ![7, 1, 0]] 
 ![![23, 0, 0], ![7, 1, 0], ![1, 0, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![7, 1, 0], ![1, 6, 5], ![-67, -24, 9]]]
  hmulB := by decide  
  f := ![![![-52, -359, -300], ![-23, 1380, 0]], ![![-18, -108, -90], ![1, 414, 0]], ![![-5, -16, -13], ![8, 60, 0]]]
  g := ![![![1, 0, 0], ![-7, 23, 0], ![-1, 0, 23]], ![![0, 1, 0], ![-2, 6, 5], ![4, -24, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N0 : Nat.card (O ⧸ I23N0) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N0)

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := prime_ideal_of_norm_prime hp23.out _ NI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![-6, 1, 0]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![23, 0, 0], ![-6, 1, 0]] 
 ![![23, 0, 0], ![17, 1, 0], ![1, 0, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![-6, 1, 0], ![1, -7, 5], ![-67, -24, -4]]]
  hmulB := by decide  
  f := ![![![250, -1989, 1425], ![-138, -6555, 0]], ![![187, -1466, 1050], ![-91, -4830, 0]], ![![14, -87, 62], ![6, -285, 0]]]
  g := ![![![1, 0, 0], ![-17, 23, 0], ![-1, 0, 23]], ![![-1, 1, 0], ![5, -7, 5], ![15, -24, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1

def I23N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![-2, 1, 0]] i)))

def SI23N2: IdealEqSpanCertificate' Table ![![23, 0, 0], ![-2, 1, 0]] 
 ![![23, 0, 0], ![21, 1, 0], ![22, 0, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![-2, 1, 0], ![1, -3, 5], ![-67, -24, 0]]]
  hmulB := by decide  
  f := ![![![-52, 164, -275], ![23, 1265, 0]], ![![-47, 149, -250], ![24, 1150, 0]], ![![-50, 157, -263], ![19, 1210, 0]]]
  g := ![![![1, 0, 0], ![-21, 23, 0], ![-22, 0, 23]], ![![-1, 1, 0], ![-2, -3, 5], ![19, -24, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N2 : Nat.card (O ⧸ I23N2) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N2)

lemma isPrimeI23N2 : Ideal.IsPrime I23N2 := prime_ideal_of_norm_prime hp23.out _ NI23N2
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![23, 0, 0], ![7, 1, 0]] ![![23, 0, 0], ![-6, 1, 0]]
  ![![23, 0, 0], ![24, 0, 1]] where
 M := ![![![529, 0, 0], ![-138, 23, 0]], ![![161, 23, 0], ![-41, 0, 5]]]
 hmul := by decide  
 g := ![![![![-1, 0, -1], ![23, 0, 0]], ![![-6, 1, 0], ![0, 0, 0]]], ![![![-17, 1, -1], ![23, 0, 0]], ![![-7, 0, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI23N1 : IdealMulLeCertificate' Table 
  ![![23, 0, 0], ![24, 0, 1]] ![![23, 0, 0], ![-2, 1, 0]]
  ![![23, 0, 0]] where
 M := ![![![529, 0, 0], ![-46, 23, 0]], ![![552, 0, 23], ![-115, 0, 0]]]
 hmul := by decide  
 g := ![![![![23, 0, 0]], ![![-2, 1, 0]]], ![![![24, 0, 1]], ![![-5, 0, 0]]]]
 hle2 := by decide  


def PBC23 : ContainsPrimesAboveP 23 ![I23N0, I23N1, I23N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
    exact isPrimeI23N1
    exact isPrimeI23N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 23 (by decide) (𝕀 ⊙ MulI23N0 ⊙ MulI23N1)
instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![-13, 1, 0]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0], ![-13, 1, 0]] 
 ![![29, 0, 0], ![16, 1, 0], ![16, 0, 1]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![-13, 1, 0], ![1, -14, 5], ![-67, -24, -11]]]
  hmulB := by decide  
  f := ![![![305, -6428, 2300], ![-348, -13340, 0]], ![![176, -3536, 1265], ![-173, -7337, 0]], ![![175, -3547, 1269], ![-177, -7360, 0]]]
  g := ![![![1, 0, 0], ![-16, 29, 0], ![-16, 0, 29]], ![![-1, 1, 0], ![5, -14, 5], ![17, -24, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N0 : Nat.card (O ⧸ I29N0) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N0)

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := prime_ideal_of_norm_prime hp29.out _ NI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![-10, 1, 0]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![29, 0, 0], ![-10, 1, 0]] 
 ![![29, 0, 0], ![19, 1, 0], ![13, 0, 1]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![-10, 1, 0], ![1, -11, 5], ![-67, -24, -8]]]
  hmulB := by decide  
  f := ![![![369, -5138, 2340], ![-290, -13572, 0]], ![![247, -3360, 1530], ![-173, -8874, 0]], ![![173, -2304, 1049], ![-108, -6084, 0]]]
  g := ![![![1, 0, 0], ![-19, 29, 0], ![-13, 0, 29]], ![![-1, 1, 0], ![5, -11, 5], ![17, -24, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1

def I29N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![25, -1, 1]] i)))

def SI29N2: IdealEqSpanCertificate' Table ![![25, -1, 1]] 
 ![![29, 0, 0], ![22, 1, 0], ![18, 0, 1]] where
  M :=![![![25, -1, 1], ![-68, 2, -3], ![22, 1, 0]]]
  hmulB := by decide  
  f := ![![![3, 1, 1]], ![![0, 0, 1]], ![![-2, -1, 0]]]
  g := ![![![1, -1, 1], ![-2, 2, -3], ![0, 1, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N2 : Nat.card (O ⧸ I29N2) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N2)

lemma isPrimeI29N2 : Ideal.IsPrime I29N2 := prime_ideal_of_norm_prime hp29.out _ NI29N2
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![29, 0, 0], ![-13, 1, 0]] ![![29, 0, 0], ![-10, 1, 0]]
  ![![3, 1, 1]] where
 M := ![![![841, 0, 0], ![-290, 29, 0]], ![![-377, 29, 0], ![131, -24, 5]]]
 hmul := by decide  
 g := ![![![![725, -29, 29]], ![![-318, 12, -13]]], ![![![-393, 15, -16]], ![![173, -6, 7]]]]
 hle2 := by decide  

def MulI29N1 : IdealMulLeCertificate' Table 
  ![![3, 1, 1]] ![![25, -1, 1]]
  ![![29, 0, 0]] where
 M := ![![![29, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC29 : ContainsPrimesAboveP 29 ![I29N0, I29N1, I29N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N1
    exact isPrimeI29N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 29 (by decide) (𝕀 ⊙ MulI29N0 ⊙ MulI29N1)
instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0]] 
 ![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 3 2 4 [17, 15, 27, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [25, 24, 23], [10, 6, 8], [0, 1]]
 g := ![![[4, 28, 25], [26, 6, 20], [28, 6, 16], [1]], ![[4, 21, 30, 11], [15, 25, 2, 13], [21, 28, 30, 24], [26, 30, 18, 15]], ![[29, 27, 4, 5], [21, 24, 14, 14], [3, 18, 7, 20], [18, 30, 7, 16]]]
 h' := ![![[25, 24, 23], [23, 1, 26], [20, 15, 12], [14, 16, 4], [0, 1]], ![[10, 6, 8], [24, 1, 24], [0, 6, 14], [24, 18, 20], [25, 24, 23]], ![[0, 1], [3, 29, 12], [25, 10, 5], [12, 28, 7], [10, 6, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 8], []]
 b := ![[], [29, 7, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 3
  hpos := by decide
  P := [17, 15, 27, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4350106, 1295676, -1355940]
  a := ![2, 18, 9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![140326, 41796, -43740]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 29791 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def PBC31 : ContainsPrimesAboveP 31 ![I31N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![31, 0, 0]]) timesTableT_eq_Table B_one_repr 31 (by decide) 𝕀



lemma PB181I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB181I0 : PrimesBelowBoundCertificateInterval O 1 31 181 where
  m := 11
  g := ![3, 1, 3, 3, 1, 2, 1, 2, 3, 3, 1]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB181I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N0, I2N0]
    · exact ![I3N0]
    · exact ![I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N0, I7N0]
    · exact ![I11N0]
    · exact ![I13N0, I13N1]
    · exact ![I17N0]
    · exact ![I19N0, I19N1]
    · exact ![I23N0, I23N1, I23N2]
    · exact ![I29N0, I29N1, I29N2]
    · exact ![I31N0]
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
    · exact ![27]
    · exact ![5, 5, 5]
    · exact ![7, 7, 7]
    · exact ![1331]
    · exact ![169, 13]
    · exact ![4913]
    · exact ![361, 19]
    · exact ![23, 23, 23]
    · exact ![29, 29, 29]
    · exact ![29791]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N0
      exact NI2N0
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N0
      exact NI5N0
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N0
      exact NI7N0
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
      exact NI23N2
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
      exact NI29N2
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
  β := ![I2N0, I3N0, I5N0, I7N0, I13N0, I13N1, I19N1, I23N0, I23N1, I23N2, I29N0, I29N1, I29N2]
  Il := ![[I2N0, I2N0, I2N0], [I3N0], [I5N0, I5N0, I5N0], [I7N0, I7N0, I7N0], [], [I13N0, I13N1], [], [I19N1], [I23N0, I23N1, I23N2], [I29N0, I29N1, I29N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
