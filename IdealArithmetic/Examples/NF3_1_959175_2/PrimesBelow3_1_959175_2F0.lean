
import IdealArithmetic.Examples.NF3_1_959175_2.RI3_1_959175_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp2 : Fact (Nat.Prime 2) := {out := by norm_num}

def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0]] 
 ![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P2P0 : CertificateIrreducibleZModOfList' 2 3 2 1 [1, 1, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 0, 1], [0, 1, 1], [0, 1]]
 g := ![![[]], ![[0, 1]], ![[0, 1]]]
 h' := ![![[0, 0, 1], [0, 1]], ![[0, 1, 1], [0, 0, 1]], ![[0, 1], [0, 1, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1], []]
 b := ![[], [1, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI2N0 : CertifiedPrimeIdeal' SI2N0 2 where
  n := 3
  hpos := by decide
  P := [1, 1, 0, 1]
  hirr := P2P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4984134, 502846, -233428]
  a := ![5, 1, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2492067, 251423, -116714]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI2N0 B_one_repr
lemma NI2N0 : Nat.card (O ⧸ I2N0) = 8 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI2N0

def PBC2 : ContainsPrimesAboveP 2 ![I2N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![2, 0, 0]]) timesTableT_eq_Table B_one_repr 2 (by decide) 𝕀


def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![0, 1, 0]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0], ![0, 1, 0]] 
 ![![3, 0, 0], ![0, 1, 0], ![1, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![0, 1, 0], ![-5, -2, 13], ![185, -8, 2]]]
  hmulB := by decide  
  f := ![![![1, 2, 0], ![-6, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![2, 0, -4], ![2, 1, 0]]]
  g := ![![![1, 0, 0], ![0, 3, 0], ![-1, 0, 3]], ![![0, 1, 0], ![-6, -2, 13], ![61, -8, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![0, 1, 0]] ![![3, 0, 0], ![0, 1, 0]]
  ![![3, 0, 0], ![4, 1, 1]] where
 M := ![![![9, 0, 0], ![0, 3, 0]], ![![0, 3, 0], ![-5, -2, 13]]]
 hmul := by decide  
 g := ![![![![-1, -1, -1], ![3, 0, 0]], ![![0, 1, 0], ![0, 0, 0]]], ![![![0, 1, 0], ![0, 0, 0]], ![![-3, -1, 4], ![1, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![4, 1, 1]] ![![3, 0, 0], ![0, 1, 0]]
  ![![3, 0, 0]] where
 M := ![![![9, 0, 0], ![0, 3, 0]], ![![12, 3, 3], ![180, -6, 15]]]
 hmul := by decide  
 g := ![![![![3, 0, 0]], ![![0, 1, 0]]], ![![![4, 1, 1]], ![![60, -2, 5]]]]
 hle2 := by decide  

def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N0, I3N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![0, 1, 0]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![5, 0, 0], ![0, 1, 0]] 
 ![![5, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![0, 1, 0], ![-5, -2, 13], ![185, -8, 2]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-3, -2, 8], ![4, -3, 0]]]
  g := ![![![1, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![0, 1, 0], ![-1, -2, 13], ![37, -8, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![5, 0, 0], ![0, 1, 0]] ![![5, 0, 0], ![0, 1, 0]]
  ![![5, 0, 0], ![5, 1, 1]] where
 M := ![![![25, 0, 0], ![0, 5, 0]], ![![0, 5, 0], ![-5, -2, 13]]]
 hmul := by decide  
 g := ![![![![5, 0, 0], ![0, 0, 0]], ![![-5, 0, -1], ![5, 0, 0]]], ![![![-5, 0, -1], ![5, 0, 0]], ![![1, 0, 3], ![-2, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![5, 0, 0], ![5, 1, 1]] ![![5, 0, 0], ![0, 1, 0]]
  ![![5, 0, 0]] where
 M := ![![![25, 0, 0], ![0, 5, 0]], ![![25, 5, 5], ![180, -5, 15]]]
 hmul := by decide  
 g := ![![![![5, 0, 0]], ![![0, 1, 0]]], ![![![5, 1, 1]], ![![36, -1, 3]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![0, 1, 0]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0], ![0, 1, 0]] 
 ![![7, 0, 0], ![0, 1, 0], ![5, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![0, 1, 0], ![-5, -2, 13], ![185, -8, 2]]]
  hmulB := by decide  
  f := ![![![-14, -6, 39], ![0, -21, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-10, -5, 28], ![5, -15, 0]]]
  g := ![![![1, 0, 0], ![0, 7, 0], ![-5, 0, 7]], ![![0, 1, 0], ![-10, -2, 13], ![25, -8, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N0)

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := prime_ideal_of_norm_prime hp7.out _ NI7N0
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![7, 0, 0], ![0, 1, 0]] ![![7, 0, 0], ![0, 1, 0]]
  ![![7, 0, 0], ![5, 2, 1]] where
 M := ![![![49, 0, 0], ![0, 7, 0]], ![![0, 7, 0], ![-5, -2, 13]]]
 hmul := by decide  
 g := ![![![![2, -2, -1], ![7, 0, 0]], ![![0, 1, 0], ![0, 0, 0]]], ![![![0, 1, 0], ![0, 0, 0]], ![![-5, -2, 1], ![6, 0, 0]]]]
 hle2 := by decide  
def MulI7N1 : IdealMulLeCertificate' Table 
  ![![7, 0, 0], ![5, 2, 1]] ![![7, 0, 0], ![0, 1, 0]]
  ![![7, 0, 0]] where
 M := ![![![49, 0, 0], ![0, 7, 0]], ![![35, 14, 7], ![175, -7, 28]]]
 hmul := by decide  
 g := ![![![![7, 0, 0]], ![![0, 1, 0]]], ![![![5, 2, 1]], ![![25, -1, 4]]]]
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


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [1, 5, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 5, 8], [4, 5, 3], [0, 1]]
 g := ![![[10, 4, 9], [9, 5, 1], []], ![[10, 10, 7, 6], [4, 2, 1, 2], [4, 9]], ![[4, 3], [8, 3, 3, 9], [9, 9]]]
 h' := ![![[1, 5, 8], [2, 5, 8], [0, 0, 1], [0, 1]], ![[4, 5, 3], [5, 5, 3], [8, 3, 5], [1, 5, 8]], ![[0, 1], [1, 1], [7, 8, 5], [4, 5, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 3], []]
 b := ![[], [9, 1, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [1, 5, 6, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![88306647, -7224536, 655853]
  a := ![-12, -7, 31]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![8027877, -656776, 59623]
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


def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![4, 1, 0]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0], ![4, 1, 0]] 
 ![![13, 0, 0], ![4, 1, 0], ![8, 0, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![4, 1, 0], ![-5, 2, 13], ![185, -8, 6]]]
  hmulB := by decide  
  f := ![![![1691, -120, 60], ![520, 0, -130]], ![![507, -36, 18], ![157, 0, -39]], ![![1040, -74, 37], ![322, 0, -80]]]
  g := ![![![1, 0, 0], ![-4, 13, 0], ![-8, 0, 13]], ![![0, 1, 0], ![-9, 2, 13], ![13, -8, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N0 : Nat.card (O ⧸ I13N0) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N0)

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := prime_ideal_of_norm_prime hp13.out _ NI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![9, 6, 1]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![13, 0, 0], ![9, 6, 1]] 
 ![![13, 0, 0], ![11, 1, 0], ![8, 0, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![9, 6, 1], ![155, -11, 80], ![1170, -35, 14]]]
  hmulB := by decide  
  f := ![![![1101, -410, 750], ![650, -130, 0]], ![![914, -341, 623], ![541, -108, 0]], ![![681, -250, 462], ![395, -80, 0]]]
  g := ![![![1, 0, 0], ![-11, 13, 0], ![-8, 0, 13]], ![![-5, 6, 1], ![-28, -11, 80], ![111, -35, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1

def I13N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![-1, 0, 1]] i)))

def SI13N2: IdealEqSpanCertificate' Table ![![13, 0, 0], ![-1, 0, 1]] 
 ![![13, 0, 0], ![11, 1, 0], ![12, 0, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![-1, 0, 1], ![185, -9, 2], ![60, 13, -8]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![44, -2, 0], ![6, -3, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![-11, 13, 0], ![-12, 0, 13]], ![![-1, 0, 1], ![20, -9, 2], ![1, 13, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N2 : Nat.card (O ⧸ I13N2) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N2)

lemma isPrimeI13N2 : Ideal.IsPrime I13N2 := prime_ideal_of_norm_prime hp13.out _ NI13N2
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![13, 0, 0], ![4, 1, 0]] ![![13, 0, 0], ![9, 6, 1]]
  ![![13, 0, 0], ![8, 0, 1]] where
 M := ![![![169, 0, 0], ![117, 78, 13]], ![![52, 13, 0], ![191, 13, 84]]]
 hmul := by decide  
 g := ![![![![5, 0, -1], ![13, 0, 0]], ![![1, 6, 0], ![13, 0, 0]]], ![![![-4, 1, -1], ![13, 0, 0]], ![![3, 1, 5], ![19, 0, 0]]]]
 hle2 := by decide  

def MulI13N1 : IdealMulLeCertificate' Table 
  ![![13, 0, 0], ![8, 0, 1]] ![![13, 0, 0], ![-1, 0, 1]]
  ![![13, 0, 0]] where
 M := ![![![169, 0, 0], ![-13, 0, 13]], ![![104, 0, 13], ![52, 13, 0]]]
 hmul := by decide  
 g := ![![![![13, 0, 0]], ![![-1, 0, 1]]], ![![![8, 0, 1]], ![![4, 1, 0]]]]
 hle2 := by decide  


def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N1, I13N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N1
    exact isPrimeI13N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 13 (by decide) (𝕀 ⊙ MulI13N0 ⊙ MulI13N1)
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


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [4, 4, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 2, 4], [12, 14, 13], [0, 1]]
 g := ![![[3, 4, 9], [15, 16], [0, 1], []], ![[2, 1, 1, 15], [8, 16], [2, 9], [16, 16]], ![[11, 12, 16, 16], [12, 13], [7, 4], [7, 16]]]
 h' := ![![[5, 2, 4], [8, 12, 3], [0, 13, 13], [0, 0, 1], [0, 1]], ![[12, 14, 13], [2, 6, 5], [0, 16, 13], [12, 11, 14], [5, 2, 4]], ![[0, 1], [7, 16, 9], [15, 5, 8], [14, 6, 2], [12, 14, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 9], []]
 b := ![[], [4, 6, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [4, 4, 0, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-362676655810, 34316339689, -11490859113]
  a := ![197, 67, -525]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-21333920930, 2018608217, -675932889]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![11, 2, 1]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0], ![11, 2, 1]] 
 ![![19, 0, 0], ![0, 19, 0], ![11, 2, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![11, 2, 1], ![175, -1, 28], ![430, -3, 8]]]
  hmulB := by decide  
  f := ![![![-10, -2, -1], ![19, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-11, -2, 19]], ![![0, 0, 1], ![-7, -3, 28], ![18, -1, 8]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [11, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 18], [0, 1]]
 g := ![![[7, 7], [18, 4], [1], [1]], ![[0, 12], [14, 15], [1], [1]]]
 h' := ![![[18, 18], [11, 11], [15, 2], [8, 18], [0, 1]], ![[0, 1], [0, 8], [13, 17], [9, 1], [18, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [4, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [11, 1, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11173, 15547, -7778]
  a := ![12, 6, -31]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3915, 1637, -7778]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![-9, 1, 0]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![19, 0, 0], ![-9, 1, 0]] 
 ![![19, 0, 0], ![10, 1, 0], ![11, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![-9, 1, 0], ![-5, -11, 13], ![185, -8, -7]]]
  hmulB := by decide  
  f := ![![![11, 22, -26], ![0, 38, 0]], ![![6, 11, -13], ![1, 19, 0]], ![![13, 12, -15], ![14, 22, 0]]]
  g := ![![![1, 0, 0], ![-10, 19, 0], ![-11, 0, 19]], ![![-1, 1, 0], ![-2, -11, 13], ![18, -8, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![19, 0, 0], ![11, 2, 1]] ![![19, 0, 0], ![-9, 1, 0]]
  ![![19, 0, 0]] where
 M := ![![![361, 0, 0], ![-171, 19, 0]], ![![209, 38, 19], ![76, -19, 19]]]
 hmul := by decide  
 g := ![![![![19, 0, 0]], ![![-9, 1, 0]]], ![![![11, 2, 1]], ![![4, -1, 1]]]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![0, 1, 0]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0], ![0, 1, 0]] 
 ![![23, 0, 0], ![0, 1, 0], ![12, 0, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![0, 1, 0], ![-5, -2, 13], ![185, -8, 2]]]
  hmulB := by decide  
  f := ![![![-69, -28, 182], ![0, -322, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-36, -15, 95], ![9, -168, 0]]]
  g := ![![![1, 0, 0], ![0, 23, 0], ![-12, 0, 23]], ![![0, 1, 0], ![-7, -2, 13], ![7, -8, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N0 : Nat.card (O ⧸ I23N0) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N0)

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := prime_ideal_of_norm_prime hp23.out _ NI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![13, -9, 1]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![23, 0, 0], ![13, -9, 1]] 
 ![![23, 0, 0], ![0, 23, 0], ![13, 14, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![13, -9, 1], ![230, 23, -115], ![-1605, 85, -12]]]
  hmulB := by decide  
  f := ![![![-12, 9, -1], ![23, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-13, -14, 23]], ![![0, -1, 1], ![75, 71, -115], ![-63, 11, -12]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P1 : CertificateIrreducibleZModOfList' 23 2 2 4 [21, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 22], [0, 1]]
 g := ![![[13, 18], [21, 1], [16, 9], [1]], ![[21, 5], [1, 22], [20, 14], [1]]]
 h' := ![![[3, 22], [19, 8], [9, 1], [2, 3], [0, 1]], ![[0, 1], [20, 15], [12, 22], [11, 20], [3, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [11, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N1 : CertifiedPrimeIdeal' SI23N1 23 where
  n := 2
  hpos := by decide
  P := [21, 20, 1]
  hirr := P23P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5471, 2433, -1612]
  a := ![5, 1, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1149, 1087, -1612]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N1 B_one_repr
lemma NI23N1 : Nat.card (O ⧸ I23N1) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![23, 0, 0], ![0, 1, 0]] ![![23, 0, 0], ![13, -9, 1]]
  ![![23, 0, 0]] where
 M := ![![![529, 0, 0], ![299, -207, 23]], ![![0, 23, 0], ![230, 23, -115]]]
 hmul := by decide  
 g := ![![![![23, 0, 0]], ![![13, -9, 1]]], ![![![0, 1, 0]], ![![10, 1, -5]]]]
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

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![9, 1, 0]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0], ![9, 1, 0]] 
 ![![29, 0, 0], ![9, 1, 0], ![26, 0, 1]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![9, 1, 0], ![-5, 7, 13], ![185, -8, 11]]]
  hmulB := by decide  
  f := ![![![113, -184, -338], ![58, 754, 0]], ![![31, -57, -104], ![30, 232, 0]], ![![101, -165, -303], ![53, 676, 0]]]
  g := ![![![1, 0, 0], ![-9, 29, 0], ![-26, 0, 29]], ![![0, 1, 0], ![-14, 7, 13], ![-1, -8, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N0 : Nat.card (O ⧸ I29N0) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N0)

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := prime_ideal_of_norm_prime hp29.out _ NI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![11, 1, 0]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![29, 0, 0], ![11, 1, 0]] 
 ![![29, 0, 0], ![11, 1, 0], ![21, 0, 1]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![11, 1, 0], ![-5, 9, 13], ![185, -8, 13]]]
  hmulB := by decide  
  f := ![![![466, -941, -1352], ![145, 3016, 0]], ![![173, -353, -507], ![59, 1131, 0]], ![![331, -682, -979], ![122, 2184, 0]]]
  g := ![![![1, 0, 0], ![-11, 29, 0], ![-21, 0, 29]], ![![0, 1, 0], ![-13, 9, 13], ![0, -8, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![29, 0, 0], ![9, 1, 0]] ![![29, 0, 0], ![9, 1, 0]]
  ![![29, 0, 0], ![17, -1, 1]] where
 M := ![![![841, 0, 0], ![261, 29, 0]], ![![261, 29, 0], ![76, 16, 13]]]
 hmul := by decide  
 g := ![![![![12, 1, -1], ![29, 0, 0]], ![![-8, 2, -1], ![29, 0, 0]]], ![![![-8, 2, -1], ![29, 0, 0]], ![![-5, 1, 0], ![13, 0, 0]]]]
 hle2 := by decide  
def MulI29N1 : IdealMulLeCertificate' Table 
  ![![29, 0, 0], ![17, -1, 1]] ![![29, 0, 0], ![11, 1, 0]]
  ![![29, 0, 0]] where
 M := ![![![841, 0, 0], ![319, 29, 0]], ![![493, -29, 29], ![377, 0, 0]]]
 hmul := by decide  
 g := ![![![![29, 0, 0]], ![![11, 1, 0]]], ![![![17, -1, 1]], ![![13, 0, 0]]]]
 hle2 := by decide  


def PBC29 : ContainsPrimesAboveP 29 ![I29N0, I29N0, I29N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N0
    exact isPrimeI29N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 29 (by decide) (𝕀 ⊙ MulI29N0 ⊙ MulI29N1)
instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![4, 8, 1]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0], ![4, 8, 1]] 
 ![![31, 0, 0], ![0, 31, 0], ![4, 8, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![4, 8, 1], ![145, -20, 106], ![1540, -51, 13]]]
  hmulB := by decide  
  f := ![![![-3, -8, -1], ![31, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-4, -8, 31]], ![![0, 0, 1], ![-9, -28, 106], ![48, -5, 13]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [10, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [25, 30], [0, 1]]
 g := ![![[13, 28], [19, 18], [25, 25], [25, 1]], ![[0, 3], [4, 13], [30, 6], [19, 30]]]
 h' := ![![[25, 30], [27, 20], [29, 7], [29, 26], [0, 1]], ![[0, 1], [0, 11], [18, 24], [28, 5], [25, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [17, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [10, 6, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![149526, -315, 1375]
  a := ![-8, 16, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4646, -365, 1375]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![-13, 1, 0]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![31, 0, 0], ![-13, 1, 0]] 
 ![![31, 0, 0], ![18, 1, 0], ![18, 0, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![-13, 1, 0], ![-5, -15, 13], ![185, -8, -11]]]
  hmulB := by decide  
  f := ![![![1011, 3430, -2964], ![-310, 7068, 0]], ![![596, 1985, -1716], ![-154, 4092, 0]], ![![595, 1991, -1721], ![-161, 4104, 0]]]
  g := ![![![1, 0, 0], ![-18, 31, 0], ![-18, 0, 31]], ![![-1, 1, 0], ![1, -15, 13], ![17, -8, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![31, 0, 0], ![4, 8, 1]] ![![31, 0, 0], ![-13, 1, 0]]
  ![![31, 0, 0]] where
 M := ![![![961, 0, 0], ![-403, 31, 0]], ![![124, 248, 31], ![93, -124, 93]]]
 hmul := by decide  
 g := ![![![![31, 0, 0]], ![![-13, 1, 0]]], ![![![4, 8, 1]], ![![3, -4, 3]]]]
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


lemma PB278I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB278I0 : PrimesBelowBoundCertificateInterval O 1 31 278 where
  m := 11
  g := ![1, 3, 3, 3, 1, 3, 1, 2, 2, 3, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB278I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0]
    · exact ![I3N0, I3N0, I3N0]
    · exact ![I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N0, I7N0]
    · exact ![I11N0]
    · exact ![I13N0, I13N1, I13N2]
    · exact ![I17N0]
    · exact ![I19N0, I19N1]
    · exact ![I23N0, I23N1]
    · exact ![I29N0, I29N0, I29N1]
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
    · exact ![8]
    · exact ![3, 3, 3]
    · exact ![5, 5, 5]
    · exact ![7, 7, 7]
    · exact ![1331]
    · exact ![13, 13, 13]
    · exact ![4913]
    · exact ![361, 19]
    · exact ![23, 529]
    · exact ![29, 29, 29]
    · exact ![961, 31]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N0
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
      exact NI13N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N0
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
  β := ![I2N0, I3N0, I5N0, I7N0, I13N0, I13N1, I13N2, I19N1, I23N0, I29N0, I29N1, I31N1]
  Il := ![[I2N0], [I3N0, I3N0, I3N0], [I5N0, I5N0, I5N0], [I7N0, I7N0, I7N0], [], [I13N0, I13N1, I13N2], [], [I19N1], [I23N0], [I29N0, I29N0, I29N1], [I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
