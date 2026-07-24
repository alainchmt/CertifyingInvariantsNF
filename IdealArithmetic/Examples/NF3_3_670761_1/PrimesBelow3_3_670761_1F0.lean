
import IdealArithmetic.Examples.NF3_3_670761_1.RI3_3_670761_1
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
  c := ![295210, 104290, -831842]
  a := ![5, 4, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![147605, 52145, -415921]
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


def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-1, 1, 0]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0], ![-1, 1, 0]] 
 ![![3, 0, 0], ![2, 1, 0], ![2, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![-1, 1, 0], ![-5, -6, 11], ![6, 23, 4]]]
  hmulB := by decide  
  f := ![![![22, 23, -44], ![3, 12, 0]], ![![11, 12, -22], ![1, 6, 0]], ![![15, 15, -29], ![3, 8, 0]]]
  g := ![![![1, 0, 0], ![-2, 3, 0], ![-2, 0, 3]], ![![-1, 1, 0], ![-5, -6, 11], ![-16, 23, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![-1, 1, 0]] ![![3, 0, 0], ![-1, 1, 0]]
  ![![3, 0, 0], ![-17, -2, 1]] where
 M := ![![![9, 0, 0], ![-3, 3, 0]], ![![-3, 3, 0], ![-4, -7, 11]]]
 hmul := by decide  
 g := ![![![![3, 0, 0], ![0, 0, 0]], ![![16, 3, -1], ![3, 0, 0]]], ![![![16, 3, -1], ![3, 0, 0]], ![![10, -1, 3], ![2, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![-17, -2, 1]] ![![3, 0, 0], ![-1, 1, 0]]
  ![![3, 0, 0]] where
 M := ![![![9, 0, 0], ![-3, 3, 0]], ![![-51, -6, 3], ![33, 18, -18]]]
 hmul := by decide  
 g := ![![![![3, 0, 0]], ![![-1, 1, 0]]], ![![![-17, -2, 1]], ![![11, 6, -6]]]]
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
instance hp5 : Fact (Nat.Prime 5) := {out := by norm_num}

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![5, 0, 0]] 
 ![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P5P0 : CertificateIrreducibleZModOfList' 5 3 2 2 [4, 3, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 2, 1], [3, 2, 4], [0, 1]]
 g := ![![[3, 1, 1], []], ![[0, 3, 4, 4], [0, 1]], ![[2, 3, 1, 1], [2, 1]]]
 h' := ![![[3, 2, 1], [0, 0, 1], [0, 1]], ![[3, 2, 4], [4, 3, 2], [3, 2, 1]], ![[0, 1], [1, 2, 2], [3, 2, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 4], []]
 b := ![[], [0, 4, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where
  n := 3
  hpos := by decide
  P := [4, 3, 4, 1]
  hirr := P5P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4579890, -5637130, 8624345]
  a := ![-11, -13, 24]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-915978, -1127426, 1724869]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI5N0 B_one_repr
lemma NI5N0 : Nat.card (O ⧸ I5N0) = 125 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI5N0

def PBC5 : ContainsPrimesAboveP 5 ![I5N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![5, 0, 0]]) timesTableT_eq_Table B_one_repr 5 (by decide) 𝕀


def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![0, 1, 0]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0], ![0, 1, 0]] 
 ![![7, 0, 0], ![0, 1, 0], ![4, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![0, 1, 0], ![-5, -5, 11], ![6, 23, 5]]]
  hmulB := by decide  
  f := ![![![-14, -15, 33], ![0, -21, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-8, -9, 19], ![3, -12, 0]]]
  g := ![![![1, 0, 0], ![0, 7, 0], ![-4, 0, 7]], ![![0, 1, 0], ![-7, -5, 11], ![-2, 23, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N0)

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := prime_ideal_of_norm_prime hp7.out _ NI7N0
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![7, 0, 0], ![0, 1, 0]] ![![7, 0, 0], ![0, 1, 0]]
  ![![7, 0, 0], ![-17, -3, 1]] where
 M := ![![![49, 0, 0], ![0, 7, 0]], ![![0, 7, 0], ![-5, -5, 11]]]
 hmul := by decide  
 g := ![![![![7, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]]], ![![![0, 1, 0], ![0, 0, 0]], ![![9, 1, 1], ![4, 0, 0]]]]
 hle2 := by decide  
def MulI7N1 : IdealMulLeCertificate' Table 
  ![![7, 0, 0], ![-17, -3, 1]] ![![7, 0, 0], ![0, 1, 0]]
  ![![7, 0, 0]] where
 M := ![![![49, 0, 0], ![0, 7, 0]], ![![-119, -21, 7], ![21, 21, -28]]]
 hmul := by decide  
 g := ![![![![7, 0, 0]], ![![0, 1, 0]]], ![![![-17, -3, 1]], ![![3, 3, -4]]]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![-80, 0, 5]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0], ![-80, 0, 5]] 
 ![![11, 0, 0], ![6, 1, 0], ![6, 0, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![-80, 0, 5], ![30, 35, 25], ![-25, 55, 60]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![36, 16, 10], ![3, -5, 0]], ![![66, 0, -4], ![9, 0, 0]]]
  g := ![![![1, 0, 0], ![-6, 11, 0], ![-6, 0, 11]], ![![-10, 0, 5], ![-30, 35, 25], ![-65, 55, 60]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N0 : Nat.card (O ⧸ I11N0) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N0)

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := prime_ideal_of_norm_prime hp11.out _ NI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![-18, -1, 1]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![11, 0, 0], ![-18, -1, 1]] 
 ![![11, 0, 0], ![6, 1, 0], ![10, 0, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![-18, -1, 1], ![11, 10, -6], ![-11, -12, 5]]]
  hmulB := by decide  
  f := ![![![197, 762, -442], ![-418, -880, 0]], ![![104, 407, -236], ![-224, -470, 0]], ![![184, 693, -402], ![-377, -800, 0]]]
  g := ![![![1, 0, 0], ![-6, 11, 0], ![-10, 0, 11]], ![![-2, -1, 1], ![1, 10, -6], ![1, -12, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1

def I11N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![-1, 1, 0]] i)))

def SI11N2: IdealEqSpanCertificate' Table ![![11, 0, 0], ![-1, 1, 0]] 
 ![![11, 0, 0], ![10, 1, 0], ![10, 0, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![-1, 1, 0], ![-5, -6, 11], ![6, 23, 4]]]
  hmulB := by decide  
  f := ![![![493, 1828, 320], ![132, 0, -880]], ![![443, 1646, 288], ![111, 0, -792]], ![![448, 1662, 291], ![118, 0, -800]]]
  g := ![![![1, 0, 0], ![-10, 11, 0], ![-10, 0, 11]], ![![-1, 1, 0], ![-5, -6, 11], ![-24, 23, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N2 : Nat.card (O ⧸ I11N2) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N2)

lemma isPrimeI11N2 : Ideal.IsPrime I11N2 := prime_ideal_of_norm_prime hp11.out _ NI11N2
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![11, 0, 0], ![-80, 0, 5]] ![![11, 0, 0], ![-18, -1, 1]]
  ![![11, 0, 0], ![-5, 1, 0]] where
 M := ![![![121, 0, 0], ![-198, -11, 11]], ![![-880, 0, 55], ![1385, 20, -55]]]
 hmul := by decide  
 g := ![![![![11, 0, 0], ![0, 0, 0]], ![![-13, -2, 1], ![11, 0, 0]]], ![![![-65, -3, 5], ![33, 0, 0]], ![![105, 6, -5], ![-46, 0, 0]]]]
 hle2 := by decide  

def MulI11N1 : IdealMulLeCertificate' Table 
  ![![11, 0, 0], ![-5, 1, 0]] ![![11, 0, 0], ![-1, 1, 0]]
  ![![11, 0, 0]] where
 M := ![![![121, 0, 0], ![-11, 11, 0]], ![![-55, 11, 0], ![0, -11, 11]]]
 hmul := by decide  
 g := ![![![![11, 0, 0]], ![![-1, 1, 0]]], ![![![-5, 1, 0]], ![![0, -1, 1]]]]
 hle2 := by decide  


def PBC11 : ContainsPrimesAboveP 11 ![I11N0, I11N1, I11N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
    exact isPrimeI11N1
    exact isPrimeI11N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 11 (by decide) (𝕀 ⊙ MulI11N0 ⊙ MulI11N1)

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![0, 1, 0]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0], ![0, 1, 0]] 
 ![![13, 0, 0], ![0, 1, 0], ![9, 0, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![0, 1, 0], ![-5, -5, 11], ![6, 23, 5]]]
  hmulB := by decide  
  f := ![![![-39, -40, 88], ![0, -104, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-27, -28, 61], ![4, -72, 0]]]
  g := ![![![1, 0, 0], ![0, 13, 0], ![-9, 0, 13]], ![![0, 1, 0], ![-8, -5, 11], ![-3, 23, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N0 : Nat.card (O ⧸ I13N0) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N0)

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := prime_ideal_of_norm_prime hp13.out _ NI13N0
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![13, 0, 0], ![0, 1, 0]] ![![13, 0, 0], ![0, 1, 0]]
  ![![13, 0, 0], ![-17, -4, 1]] where
 M := ![![![169, 0, 0], ![0, 13, 0]], ![![0, 13, 0], ![-5, -5, 11]]]
 hmul := by decide  
 g := ![![![![13, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]]], ![![![0, 1, 0], ![0, 0, 0]], ![![14, 3, 0], ![11, 0, 0]]]]
 hle2 := by decide  
def MulI13N1 : IdealMulLeCertificate' Table 
  ![![13, 0, 0], ![-17, -4, 1]] ![![13, 0, 0], ![0, 1, 0]]
  ![![13, 0, 0]] where
 M := ![![![169, 0, 0], ![0, 13, 0]], ![![-221, -52, 13], ![26, 26, -39]]]
 hmul := by decide  
 g := ![![![![13, 0, 0]], ![![0, 1, 0]]], ![![![-17, -4, 1]], ![![2, 2, -3]]]]
 hle2 := by decide  

def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N0, I13N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N0
    exact isPrimeI13N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 13 (by decide) (𝕀 ⊙ MulI13N0 ⊙ MulI13N1)
instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![8, 1, 0]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0], ![8, 1, 0]] 
 ![![17, 0, 0], ![8, 1, 0], ![2, 0, 1]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]], ![![8, 1, 0], ![-5, 3, 11], ![6, 23, 13]]]
  hmulB := by decide  
  f := ![![![312, -233, -825], ![136, 1275, 0]], ![![143, -109, -385], ![69, 595, 0]], ![![32, -28, -97], ![26, 150, 0]]]
  g := ![![![1, 0, 0], ![-8, 17, 0], ![-2, 0, 17]], ![![0, 1, 0], ![-3, 3, 11], ![-12, 23, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N0 : Nat.card (O ⧸ I17N0) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N0)

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := prime_ideal_of_norm_prime hp17.out _ NI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![-6, 1, 0]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![17, 0, 0], ![-6, 1, 0]] 
 ![![17, 0, 0], ![11, 1, 0], ![9, 0, 1]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]], ![![-6, 1, 0], ![-5, -11, 11], ![6, 23, -1]]]
  hmulB := by decide  
  f := ![![![135, 309, -308], ![-17, 476, 0]], ![![85, 199, -198], ![-16, 306, 0]], ![![75, 163, -163], ![1, 252, 0]]]
  g := ![![![1, 0, 0], ![-11, 17, 0], ![-9, 0, 17]], ![![-1, 1, 0], ![1, -11, 11], ![-14, 23, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1

def I17N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![-2, 1, 0]] i)))

def SI17N2: IdealEqSpanCertificate' Table ![![17, 0, 0], ![-2, 1, 0]] 
 ![![17, 0, 0], ![15, 1, 0], ![6, 0, 1]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]], ![![-2, 1, 0], ![-5, -7, 11], ![6, 23, 3]]]
  hmulB := by decide  
  f := ![![![41, 56, -88], ![0, 136, 0]], ![![36, 49, -77], ![1, 119, 0]], ![![16, 19, -31], ![13, 48, 0]]]
  g := ![![![1, 0, 0], ![-15, 17, 0], ![-6, 0, 17]], ![![-1, 1, 0], ![2, -7, 11], ![-21, 23, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N2 : Nat.card (O ⧸ I17N2) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N2)

lemma isPrimeI17N2 : Ideal.IsPrime I17N2 := prime_ideal_of_norm_prime hp17.out _ NI17N2
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![17, 0, 0], ![8, 1, 0]] ![![17, 0, 0], ![-6, 1, 0]]
  ![![17, 0, 0], ![-11, -8, 1]] where
 M := ![![![289, 0, 0], ![-102, 17, 0]], ![![136, 17, 0], ![-53, -3, 11]]]
 hmul := by decide  
 g := ![![![![17, 0, 0], ![0, 0, 0]], ![![5, 9, -1], ![17, 0, 0]]], ![![![8, 1, 0], ![0, 0, 0]], ![![4, 5, 0], ![11, 0, 0]]]]
 hle2 := by decide  

def MulI17N1 : IdealMulLeCertificate' Table 
  ![![17, 0, 0], ![-11, -8, 1]] ![![17, 0, 0], ![-2, 1, 0]]
  ![![17, 0, 0]] where
 M := ![![![289, 0, 0], ![-34, 17, 0]], ![![-187, -136, 17], ![68, 68, -85]]]
 hmul := by decide  
 g := ![![![![17, 0, 0]], ![![-2, 1, 0]]], ![![![-11, -8, 1]], ![![4, 4, -5]]]]
 hle2 := by decide  


def PBC17 : ContainsPrimesAboveP 17 ![I17N0, I17N1, I17N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N1
    exact isPrimeI17N2
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


def P19P0 : CertificateIrreducibleZModOfList' 19 3 2 4 [6, 7, 8, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 7, 9], [12, 11, 10], [0, 1]]
 g := ![![[16], [11], [11, 1], []], ![[11, 3, 5, 17], [11, 2, 7, 1], [1, 7], [10, 5]], ![[2, 17, 2, 2], [11, 14, 18, 18], [7, 11], [9, 5]]]
 h' := ![![[18, 7, 9], [10, 4], [10, 12], [0, 0, 1], [0, 1]], ![[12, 11, 10], [6, 9, 17], [17, 8, 13], [17, 0, 11], [18, 7, 9]], ![[0, 1], [1, 6, 2], [2, 18, 6], [14, 0, 7], [12, 11, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14, 10], []]
 b := ![[], [7, 10, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 3
  hpos := by decide
  P := [6, 7, 8, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![54407161371, 46066293630, -124714919166]
  a := ![261, 262, -587]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2863534809, 2424541770, -6563943114]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0]] 
 ![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [9, 1, 18, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 7, 2], [15, 15, 21], [0, 1]]
 g := ![![[19, 18, 6], [13, 14, 12], [1, 5, 1], []], ![[22, 7, 21, 4], [14, 21, 11, 18], [0, 5, 22, 13], [2, 4]], ![[5, 20, 20, 17], [17, 8, 11, 20], [9, 21, 22, 17], [6, 4]]]
 h' := ![![[13, 7, 2], [21, 11, 12], [14, 0, 14], [0, 0, 1], [0, 1]], ![[15, 15, 21], [21, 11, 18], [12, 15, 3], [13, 6, 15], [13, 7, 2]], ![[0, 1], [7, 1, 16], [16, 8, 6], [10, 17, 7], [15, 15, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 20], []]
 b := ![[], [15, 9, 13], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [9, 1, 18, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4048345, 4383984, -8261232]
  a := ![11, 12, -24]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![176015, 190608, -359184]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 12167 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def PBC23 : ContainsPrimesAboveP 23 ![I23N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![23, 0, 0]]) timesTableT_eq_Table B_one_repr 23 (by decide) 𝕀

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


def P29P0 : CertificateIrreducibleZModOfList' 29 3 2 4 [1, 4, 24, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 1, 20], [12, 27, 9], [0, 1]]
 g := ![![[7, 7, 6], [5, 20], [12, 27, 25], [1]], ![[17, 21, 16, 24], [1, 24], [24, 5, 0, 6], [15, 12, 20, 25]], ![[26, 25, 9, 24], [0, 7], [24, 8, 2, 7], [2, 11, 27, 4]]]
 h' := ![![[22, 1, 20], [23, 25, 21], [17, 13, 22], [28, 25, 5], [0, 1]], ![[12, 27, 9], [0, 3, 23], [1, 1, 13], [19, 17, 26], [22, 1, 20]], ![[0, 1], [6, 1, 14], [8, 15, 23], [15, 16, 27], [12, 27, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18], []]
 b := ![[], [19, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 3
  hpos := by decide
  P := [1, 4, 24, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![266713, 86710, -759539]
  a := ![5, 4, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![9197, 2990, -26191]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![8, 1, 0]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0], ![8, 1, 0]] 
 ![![31, 0, 0], ![8, 1, 0], ![3, 0, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![8, 1, 0], ![-5, 3, 11], ![6, 23, 13]]]
  hmulB := by decide  
  f := ![![![-515, 327, 1188], ![-93, -3348, 0]], ![![-127, 82, 297], ![-30, -837, 0]], ![![-55, 31, 115], ![11, -324, 0]]]
  g := ![![![1, 0, 0], ![-8, 31, 0], ![-3, 0, 31]], ![![0, 1, 0], ![-2, 3, 11], ![-7, 23, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N0 : Nat.card (O ⧸ I31N0) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N0)

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := prime_ideal_of_norm_prime hp31.out _ NI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![11, 1, 0]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![31, 0, 0], ![11, 1, 0]] 
 ![![31, 0, 0], ![11, 1, 0], ![2, 0, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![11, 1, 0], ![-5, 6, 11], ![6, 23, 16]]]
  hmulB := by decide  
  f := ![![![1218, -1645, -2992], ![403, 8432, 0]], ![![425, -581, -1056], ![156, 2976, 0]], ![![69, -107, -193], ![53, 544, 0]]]
  g := ![![![1, 0, 0], ![-11, 31, 0], ![-2, 0, 31]], ![![0, 1, 0], ![-3, 6, 11], ![-9, 23, 16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1

def I31N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![12, 1, 0]] i)))

def SI31N2: IdealEqSpanCertificate' Table ![![31, 0, 0], ![12, 1, 0]] 
 ![![31, 0, 0], ![12, 1, 0], ![6, 0, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![12, 1, 0], ![-5, 7, 11], ![6, 23, 17]]]
  hmulB := by decide  
  f := ![![![172, -275, -429], ![62, 1209, 0]], ![![63, -106, -165], ![32, 465, 0]], ![![24, -54, -83], ![36, 234, 0]]]
  g := ![![![1, 0, 0], ![-12, 31, 0], ![-6, 0, 31]], ![![0, 1, 0], ![-5, 7, 11], ![-12, 23, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N2 : Nat.card (O ⧸ I31N2) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N2)

lemma isPrimeI31N2 : Ideal.IsPrime I31N2 := prime_ideal_of_norm_prime hp31.out _ NI31N2
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![31, 0, 0], ![8, 1, 0]] ![![31, 0, 0], ![11, 1, 0]]
  ![![31, 0, 0], ![-15, -10, 1]] where
 M := ![![![961, 0, 0], ![341, 31, 0]], ![![248, 31, 0], ![83, 14, 11]]]
 hmul := by decide  
 g := ![![![![31, 0, 0], ![0, 0, 0]], ![![11, 1, 0], ![0, 0, 0]]], ![![![8, 1, 0], ![0, 0, 0]], ![![8, 4, 0], ![11, 0, 0]]]]
 hle2 := by decide  

def MulI31N1 : IdealMulLeCertificate' Table 
  ![![31, 0, 0], ![-15, -10, 1]] ![![31, 0, 0], ![12, 1, 0]]
  ![![31, 0, 0]] where
 M := ![![![961, 0, 0], ![372, 31, 0]], ![![-465, -310, 31], ![-124, -62, -93]]]
 hmul := by decide  
 g := ![![![![31, 0, 0]], ![![12, 1, 0]]], ![![![-15, -10, 1]], ![![-4, -2, -3]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N1, I31N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N1
    exact isPrimeI31N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0 ⊙ MulI31N1)


lemma PB183I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB183I0 : PrimesBelowBoundCertificateInterval O 1 31 183 where
  m := 11
  g := ![1, 3, 1, 3, 3, 3, 3, 1, 1, 1, 3]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB183I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0]
    · exact ![I3N0, I3N0, I3N0]
    · exact ![I5N0]
    · exact ![I7N0, I7N0, I7N0]
    · exact ![I11N0, I11N1, I11N2]
    · exact ![I13N0, I13N0, I13N0]
    · exact ![I17N0, I17N1, I17N2]
    · exact ![I19N0]
    · exact ![I23N0]
    · exact ![I29N0]
    · exact ![I31N0, I31N1, I31N2]
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
    · exact ![125]
    · exact ![7, 7, 7]
    · exact ![11, 11, 11]
    · exact ![13, 13, 13]
    · exact ![17, 17, 17]
    · exact ![6859]
    · exact ![12167]
    · exact ![24389]
    · exact ![31, 31, 31]
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
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N0
      exact NI7N0
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
      exact NI11N2
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N0
      exact NI13N0
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
      exact NI17N2
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
      exact NI31N2
  β := ![I2N0, I3N0, I5N0, I7N0, I11N0, I11N1, I11N2, I13N0, I17N0, I17N1, I17N2, I31N0, I31N1, I31N2]
  Il := ![[I2N0], [I3N0, I3N0, I3N0], [I5N0], [I7N0, I7N0, I7N0], [I11N0, I11N1, I11N2], [I13N0, I13N0, I13N0], [I17N0, I17N1, I17N2], [], [], [], [I31N0, I31N1, I31N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
