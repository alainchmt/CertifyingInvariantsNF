
import IdealArithmetic.Examples.NF3_1_960204_2.RI3_1_960204_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 1, 0]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0], ![0, 1, 0]] 
 ![![2, 0, 0], ![0, 1, 0], ![1, 0, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![0, 1, 0], ![-1, -1, 3], ![51, -42, 1]]]
  hmulB := by decide  
  f := ![![![0, -1, 3], ![0, -2, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, 2], ![-1, -1, 0]]]
  g := ![![![1, 0, 0], ![0, 2, 0], ![-1, 0, 2]], ![![0, 1, 0], ![-2, -1, 3], ![25, -42, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![2, 0, 0], ![0, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![2, 0, 0], ![29, 1, 1]] where
 M := ![![![4, 0, 0], ![0, 2, 0]], ![![0, 2, 0], ![-1, -1, 3]]]
 hmul := by decide  
 g := ![![![![-27, -1, -1], ![2, 0, 0]], ![![0, 1, 0], ![0, 0, 0]]], ![![![0, 1, 0], ![0, 0, 0]], ![![-15, -1, 1], ![1, 0, 0]]]]
 hle2 := by decide  
def MulI2N1 : IdealMulLeCertificate' Table 
  ![![2, 0, 0], ![29, 1, 1]] ![![2, 0, 0], ![0, 1, 0]]
  ![![2, 0, 0]] where
 M := ![![![4, 0, 0], ![0, 2, 0]], ![![58, 2, 2], ![50, -14, 4]]]
 hmul := by decide  
 g := ![![![![2, 0, 0]], ![![0, 1, 0]]], ![![![29, 1, 1]], ![![25, -7, 2]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![29, 0, 1]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0], ![29, 0, 1]] 
 ![![3, 0, 0], ![2, 1, 0], ![2, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![29, 0, 1], ![51, -13, 1], ![48, 3, -12]]]
  hmulB := by decide  
  f := ![![![-28, 0, -1], ![3, 0, 0]], ![![-14, 9, 0], ![-2, 2, 0]], ![![-9, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![-2, 3, 0], ![-2, 0, 3]], ![![9, 0, 1], ![25, -13, 1], ![22, 3, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-29, -1, -1]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![3, 0, 0], ![-29, -1, -1]] 
 ![![3, 0, 0], ![2, 1, 0], ![0, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![-29, -1, -1], ![-50, 14, -4], ![-99, 39, 11]]]
  hmulB := by decide  
  f := ![![![25, -84, -28], ![-18, 0, 6]], ![![7, -56, -19], ![-13, 0, 4]], ![![25, 15, 6], ![6, 0, -1]]]
  g := ![![![1, 0, 0], ![-2, 3, 0], ![0, 0, 3]], ![![-9, -1, -1], ![-26, 14, -4], ![-59, 39, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![29, 0, 1]] ![![3, 0, 0], ![-29, -1, -1]]
  ![![3, 0, 0], ![-1, 1, 0]] where
 M := ![![![9, 0, 0], ![-87, -3, -3]], ![![87, 0, 3], ![-940, 10, -18]]]
 hmul := by decide  
 g := ![![![![3, 0, 0], ![0, 0, 0]], ![![-26, -4, -1], ![9, 0, 0]]], ![![![27, 2, 1], ![-6, 0, 0]], ![![-284, -26, -6], ![88, 0, 0]]]]
 hle2 := by decide  

def MulI3N1 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![-1, 1, 0]] ![![3, 0, 0], ![-29, -1, -1]]
  ![![3, 0, 0]] where
 M := ![![![9, 0, 0], ![-87, -3, -3]], ![![-3, 3, 0], ![-21, 15, -3]]]
 hmul := by decide  
 g := ![![![![3, 0, 0]], ![![-29, -1, -1]]], ![![![-1, 1, 0]], ![![-7, 5, -1]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N1, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N1
    exact isPrimeI3N1
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


def P5P0 : CertificateIrreducibleZModOfList' 5 3 2 2 [4, 0, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 2, 4], [3, 2, 1], [0, 1]]
 g := ![![[4, 2, 1], []], ![[4, 1, 2, 1], [3, 1]], ![[0, 1, 3, 4], [1, 1]]]
 h' := ![![[4, 2, 4], [0, 0, 1], [0, 1]], ![[3, 2, 1], [4, 2, 2], [4, 2, 4]], ![[0, 1], [0, 3, 2], [3, 2, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 3], []]
 b := ![[], [2, 4, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where
  n := 3
  hpos := by decide
  P := [4, 0, 3, 1]
  hirr := P5P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![51605, 6885, -49005]
  a := ![1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![10321, 1377, -9801]
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


def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3035, -5, -72]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![-3035, -5, -72]] 
 ![![7, 0, 0], ![0, 1, 0], ![2, 0, 1]] where
  M :=![![![-3035, -5, -72], ![-3667, -6, -87], ![-3711, -6, -88]]]
  hmulB := by decide  
  f := ![![![-6, 8, -3]], ![![-23, 16, 3]], ![![36, -47, 17]]]
  g := ![![![-413, -5, -72], ![-499, -6, -87], ![-505, -6, -88]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N0)

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := prime_ideal_of_norm_prime hp7.out _ NI7N0
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![-3035, -5, -72]] ![![-3035, -5, -72]]
  ![![9496752, 15637, 225291]] where
 M := ![![![9496752, 15637, 225291]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI7N1 : IdealMulLeCertificate' Table 
  ![![9496752, 15637, 225291]] ![![-3035, -5, -72]]
  ![![7, 0, 0]] where
 M := ![![![-29716038100, -48929328, -704952171]]]
 hmul := by decide  
 g := ![![![![-4245148300, -6989904, -100707453]]]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![0, 1, 0]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0], ![0, 1, 0]] 
 ![![11, 0, 0], ![0, 1, 0], ![7, 0, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![0, 1, 0], ![-1, -1, 3], ![51, -42, 1]]]
  hmulB := by decide  
  f := ![![![0, -1, 3], ![0, -11, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, -1, 2], ![4, -7, 0]]]
  g := ![![![1, 0, 0], ![0, 11, 0], ![-7, 0, 11]], ![![0, 1, 0], ![-2, -1, 3], ![4, -42, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N0 : Nat.card (O ⧸ I11N0) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N0)

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := prime_ideal_of_norm_prime hp11.out _ NI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![27, -4, 1]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![11, 0, 0], ![27, -4, 1]] 
 ![![11, 0, 0], ![0, 11, 0], ![5, 7, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![27, -4, 1], ![55, -11, -11], ![-156, 171, -18]]]
  hmulB := by decide  
  f := ![![![-26, 4, -1], ![11, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![-2, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-5, -7, 11]], ![![2, -1, 1], ![10, 6, -11], ![-6, 27, -18]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P1 : CertificateIrreducibleZModOfList' 11 2 2 3 [5, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 10], [0, 1]]
 g := ![![[4, 9], [10, 4], [1]], ![[0, 2], [7, 7], [1]]]
 h' := ![![[2, 10], [5, 3], [6, 2], [0, 1]], ![[0, 1], [0, 8], [10, 9], [2, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [4, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N1 : CertifiedPrimeIdeal' SI11N1 11 where
  n := 2
  hpos := by decide
  P := [5, 9, 1]
  hirr := P11P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1046, 3512, -2605]
  a := ![-3, -5, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1089, 1977, -2605]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N1 B_one_repr
lemma NI11N1 : Nat.card (O ⧸ I11N1) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![11, 0, 0], ![0, 1, 0]] ![![11, 0, 0], ![27, -4, 1]]
  ![![11, 0, 0]] where
 M := ![![![121, 0, 0], ![297, -44, 11]], ![![0, 11, 0], ![55, -11, -11]]]
 hmul := by decide  
 g := ![![![![11, 0, 0]], ![![27, -4, 1]]], ![![![0, 1, 0]], ![![5, -1, -1]]]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![23, 3, 1]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0], ![23, 3, 1]] 
 ![![13, 0, 0], ![0, 13, 0], ![10, 3, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![23, 3, 1], ![48, -22, 10], ![201, -123, -15]]]
  hmulB := by decide  
  f := ![![![-22, -3, -1], ![13, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![-1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-10, -3, 13]], ![![1, 0, 1], ![-4, -4, 10], ![27, -6, -15]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [4, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 12], [0, 1]]
 g := ![![[3, 10], [9], [1, 1]], ![[0, 3], [9], [2, 12]]]
 h' := ![![[1, 12], [6, 7], [9, 10], [0, 1]], ![[0, 1], [0, 6], [6, 3], [1, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [6, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 2
  hpos := by decide
  P := [4, 12, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![201817, 24747, -185243]
  a := ![1, 2, -67]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![158019, 44652, -185243]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![3, 1, 0]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![13, 0, 0], ![3, 1, 0]] 
 ![![13, 0, 0], ![3, 1, 0], ![2, 0, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![3, 1, 0], ![-1, 2, 3], ![51, -42, 4]]]
  hmulB := by decide  
  f := ![![![-53, 108, 162], ![0, -702, 0]], ![![-12, 24, 36], ![1, -156, 0]], ![![-10, 16, 25], ![8, -108, 0]]]
  g := ![![![1, 0, 0], ![-3, 13, 0], ![-2, 0, 13]], ![![0, 1, 0], ![-1, 2, 3], ![13, -42, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![13, 0, 0], ![23, 3, 1]] ![![13, 0, 0], ![3, 1, 0]]
  ![![13, 0, 0]] where
 M := ![![![169, 0, 0], ![39, 13, 0]], ![![299, 39, 13], ![117, -13, 13]]]
 hmul := by decide  
 g := ![![![![13, 0, 0]], ![![3, 1, 0]]], ![![![23, 3, 1]], ![![9, -1, 1]]]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![24, 2, 1]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0], ![24, 2, 1]] 
 ![![17, 0, 0], ![0, 17, 0], ![7, 2, 1]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]], ![![24, 2, 1], ![49, -20, 7], ![150, -81, -15]]]
  hmulB := by decide  
  f := ![![![-23, -2, -1], ![17, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![-1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-7, -2, 17]], ![![1, 0, 1], ![0, -2, 7], ![15, -3, -15]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 2 2 4 [9, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 16], [0, 1]]
 g := ![![[10, 2], [1], [8], [1]], ![[0, 15], [1], [8], [1]]]
 h' := ![![[12, 16], [4, 11], [9, 16], [8, 12], [0, 1]], ![[0, 1], [0, 6], [14, 1], [16, 5], [12, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [2, 11]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 2
  hpos := by decide
  P := [9, 5, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-175, 2908, -2728]
  a := ![3, 4, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1113, 492, -2728]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![-7, 1, 0]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![17, 0, 0], ![-7, 1, 0]] 
 ![![17, 0, 0], ![10, 1, 0], ![15, 0, 1]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]], ![![-7, 1, 0], ![-1, -8, 3], ![51, -42, -6]]]
  hmulB := by decide  
  f := ![![![-155, -1248, 468], ![0, -2652, 0]], ![![-90, -728, 273], ![1, -1547, 0]], ![![-138, -1101, 413], ![-3, -2340, 0]]]
  g := ![![![1, 0, 0], ![-10, 17, 0], ![-15, 0, 17]], ![![-1, 1, 0], ![2, -8, 3], ![33, -42, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![17, 0, 0], ![24, 2, 1]] ![![17, 0, 0], ![-7, 1, 0]]
  ![![17, 0, 0]] where
 M := ![![![289, 0, 0], ![-119, 17, 0]], ![![408, 34, 17], ![-119, -34, 0]]]
 hmul := by decide  
 g := ![![![![17, 0, 0]], ![![-7, 1, 0]]], ![![![24, 2, 1]], ![![-7, -2, 0]]]]
 hle2 := by decide  


def PBC17 : ContainsPrimesAboveP 17 ![I17N0, I17N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 17 (by decide) (𝕀 ⊙ MulI17N0)
instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![28, -8, 1]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0], ![28, -8, 1]] 
 ![![19, 0, 0], ![0, 19, 0], ![9, 11, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![28, -8, 1], ![59, -6, -23], ![-360, 339, -21]]]
  hmulB := by decide  
  f := ![![![-27, 8, -1], ![19, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![-1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-9, -11, 19]], ![![1, -1, 1], ![14, 13, -23], ![-9, 30, -21]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [12, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 18], [0, 1]]
 g := ![![[16, 1], [15, 4], [4], [1]], ![[14, 18], [7, 15], [4], [1]]]
 h' := ![![[17, 18], [10, 18], [1, 2], [7, 17], [0, 1]], ![[0, 1], [12, 1], [16, 17], [11, 2], [17, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [13, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [12, 2, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![447, 27, -381]
  a := ![1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![204, 222, -381]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![4, 1, 0]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![19, 0, 0], ![4, 1, 0]] 
 ![![19, 0, 0], ![4, 1, 0], ![2, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![4, 1, 0], ![-1, 3, 3], ![51, -42, 5]]]
  hmulB := by decide  
  f := ![![![-59, 180, 180], ![0, -1140, 0]], ![![-12, 36, 36], ![1, -228, 0]], ![![-10, 18, 19], ![18, -120, 0]]]
  g := ![![![1, 0, 0], ![-4, 19, 0], ![-2, 0, 19]], ![![0, 1, 0], ![-1, 3, 3], ![11, -42, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![19, 0, 0], ![28, -8, 1]] ![![19, 0, 0], ![4, 1, 0]]
  ![![19, 0, 0]] where
 M := ![![![361, 0, 0], ![76, 19, 0]], ![![532, -152, 19], ![171, -38, -19]]]
 hmul := by decide  
 g := ![![![![19, 0, 0]], ![![4, 1, 0]]], ![![![28, -8, 1]], ![![9, -2, -1]]]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![2, 1, 0]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0], ![2, 1, 0]] 
 ![![23, 0, 0], ![2, 1, 0], ![22, 0, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![2, 1, 0], ![-1, 1, 3], ![51, -42, 3]]]
  hmulB := by decide  
  f := ![![![-191, 192, 576], ![0, -4416, 0]], ![![-16, 16, 48], ![1, -368, 0]], ![![-184, 183, 551], ![15, -4224, 0]]]
  g := ![![![1, 0, 0], ![-2, 23, 0], ![-22, 0, 23]], ![![0, 1, 0], ![-3, 1, 3], ![3, -42, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N0 : Nat.card (O ⧸ I23N0) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N0)

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := prime_ideal_of_norm_prime hp23.out _ NI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![-4, 1, 0]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![23, 0, 0], ![-4, 1, 0]] 
 ![![23, 0, 0], ![19, 1, 0], ![16, 0, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![-4, 1, 0], ![-1, -5, 3], ![51, -42, -3]]]
  hmulB := by decide  
  f := ![![![-33, -170, 102], ![0, -782, 0]], ![![-27, -140, 84], ![1, -644, 0]], ![![-20, -119, 71], ![17, -544, 0]]]
  g := ![![![1, 0, 0], ![-19, 23, 0], ![-16, 0, 23]], ![![-1, 1, 0], ![2, -5, 3], ![39, -42, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![23, 0, 0], ![2, 1, 0]] ![![23, 0, 0], ![2, 1, 0]]
  ![![23, 0, 0], ![24, 1, 1]] where
 M := ![![![529, 0, 0], ![46, 23, 0]], ![![46, 23, 0], ![3, 3, 3]]]
 hmul := by decide  
 g := ![![![![-1, -1, -1], ![23, 0, 0]], ![![-22, 0, -1], ![23, 0, 0]]], ![![![-22, 0, -1], ![23, 0, 0]], ![![-3, 0, 0], ![3, 0, 0]]]]
 hle2 := by decide  
def MulI23N1 : IdealMulLeCertificate' Table 
  ![![23, 0, 0], ![24, 1, 1]] ![![23, 0, 0], ![-4, 1, 0]]
  ![![23, 0, 0]] where
 M := ![![![529, 0, 0], ![-92, 23, 0]], ![![552, 23, 23], ![-46, -23, 0]]]
 hmul := by decide  
 g := ![![![![23, 0, 0]], ![![-4, 1, 0]]], ![![![24, 1, 1]], ![![-2, -1, 0]]]]
 hle2 := by decide  


def PBC23 : ContainsPrimesAboveP 23 ![I23N0, I23N0, I23N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
    exact isPrimeI23N0
    exact isPrimeI23N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 23 (by decide) (𝕀 ⊙ MulI23N0 ⊙ MulI23N1)
instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![24, -4, 1]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0], ![24, -4, 1]] 
 ![![29, 0, 0], ![0, 29, 0], ![24, 25, 1]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![24, -4, 1], ![55, -14, -11], ![-156, 171, -21]]]
  hmulB := by decide  
  f := ![![![-23, 4, -1], ![29, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-24, -25, 29]], ![![0, -1, 1], ![11, 9, -11], ![12, 24, -21]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [12, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 28], [0, 1]]
 g := ![![[14, 7], [28], [0, 25], [6, 1]], ![[27, 22], [28], [5, 4], [12, 28]]]
 h' := ![![[6, 28], [12, 23], [0, 12], [15, 24], [0, 1]], ![[0, 1], [5, 6], [14, 17], [14, 5], [6, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [14, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [12, 23, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7778, -5946, 544]
  a := ![-1, 18, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-182, -674, 544]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![11, 1, 0]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![29, 0, 0], ![11, 1, 0]] 
 ![![29, 0, 0], ![11, 1, 0], ![21, 0, 1]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![11, 1, 0], ![-1, 10, 3], ![51, -42, 12]]]
  hmulB := by decide  
  f := ![![![-167, 1680, 504], ![0, -4872, 0]], ![![-63, 630, 189], ![1, -1827, 0]], ![![-127, 1216, 365], ![16, -3528, 0]]]
  g := ![![![1, 0, 0], ![-11, 29, 0], ![-21, 0, 29]], ![![0, 1, 0], ![-6, 10, 3], ![9, -42, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![29, 0, 0], ![24, -4, 1]] ![![29, 0, 0], ![11, 1, 0]]
  ![![29, 0, 0]] where
 M := ![![![841, 0, 0], ![319, 29, 0]], ![![696, -116, 29], ![319, -58, 0]]]
 hmul := by decide  
 g := ![![![![29, 0, 0]], ![![11, 1, 0]]], ![![![24, -4, 1]], ![![11, -2, 0]]]]
 hle2 := by decide  


def PBC29 : ContainsPrimesAboveP 29 ![I29N0, I29N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 29 (by decide) (𝕀 ⊙ MulI29N0)
instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![32, -3, 1]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0], ![32, -3, 1]] 
 ![![31, 0, 0], ![0, 31, 0], ![1, 28, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![32, -3, 1], ![54, -7, -8], ![-105, 129, -12]]]
  hmulB := by decide  
  f := ![![![-31, 3, -1], ![31, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![-1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-1, -28, 31]], ![![1, -1, 1], ![2, 7, -8], ![-3, 15, -12]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [23, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 30], [0, 1]]
 g := ![![[1, 18], [30, 19], [3, 7], [8, 1]], ![[21, 13], [27, 12], [28, 24], [16, 30]]]
 h' := ![![[8, 30], [23, 7], [24, 22], [2, 10], [0, 1]], ![[0, 1], [17, 24], [14, 9], [20, 21], [8, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [13, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [23, 23, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-833, 1476, -740]
  a := ![1, 4, -4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3, 716, -740]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![8, 1, 0]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![31, 0, 0], ![8, 1, 0]] 
 ![![31, 0, 0], ![8, 1, 0], ![12, 0, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![8, 1, 0], ![-1, 7, 3], ![51, -42, 9]]]
  hmulB := by decide  
  f := ![![![-67, 476, 204], ![0, -2108, 0]], ![![-17, 119, 51], ![1, -527, 0]], ![![-28, 184, 79], ![8, -816, 0]]]
  g := ![![![1, 0, 0], ![-8, 31, 0], ![-12, 0, 31]], ![![0, 1, 0], ![-3, 7, 3], ![9, -42, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![31, 0, 0], ![32, -3, 1]] ![![31, 0, 0], ![8, 1, 0]]
  ![![31, 0, 0]] where
 M := ![![![961, 0, 0], ![248, 31, 0]], ![![992, -93, 31], ![310, -31, 0]]]
 hmul := by decide  
 g := ![![![![31, 0, 0]], ![![8, 1, 0]]], ![![![32, -3, 1]], ![![10, -1, 0]]]]
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
  g := ![3, 3, 1, 3, 2, 2, 2, 2, 3, 2, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB278I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N0, I2N0]
    · exact ![I3N0, I3N1, I3N1]
    · exact ![I5N0]
    · exact ![I7N0, I7N0, I7N0]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1]
    · exact ![I17N0, I17N1]
    · exact ![I19N0, I19N1]
    · exact ![I23N0, I23N0, I23N1]
    · exact ![I29N0, I29N1]
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
    · exact ![3, 3, 3]
    · exact ![125]
    · exact ![7, 7, 7]
    · exact ![11, 121]
    · exact ![169, 13]
    · exact ![289, 17]
    · exact ![361, 19]
    · exact ![23, 23, 23]
    · exact ![841, 29]
    · exact ![961, 31]
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
      exact NI3N1
      exact NI3N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N0
      exact NI23N1
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
  β := ![I2N0, I3N0, I3N1, I5N0, I7N0, I11N0, I11N1, I13N0, I13N1, I17N1, I19N1, I23N0, I23N1, I29N1, I31N1]
  Il := ![[I2N0, I2N0, I2N0], [I3N0, I3N1, I3N1], [I5N0], [I7N0, I7N0, I7N0], [I11N0, I11N1], [I13N0, I13N1], [I17N1], [I19N1], [I23N0, I23N0, I23N1], [I29N1], [I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
