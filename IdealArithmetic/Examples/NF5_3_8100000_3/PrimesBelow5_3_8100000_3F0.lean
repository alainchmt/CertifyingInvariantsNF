
import IdealArithmetic.Examples.NF5_3_8100000_3.RI5_3_8100000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 18, -7, 8, -8]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 18, -7, 8, -8]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![2, 18, -7, 8, -8], ![-24, -43, 18, -18, 24], ![72, 102, -43, 42, -60], ![-18, -18, 8, -7, 12], ![27, 30, -13, 12, -19]]]
  hmulB := by decide  
  f := ![![![1, 0, -1, 2, 4]], ![![6, 5, 0, -6, 0]], ![![0, 6, 5, -6, -12]], ![![-9, -6, 1, 11, 0]], ![![5, 0, -4, 4, 13]]]
  g := ![![![5, 18, -7, 8, -8], ![-24, -43, 18, -18, 24], ![66, 102, -43, 42, -60], ![-15, -18, 8, -7, 12], ![23, 30, -13, 12, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4, -5, 2, -2, 3]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![-4, -5, 2, -2, 3]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-4, -5, 2, -2, 3], ![9, 11, -5, 4, -7], ![-21, -27, 11, -12, 15], ![3, 4, -2, 2, -3], ![-6, -8, 3, -3, 5]]]
  hmulB := by decide  
  f := ![![![-14, -1, 1, 0, 4]], ![![-1, 0, 0, -1, 0]], ![![-13, -2, 1, 0, 2]], ![![-3, -1, 0, 1, 1]], ![![-4, 0, 0, -1, 2]]]
  g := ![![![-2, -5, 2, -2, 3], ![5, 11, -5, 4, -7], ![-10, -27, 11, -12, 15], ![2, 4, -2, 2, -3], ![-3, -8, 3, -3, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2, 0, 0, 0, 1]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![-2, 0, 0, 0, 1]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-2, 0, 0, 0, 1], ![3, 1, 0, -2, -1], ![-3, 0, 1, 0, -3], ![-3, -2, 0, 3, 1], ![3, 1, -1, -1, 2]]]
  hmulB := by decide  
  f := ![![![-1, -1, -1, -1, -1]], ![![-2, -4, -1, -3, -1]], ![![-2, -5, -4, -5, -5]], ![![-2, -3, -1, -2, -1]], ![![0, -1, -1, -1, -1]]]
  g := ![![![-1, 0, 0, 0, 1], ![2, 1, 0, -2, -1], ![-2, 0, 1, 0, -3], ![-2, -2, 0, 3, 1], ![2, 1, -1, -1, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![2, 18, -7, 8, -8]] ![![-4, -5, 2, -2, 3]]
  ![![373, 473, -203, 192, -289]] where
 M := ![![![373, 473, -203, 192, -289]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![373, 473, -203, 192, -289]] ![![-4, -5, 2, -2, 3]]
  ![![9338, 11899, -5103, 4833, -7258]] where
 M := ![![![9338, 11899, -5103, 4833, -7258]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![9338, 11899, -5103, 4833, -7258]] ![![-2, 0, 0, 0, 1]]
  ![![-3943, -5025, 2155, -2041, 3065]] where
 M := ![![![-3943, -5025, 2155, -2041, 3065]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![-3943, -5025, 2155, -2041, 3065]] ![![-2, 0, 0, 0, 1]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![1664, 2122, -910, 862, -1294]]]
 hmul := by decide  
 g := ![![![![832, 1061, -455, 431, -647]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N1, I2N1, I2N2, I2N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
    exact isPrimeI2N1
    exact isPrimeI2N2
    exact isPrimeI2N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1 ⊙ MulI2N2 ⊙ MulI2N3)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![0, 0, 0, -1, -1]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![0, 0, 0, -1, -1]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![0, 0, 0, -1, -1], ![-3, -3, 0, 1, -1], ![-3, -6, -3, 3, 3], ![3, 1, -1, -4, 1], ![0, 1, 1, -4, -5]]]
  hmulB := by decide  
  f := ![![![-102, -6, 8, 3, 27]], ![![27, 1, -2, -1, -7]], ![![-21, 0, 1, 1, 5]], ![![-11, -1, 1, 0, 3]], ![![10, 1, -1, 0, -3]]]
  g := ![![![0, 0, 0, -1, -1], ![-1, -3, 0, 1, -1], ![-1, -6, -3, 3, 3], ![1, 1, -1, -4, 1], ![0, 1, 1, -4, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![0, 0, 0, -1, -1]] ![![0, 0, 0, -1, -1]]
  ![![-3, -2, 0, 8, 4]] where
 M := ![![![-3, -2, 0, 8, 4]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![-3, -2, 0, 8, 4]] ![![0, 0, 0, -1, -1]]
  ![![30, 18, -4, -47, -7]] where
 M := ![![![30, 18, -4, -47, -7]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N2 : IdealMulLeCertificate' Table 
  ![![30, 18, -4, -47, -7]] ![![0, 0, 0, -1, -1]]
  ![![-183, -84, 52, 192, -72]] where
 M := ![![![-183, -84, 52, 192, -72]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N3 : IdealMulLeCertificate' Table 
  ![![-183, -84, 52, 192, -72]] ![![0, 0, 0, -1, -1]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![672, 60, -420, -225, 975]]]
 hmul := by decide  
 g := ![![![![224, 20, -140, -75, 325]]]]
 hle2 := by decide  

def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N0, I3N0, I3N0, I3N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1 ⊙ MulI3N2 ⊙ MulI3N3)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, -1, 1, 0, 2]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![-5, -1, 1, 0, 2]] 
 ![![5, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-5, -1, 1, 0, 2], ![6, 4, -1, 2, -2], ![-6, -3, 4, 0, 6], ![0, 2, 0, 1, 0], ![0, -1, 1, 0, 1]]]
  hmulB := by decide  
  f := ![![![-1, 1, 1, -2, -2]], ![![-2, 0, 1, 0, -2]], ![![-2, -1, 0, 2, 2]], ![![2, 2, 0, -3, 0]], ![![0, 1, 1, -2, -3]]]
  g := ![![![-1, -1, 1, 0, 2], ![-2, 4, -1, 2, -2], ![-2, -3, 4, 0, 6], ![-2, 2, 0, 1, 0], ![0, -1, 1, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![-5, -1, 1, 0, 2]] ![![-5, -1, 1, 0, 2]]
  ![![13, -4, 2, -2, 0]] where
 M := ![![![13, -4, 2, -2, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![13, -4, 2, -2, 0]] ![![-5, -1, 1, 0, 2]]
  ![![-101, -39, 25, -10, 46]] where
 M := ![![![-101, -39, 25, -10, 46]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![-101, -39, 25, -10, 46]] ![![-5, -1, 1, 0, 2]]
  ![![121, -196, 84, -88, 72]] where
 M := ![![![121, -196, 84, -88, 72]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![121, -196, 84, -88, 72]] ![![-5, -1, 1, 0, 2]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![-2285, -1405, 725, -480, 1210]]]
 hmul := by decide  
 g := ![![![![-457, -281, 145, -96, 242]]]]
 hle2 := by decide  

def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N0, I5N0, I5N0, I5N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0 ⊙ MulI5N1 ⊙ MulI5N2 ⊙ MulI5N3)
instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0, 0]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0, 0, 0]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]] where
  M :=![![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 5 2 2 [5, 0, 1, 6, 6, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 2, 0, 1, 2], [3, 3, 2, 1, 6], [5, 4, 3, 3, 3], [3, 4, 2, 2, 3], [0, 1]]
 g := ![![[2, 1, 1], []], ![[4, 4, 4, 2, 3, 3, 0, 1], [2, 6, 5, 3, 1, 6, 6, 1]], ![[1, 0, 5, 6, 5, 2, 4, 5], [0, 2, 0, 6, 5, 4, 2, 6]], ![[6, 2, 3, 5, 1, 6, 5, 5], [1, 1, 6, 5, 3, 3, 3, 6]], ![[4, 3, 2, 5, 0, 5, 0, 6], [2, 3, 6, 2, 6, 2, 4, 6]]]
 h' := ![![[4, 2, 0, 1, 2], [0, 0, 0, 1], [0, 1]], ![[3, 3, 2, 1, 6], [5, 3, 0, 2, 2], [4, 2, 0, 1, 2]], ![[5, 4, 3, 3, 3], [6, 1, 2, 4, 3], [3, 3, 2, 1, 6]], ![[3, 4, 2, 2, 3], [1, 1, 0, 1, 5], [5, 4, 3, 3, 3]], ![[0, 1], [3, 2, 5, 6, 4], [3, 4, 2, 2, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 1, 3, 5], [], [], []]
 b := ![[], [2, 0, 5, 4, 1], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 5
  hpos := by decide
  P := [5, 0, 1, 6, 6, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-148265299, -383481644, -153969032, -325356290, -146348314]
  a := ![0, -2, -4, -10, -13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-21180757, -54783092, -21995576, -46479470, -20906902]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 16807 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def PBC7 : ContainsPrimesAboveP 7 ![I7N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![7, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 7 (by decide) 𝕀

instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4, 2, 0, 1, 1]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![-4, 2, 0, 1, 1]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![2, 7, 10, 1, 0], ![5, 6, 1, 0, 1]] where
  M :=![![![-4, 2, 0, 1, 1], ![3, -1, 2, -1, 1], ![3, 12, -1, 9, -3], ![-3, -1, 1, 2, 3], ![6, 5, -1, 0, -1]]]
  hmulB := by decide  
  f := ![![![-2, 0, 0, 1, 1]], ![![3, 1, 0, -1, 1]], ![![3, 6, 1, -3, -3]], ![![4, 6, 1, -3, -2]], ![![1, 1, 0, 0, 1]]]
  g := ![![![-1, -1, -1, 1, 1], ![0, 0, 1, -1, 1], ![0, -3, -8, 9, -3], ![-2, -3, -2, 2, 3], ![1, 1, 0, 0, -1]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [3, 6, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 9, 2], [3, 1, 9], [0, 1]]
 g := ![![[1, 4, 9], [5, 0, 1], []], ![[6, 1, 8, 7], [8, 1, 3, 2], [3, 4]], ![[9, 1], [2, 3, 5, 3], [7, 4]]]
 h' := ![![[8, 9, 2], [7, 3, 8], [0, 0, 1], [0, 1]], ![[3, 1, 9], [9, 4, 3], [0, 4, 1], [8, 9, 2]], ![[0, 1], [8, 4], [10, 7, 9], [3, 1, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 5], []]
 b := ![[], [4, 6, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [3, 6, 0, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-94980324, -291839679, -126824824, -303074135, -132280198]
  a := ![3, -65, -62, -191, -186]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![106597176, 238487314, 276017884, -303074135, -132280198]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 1331 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -2, 0, -2, 0]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![-1, -2, 0, -2, 0]] 
 ![![11, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![-1, -2, 0, -2, 0], ![0, -1, -2, -2, -4], ![-12, -18, -1, -6, 0], ![0, -2, -2, -1, 0], ![0, -2, 0, -6, -1]]]
  hmulB := by decide  
  f := ![![![-683, -46, 56, 18, 184]], ![![-74, -5, 6, 2, 20]], ![![-475, -32, 39, 12, 128]], ![![-268, -18, 22, 7, 72]], ![![-293, -20, 24, 8, 79]]]
  g := ![![![1, -2, 0, -2, 0], ![4, -1, -2, -2, -4], ![5, -18, -1, -6, 0], ![2, -2, -2, -1, 0], ![3, -2, 0, -6, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1

def I11N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![122, 8, -10, -3, -33]] i)))

def SI11N2: IdealEqSpanCertificate' Table ![![122, 8, -10, -3, -33]] 
 ![![11, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![122, 8, -10, -3, -33], ![-99, -7, 8, 3, 27], ![81, 6, -7, -3, -21], ![39, 3, -3, -2, -11], ![-36, -3, 3, 2, 9]]]
  hmulB := by decide  
  f := ![![![4, 2, -6, -3, -9]], ![![-1, -3, -2, -3, -3]], ![![3, 0, -7, -3, -9]], ![![1, -1, -3, -3, -4]], ![![2, 1, -3, -2, -5]]]
  g := ![![![27, 8, -10, -3, -33], ![-22, -7, 8, 3, 27], ![18, 6, -7, -3, -21], ![9, 3, -3, -2, -11], ![-8, -3, 3, 2, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N2 : Nat.card (O ⧸ I11N2) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N2)

lemma isPrimeI11N2 : Ideal.IsPrime I11N2 := prime_ideal_of_norm_prime hp11.out _ NI11N2
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![-4, 2, 0, 1, 1]] ![![-1, -2, 0, -2, 0]]
  ![![4, 2, -6, -3, -9]] where
 M := ![![![4, 2, -6, -3, -9]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI11N1 : IdealMulLeCertificate' Table 
  ![![4, 2, -6, -3, -9]] ![![122, 8, -10, -3, -33]]
  ![![11, 0, 0, 0, 0]] where
 M := ![![![11, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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
instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0, 0]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0, 0, 0]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]] where
  M :=![![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 5 2 3 [4, 8, 11, 0, 8, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 5, 7, 4, 8], [9, 7, 10, 6, 8], [5, 0, 3, 9], [1, 0, 6, 7, 10], [0, 1]]
 g := ![![[9, 6, 5, 1, 1], [5, 1], []], ![[1, 6, 9, 0, 7, 11, 6, 6], [1, 12, 7, 9], [4, 1, 12, 1, 7, 12, 0, 5]], ![[5, 1, 9, 8, 0, 5, 8, 6], [4, 6, 1, 1], [5, 8, 3, 5, 7, 11, 7, 5]], ![[10, 7, 10, 6, 6, 11, 4], [3, 9, 9, 9], [1, 9, 0, 6, 1]], ![[3, 5, 4, 11, 11, 2, 0, 9], [5, 12, 4, 1], [12, 7, 2, 0, 8, 4, 2, 12]]]
 h' := ![![[3, 5, 7, 4, 8], [6, 8, 2, 2, 12], [0, 0, 0, 1], [0, 1]], ![[9, 7, 10, 6, 8], [0, 3, 12, 11, 11], [11, 8, 2, 11, 3], [3, 5, 7, 4, 8]], ![[5, 0, 3, 9], [7, 0, 6, 1, 2], [7, 4, 8, 2, 12], [9, 7, 10, 6, 8]], ![[1, 0, 6, 7, 10], [4, 4, 6, 7, 8], [4, 8, 12, 6, 10], [5, 0, 3, 9]], ![[0, 1], [5, 11, 0, 5, 6], [5, 6, 4, 6, 1], [1, 0, 6, 7, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 5, 8, 10], [], [], []]
 b := ![[], [12, 5, 7, 1, 2], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 5
  hpos := by decide
  P := [4, 8, 11, 0, 8, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-323533366, -745639102, -278607576, -547905514, -266804278]
  a := ![1, -4, -4, -13, -13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-24887182, -57356854, -21431352, -42146578, -20523406]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 371293 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def PBC13 : ContainsPrimesAboveP 13 ![I13N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![13, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 13 (by decide) 𝕀

instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4, 13, -3, 9, -19]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![4, 13, -3, 9, -19]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![15, 2, 10, 4, 1]] where
  M :=![![![4, 13, -3, 9, -19], ![-57, -62, 13, 29, 37], ![111, 93, -62, 33, 21], ![39, 29, 9, -78, -11], ![-36, 2, 10, 38, -67]]]
  hmulB := by decide  
  f := ![![![-94, -3, 9, 5, 27]], ![![81, 14, -3, 5, -17]], ![![-51, 21, 14, 21, 27]], ![![-27, 5, 5, 6, 11]], ![![-108, 13, 17, 19, 40]]]
  g := ![![![17, 3, 11, 5, -19], ![-36, -8, -21, -7, 37], ![-12, 3, -16, -3, 21], ![12, 3, 7, -2, -11], ![57, 8, 40, 18, -67]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 4 2 4 [11, 11, 15, 5, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 3, 16, 14], [7, 5, 3, 10], [13, 8, 15, 10], [0, 1]]
 g := ![![[10, 4, 16, 9], [5, 8, 8], [1], []], ![[9, 11, 2, 16, 7, 11], [10, 3, 2], [4, 13, 15], [9, 12, 9]], ![[13, 4, 6, 12, 13, 11], [13, 9, 1], [6, 16, 15], [10, 2, 15]], ![[7, 13, 9, 14], [11, 16, 15], [4], [4, 4, 15]]]
 h' := ![![[9, 3, 16, 14], [15, 14, 13, 3], [6, 6, 2, 12], [0, 0, 1], [0, 1]], ![[7, 5, 3, 10], [5, 13, 2, 6], [8, 14, 6, 11], [16, 10, 16, 7], [9, 3, 16, 14]], ![[13, 8, 15, 10], [10, 13, 9, 8], [0, 12, 7, 1], [7, 6, 2, 10], [7, 5, 3, 10]], ![[0, 1], [11, 11, 10], [9, 2, 2, 10], [6, 1, 15], [13, 8, 15, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [14, 5], []]
 b := ![[], [], [0, 9, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 4
  hpos := by decide
  P := [11, 11, 15, 5, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2410305538, 6513639255, 2670331873, 5950945023, 2703054819]
  a := ![1, 18, 23, 62, 71]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2243265691, 65148801, -1432953901, -285957309, 2703054819]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 83521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-94, -3, 9, 5, 27]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![-94, -3, 9, 5, 27]] 
 ![![17, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] where
  M :=![![![-94, -3, 9, 5, 27], ![81, 14, -3, 5, -17], ![-51, 21, 14, 21, 27], ![-27, 5, 5, 6, 11], ![30, 8, 0, 4, -5]]]
  hmulB := by decide  
  f := ![![![4, 13, -3, 9, -19]], ![![-1, 4, -1, 7, -9]], ![![7, 7, -4, 3, -1]], ![![3, 4, 0, -3, -4]], ![![0, 7, -1, 7, -14]]]
  g := ![![![-20, -3, 9, 5, 27], ![5, 14, -3, 5, -17], ![-35, 21, 14, 21, 27], ![-12, 5, 5, 6, 11], ![-1, 8, 0, 4, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![4, 13, -3, 9, -19]] ![![-94, -3, 9, 5, 27]]
  ![![17, 0, 0, 0, 0]] where
 M := ![![![17, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0, 0, 0]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0, 0, 0]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]] where
  M :=![![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 5 2 4 [6, 4, 18, 16, 9, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 12, 8, 4, 15], [2, 12, 9, 12, 9], [17, 15, 18, 2, 1], [13, 17, 3, 1, 13], [0, 1]]
 g := ![![[10, 4, 4, 12, 5], [0, 16, 8, 10, 1], [], []], ![[10, 8, 9, 10, 10, 3, 16, 12], [13, 18, 16, 11, 17, 8, 9, 10], [18, 0, 10, 17], [1, 7, 14, 16]], ![[16, 14, 0, 13, 13, 16, 8, 6], [5, 5, 14, 9, 1, 16, 15, 17], [9, 17, 10, 7], [18, 17, 0, 5]], ![[17, 4, 2, 4, 16, 11, 14, 4], [0, 3, 13, 17, 15, 13, 17, 17], [6, 17, 5, 4], [18, 12, 14, 1]], ![[15, 4, 1, 9, 5, 6, 7, 10], [2, 10, 6, 14, 8, 10, 11, 14], [11, 11], [8, 0, 6, 17]]]
 h' := ![![[16, 12, 8, 4, 15], [0, 18, 2, 0, 10], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[2, 12, 9, 12, 9], [7, 8, 18, 9, 15], [15, 18, 17, 17, 8], [3, 15, 4, 7, 13], [16, 12, 8, 4, 15]], ![[17, 15, 18, 2, 1], [3, 3, 15, 17, 8], [8, 2, 3, 16, 2], [10, 7, 16, 1, 8], [2, 12, 9, 12, 9]], ![[13, 17, 3, 1, 13], [16, 1, 8, 18, 17], [7, 12, 10, 5, 6], [10, 5, 1, 4, 17], [17, 15, 18, 2, 1]], ![[0, 1], [2, 8, 14, 13, 7], [2, 6, 8, 0, 2], [7, 11, 16, 7], [13, 17, 3, 1, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12, 16, 10, 4], [], [], []]
 b := ![[], [11, 6, 0, 3, 1], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 5
  hpos := by decide
  P := [6, 4, 18, 16, 9, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![23241978, 12531431, -6307221, -373038286, -381201218]
  a := ![-1, 2, -4, -5, -18]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1223262, 659549, -331959, -19633594, -20063222]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 2476099 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def PBC19 : ContainsPrimesAboveP 19 ![I19N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![19, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 19 (by decide) 𝕀

instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0, 0, 0]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0, 0, 0]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]] where
  M :=![![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 5 2 4 [12, 22, 15, 10, 4, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 3, 18, 0, 20], [5, 10, 19, 15, 1], [21, 10, 3, 5, 15], [10, 22, 6, 3, 10], [0, 1]]
 g := ![![[11, 18, 6, 2, 13], [2, 0, 19, 16, 16], [1], []], ![[22, 10, 22, 19, 18, 18, 20, 14], [11, 7, 21, 13, 22, 20, 14, 14], [13, 4, 7, 2, 20, 20, 12, 14], [9, 15, 10, 9]], ![[1, 14, 21, 13, 20, 5, 15, 13], [8, 12, 18, 7, 5, 2, 4, 6], [1, 1, 8, 12, 10, 16, 1, 18], [18, 11, 3, 1]], ![[1, 18, 15, 15, 6, 7, 5, 7], [12, 2, 12, 2, 3, 20, 13, 22], [0, 18, 2, 7, 4, 3, 10, 14], [6, 14, 9, 18]], ![[15, 11, 4, 2, 5, 13, 5, 10], [21, 7, 11, 0, 0, 17, 14, 15], [16, 14, 6, 4, 7, 13, 20, 11], [6, 6, 5, 8]]]
 h' := ![![[6, 3, 18, 0, 20], [22, 8, 17, 7, 17], [11, 1, 8, 13, 19], [0, 0, 1], [0, 1]], ![[5, 10, 19, 15, 1], [8, 2, 11, 4, 16], [13, 22, 13, 17, 16], [20, 3, 8, 17, 7], [6, 3, 18, 0, 20]], ![[21, 10, 3, 5, 15], [18, 1, 8, 3, 17], [3, 10, 17, 7, 12], [16, 9, 18, 15, 8], [5, 10, 19, 15, 1]], ![[10, 22, 6, 3, 10], [9, 14, 2, 0, 18], [21, 4, 17, 2, 16], [1, 5, 19, 0, 21], [21, 10, 3, 5, 15]], ![[0, 1], [15, 21, 8, 9, 1], [12, 9, 14, 7, 6], [5, 6, 0, 14, 10], [10, 22, 6, 3, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17, 8, 4, 3], [], [], []]
 b := ![[], [16, 16, 1, 13, 1], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 5
  hpos := by decide
  P := [12, 22, 15, 10, 4, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-625627140, -644054464, 297618160, -106007368, 193130816]
  a := ![0, -10, 4, -14, 12]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-27201180, -28002368, 12939920, -4609016, 8396992]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 6436343 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def PBC23 : ContainsPrimesAboveP 23 ![I23N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![23, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 23 (by decide) 𝕀



lemma PB140I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB140I0 : PrimesBelowBoundCertificateInterval O 1 23 140 where
  m := 9
  g := ![5, 5, 5, 1, 3, 1, 2, 1, 1]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB140I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N0, I3N0, I3N0, I3N0]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0]
    · exact ![I11N0, I11N1, I11N2]
    · exact ![I13N0]
    · exact ![I17N0, I17N1]
    · exact ![I19N0]
    · exact ![I23N0]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2, 2, 2, 2, 2]
    · exact ![3, 3, 3, 3, 3]
    · exact ![5, 5, 5, 5, 5]
    · exact ![16807]
    · exact ![1331, 11, 11]
    · exact ![371293]
    · exact ![83521, 17]
    · exact ![2476099]
    · exact ![6436343]
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
      exact NI2N2
      exact NI2N2
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N0
      exact NI3N0
      exact NI3N0
      exact NI3N0
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N0
      exact NI5N0
      exact NI5N0
      exact NI5N0
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
      exact NI11N2
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
  β := ![I2N0, I2N1, I2N2, I3N0, I5N0, I11N1, I11N2, I17N1]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N0, I3N0, I3N0, I3N0], [I5N0, I5N0, I5N0, I5N0, I5N0], [], [I11N1, I11N2], [], [I17N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
