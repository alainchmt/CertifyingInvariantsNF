
import IdealArithmetic.Examples.NF3_3_50172_1.RI3_3_50172_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-386, 3, 24]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![-386, 3, 24]] 
 ![![2, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![-386, 3, 24], ![-144, 1, 9], ![30, 0, -2]]]
  hmulB := by decide  
  f := ![![![2, -6, -3]], ![![9, -26, -9]], ![![15, -45, -23]]]
  g := ![![![-193, 3, 24], ![-72, 1, 9], ![15, 0, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 3, 1]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![3, 3, 1]] 
 ![![2, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![3, 3, 1], ![-6, 22, 9], ![-16, 46, 19]]]
  hmulB := by decide  
  f := ![![![-4, 11, -5]], ![![13, -31, 14]], ![![-38, 93, -42]]]
  g := ![![![0, 3, 1], ![-14, 22, 9], ![-31, 46, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![-386, 3, 24]] ![![-386, 3, 24]]
  ![![149284, -1155, -9285]] where
 M := ![![![149284, -1155, -9285]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI2N1 : IdealMulLeCertificate' Table 
  ![![149284, -1155, -9285]] ![![3, 3, 1]]
  ![![2, 0, 0]] where
 M := ![![![603342, -4668, -37526]]]
 hmul := by decide  
 g := ![![![![301671, -2334, -18763]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N0, I2N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N0
    exact isPrimeI2N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, -1]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![17, 0, -1]] 
 ![![3, 0, 0], ![0, 1, 0], ![1, 0, 1]] where
  M :=![![![17, 0, -1], ![6, 1, 0], ![-2, 2, 1]]]
  hmulB := by decide  
  f := ![![![1, -2, 1]], ![![-2, 5, -2]], ![![5, -12, 6]]]
  g := ![![![6, 0, -1], ![2, 1, 0], ![-1, 2, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, -22, 10]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![9, -22, 10]] 
 ![![3, 0, 0], ![2, 1, 0], ![2, 0, 1]] where
  M :=![![![9, -22, 10], ![-60, 147, -66], ![152, -372, 169]]]
  hmulB := by decide  
  f := ![![![291, -2, -18]], ![![230, -1, -14]], ![![186, 0, -11]]]
  g := ![![![11, -22, 10], ![-74, 147, -66], ![186, -372, 169]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![17, 0, -1]] ![![17, 0, -1]]
  ![![291, -2, -18]] where
 M := ![![![291, -2, -18]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![291, -2, -18]] ![![9, -22, 10]]
  ![![3, 0, 0]] where
 M := ![![![3, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N0, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1)
instance hp5 : Fact (Nat.Prime 5) := {out := by norm_num}

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 2, 1]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![-1, 2, 1]] 
 ![![5, 0, 0], ![0, 5, 0], ![4, 2, 1]] where
  M :=![![![-1, 2, 1], ![-6, 17, 6], ![-10, 30, 15]]]
  hmulB := by decide  
  f := ![![![-15, 0, 1]], ![![-6, 1, 0]], ![![-14, 0, 1]]]
  g := ![![![-1, 0, 1], ![-6, 1, 6], ![-14, 0, 15]]]
  hle1 := by decide   
  hle2 := by decide  


def P5P0 : CertificateIrreducibleZModOfList' 5 2 2 2 [3, 0, 1] where
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
 h' := ![![[0, 4], [2], [0, 1]], ![[0, 1], [2], [0, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [0, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where
  n := 2
  hpos := by decide
  P := [3, 0, 1]
  hirr := P5P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-67, 274, 412]
  a := ![0, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-343, -110, 412]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI5N0 B_one_repr
lemma NI5N0 : Nat.card (O ⧸ I5N0) = 25 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-15, 0, 1]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![-15, 0, 1]] 
 ![![5, 0, 0], ![4, 1, 0], ![0, 0, 1]] where
  M :=![![![-15, 0, 1], ![-6, 1, 0], ![2, -2, 1]]]
  hmulB := by decide  
  f := ![![![-1, 2, 1]], ![![-2, 5, 2]], ![![-2, 6, 3]]]
  g := ![![![-3, 0, 1], ![-2, 1, 0], ![2, -2, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![-1, 2, 1]] ![![-15, 0, 1]]
  ![![5, 0, 0]] where
 M := ![![![5, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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
instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, -654, -270]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![223, -654, -270]] 
 ![![7, 0, 0], ![0, 7, 0], ![2, 6, 1]] where
  M :=![![![223, -654, -270], ![1620, -4751, -1962], ![3384, -9924, -4097]]]
  hmulB := by decide  
  f := ![![![-863, 6, 54]], ![![-324, 7, 18]], ![![-514, 6, 31]]]
  g := ![![![109, 138, -270], ![792, 1003, -1962], ![1654, 2094, -4097]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 2 2 2 [3, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 6], [0, 1]]
 g := ![![[4, 1], [2, 1]], ![[6, 6], [4, 6]]]
 h' := ![![[2, 6], [1, 1], [0, 1]], ![[0, 1], [3, 6], [2, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [5, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 2
  hpos := by decide
  P := [3, 5, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11, 114, 418]
  a := ![-1, 1, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-121, -342, 418]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-863, 6, 54]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![-863, 6, 54]] 
 ![![7, 0, 0], ![3, 1, 0], ![3, 0, 1]] where
  M :=![![![-863, 6, 54], ![-324, 7, 18], ![72, -12, 1]]]
  hmulB := by decide  
  f := ![![![223, -654, -270]], ![![327, -959, -396]], ![![579, -1698, -701]]]
  g := ![![![-149, 6, 54], ![-57, 7, 18], ![15, -12, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![223, -654, -270]] ![![-863, 6, 54]]
  ![![7, 0, 0]] where
 M := ![![![7, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0)
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


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [10, 6, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 1, 10], [2, 9, 1], [0, 1]]
 g := ![![[5, 8, 5], [10, 7, 1], []], ![[8, 0, 3, 8], [9, 4, 10, 7], [5, 1]], ![[4, 7, 10, 4], [9, 2, 10, 1], [3, 1]]]
 h' := ![![[5, 1, 10], [10, 2, 7], [0, 0, 1], [0, 1]], ![[2, 9, 1], [10, 1, 6], [8, 3, 9], [5, 1, 10]], ![[0, 1], [8, 8, 9], [7, 8, 1], [2, 9, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7], []]
 b := ![[], [6, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [10, 6, 4, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-246554, 440, -15048]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-22414, 40, -1368]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2451, 7188, 2968]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![-2451, 7188, 2968]] 
 ![![13, 0, 0], ![0, 13, 0], ![8, 3, 1]] where
  M :=![![![-2451, 7188, 2968], ![-17808, 52225, 21564], ![-37192, 109072, 45037]]]
  hmulB := by decide  
  f := ![![![2209, -20, -136]], ![![816, 13, -60]], ![![1536, -13, -95]]]
  g := ![![![-2015, -132, 2968], ![-14640, -959, 21564], ![-30576, -2003, 45037]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [12, 12, 1] where
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
 g := ![![[1, 12], [4], [1, 1]], ![[0, 1], [4], [2, 12]]]
 h' := ![![[1, 12], [5, 8], [1, 2], [0, 1]], ![[0, 1], [0, 5], [3, 11], [1, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [8, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 2
  hpos := by decide
  P := [12, 12, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-45, 326, 698]
  a := ![1, -2, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-433, -136, 698]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2209, 20, 136]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![-2209, 20, 136]] 
 ![![13, 0, 0], ![4, 1, 0], ![2, 0, 1]] where
  M :=![![![-2209, 20, 136], ![-816, -13, 60], ![152, 48, -33]]]
  hmulB := by decide  
  f := ![![![2451, -7188, -2968]], ![![2124, -6229, -2572]], ![![3238, -9496, -3921]]]
  g := ![![![-197, 20, 136], ![-68, -13, 60], ![2, 48, -33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![-2451, 7188, 2968]] ![![-2209, 20, 136]]
  ![![13, 0, 0]] where
 M := ![![![-13, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-21, -18, 10]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![-21, -18, 10]] 
 ![![17, 0, 0], ![0, 17, 0], ![3, 5, 1]] where
  M :=![![![-21, -18, 10], ![-60, 121, -54], ![128, -308, 139]]]
  hmulB := by decide  
  f := ![![![11, -34, -14]], ![![84, -247, -102]], ![![37, -109, -45]]]
  g := ![![![-3, -4, 10], ![6, 23, -54], ![-17, -59, 139]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 2 2 4 [3, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 16], [0, 1]]
 g := ![![[1, 16], [13], [9], [1]], ![[4, 1], [13], [9], [1]]]
 h' := ![![[14, 16], [13, 13], [16, 8], [14, 14], [0, 1]], ![[0, 1], [8, 4], [9, 9], [6, 3], [14, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [1, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 2
  hpos := by decide
  P := [3, 3, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-67, 268, 397]
  a := ![0, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-74, -101, 397]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, -34, -14]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![11, -34, -14]] 
 ![![17, 0, 0], ![2, 1, 0], ![15, 0, 1]] where
  M :=![![![11, -34, -14], ![84, -247, -102], ![176, -516, -213]]]
  hmulB := by decide  
  f := ![![![-21, -18, 10]], ![![-6, 5, -2]], ![![-11, -34, 17]]]
  g := ![![![17, -34, -14], ![124, -247, -102], ![259, -516, -213]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![-21, -18, 10]] ![![11, -34, -14]]
  ![![17, 0, 0]] where
 M := ![![![17, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9, -4, -1]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![-9, -4, -1]] 
 ![![19, 0, 0], ![0, 19, 0], ![9, 4, 1]] where
  M :=![![![-9, -4, -1], ![6, -29, -12], ![22, -62, -25]]]
  hmulB := by decide  
  f := ![![![-1, -2, 1]], ![![-6, 13, -6]], ![![-1, 0, 0]]]
  g := ![![![0, 0, -1], ![6, 1, -12], ![13, 2, -25]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [18, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 18], [0, 1]]
 g := ![![[12, 17], [3, 16], [11], [1]], ![[7, 2], [5, 3], [11], [1]]]
 h' := ![![[12, 18], [3, 6], [12, 4], [1, 12], [0, 1]], ![[0, 1], [18, 13], [3, 15], [12, 7], [12, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [16, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [18, 7, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6452, 23458, 28465]
  a := ![1, 20, 41]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-13823, -4758, 28465]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -2, 1]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![-1, -2, 1]] 
 ![![19, 0, 0], ![7, 1, 0], ![13, 0, 1]] where
  M :=![![![-1, -2, 1], ![-6, 13, -6], ![14, -34, 15]]]
  hmulB := by decide  
  f := ![![![-9, -4, -1]], ![![-3, -3, -1]], ![![-5, -6, -2]]]
  g := ![![![0, -2, 1], ![-1, 13, -6], ![3, -34, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![-9, -4, -1]] ![![-1, -2, 1]]
  ![![19, 0, 0]] where
 M := ![![![19, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0]] 
 ![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [14, 12, 20, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 12, 19], [11, 10, 4], [0, 1]]
 g := ![![[17, 8, 6], [9, 19, 8], [20, 3, 1], []], ![[20, 3, 2, 19], [19, 17, 16, 21], [10, 17, 11, 14], [21, 16]], ![[12, 15, 10, 1], [11, 6, 17, 18], [20, 2, 21, 1], [13, 16]]]
 h' := ![![[15, 12, 19], [12, 10, 11], [19, 17, 10], [0, 0, 1], [0, 1]], ![[11, 10, 4], [1, 17, 1], [21, 10, 9], [0, 22, 10], [15, 12, 19]], ![[0, 1], [3, 19, 11], [10, 19, 4], [8, 1, 12], [11, 10, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 21], []]
 b := ![[], [7, 11, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [14, 12, 20, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5037, 15824, 10971]
  a := ![-1, 2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-219, 688, 477]
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

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![57, -106, 47]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![57, -106, 47]] 
 ![![29, 0, 0], ![0, 29, 0], ![8, 7, 1]] where
  M :=![![![57, -106, 47], ![-282, 703, -318], ![730, -1790, 809]]]
  hmulB := by decide  
  f := ![![![-17, 56, 23]], ![![-138, 407, 168]], ![![-48, 143, 59]]]
  g := ![![![-11, -15, 47], ![78, 101, -318], ![-198, -257, 809]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [18, 25, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 28], [0, 1]]
 g := ![![[3, 23], [7], [14, 4], [4, 1]], ![[8, 6], [7], [1, 25], [8, 28]]]
 h' := ![![[4, 28], [13, 20], [9, 6], [15, 27], [0, 1]], ![[0, 1], [6, 9], [4, 23], [7, 2], [4, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [2, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [18, 25, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-142, 724, 1251]
  a := ![0, 3, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-350, -277, 1251]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, -56, -23]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![17, -56, -23]] 
 ![![29, 0, 0], ![8, 1, 0], ![5, 0, 1]] where
  M :=![![![17, -56, -23], ![138, -407, -168], ![290, -850, -351]]]
  hmulB := by decide  
  f := ![![![-57, 106, -47]], ![![-6, 5, -2]], ![![-35, 80, -36]]]
  g := ![![![20, -56, -23], ![146, -407, -168], ![305, -850, -351]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![57, -106, 47]] ![![17, -56, -23]]
  ![![29, 0, 0]] where
 M := ![![![-29, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0]] 
 ![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 3 2 4 [1, 7, 16, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 19, 18], [7, 11, 13], [0, 1]]
 g := ![![[23, 20, 25], [13, 24, 20], [8, 3, 8], [1]], ![[11, 5, 3, 16], [16, 2, 23, 4], [3, 13, 11, 5], [30, 29, 21, 4]], ![[7, 30, 22, 29], [17, 25, 18, 13], [13, 15, 30, 26], [30, 4, 30, 27]]]
 h' := ![![[8, 19, 18], [18, 11, 5], [23, 4, 12], [30, 24, 15], [0, 1]], ![[7, 11, 13], [17, 5, 5], [15, 8, 18], [17, 30, 8], [8, 19, 18]], ![[0, 1], [30, 15, 21], [19, 19, 1], [3, 8, 8], [7, 11, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 20], []]
 b := ![[], [25, 3, 23], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 3
  hpos := by decide
  P := [1, 7, 16, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![319207, -1009608, -738234]
  a := ![2, -8, -14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![10297, -32568, -23814]
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



lemma PB50I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB50I0 : PrimesBelowBoundCertificateInterval O 1 31 50 where
  m := 11
  g := ![3, 3, 2, 2, 1, 2, 2, 2, 1, 2, 1]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB50I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N0, I2N1]
    · exact ![I3N0, I3N0, I3N1]
    · exact ![I5N0, I5N1]
    · exact ![I7N0, I7N1]
    · exact ![I11N0]
    · exact ![I13N0, I13N1]
    · exact ![I17N0, I17N1]
    · exact ![I19N0, I19N1]
    · exact ![I23N0]
    · exact ![I29N0, I29N1]
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
    · exact ![3, 3, 3]
    · exact ![25, 5]
    · exact ![49, 7]
    · exact ![1331]
    · exact ![169, 13]
    · exact ![289, 17]
    · exact ![361, 19]
    · exact ![12167]
    · exact ![841, 29]
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
      exact NI2N1
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
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
      exact NI17N1
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
  β := ![I2N0, I2N1, I3N0, I3N1, I5N0, I5N1, I7N0, I7N1, I13N1, I17N1, I19N1, I29N1]
  Il := ![[I2N0, I2N0, I2N1], [I3N0, I3N0, I3N1], [I5N0, I5N1], [I7N0, I7N1], [], [I13N1], [I17N1], [I19N1], [], [I29N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
