
import IdealArithmetic.Examples.NF3_3_653844_1.RI3_3_653844_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1442, 37, -34]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![1442, 37, -34]] 
 ![![2, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![1442, 37, -34], ![-4692, -122, 111], ![5106, 138, -122]]]
  hmulB := by decide  
  f := ![![![-434, -178, -41]], ![![-2829, -1160, -267]], ![![-12282, -5037, -1160]]]
  g := ![![![721, 37, -34], ![-2346, -122, 111], ![2553, 138, -122]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![1442, 37, -34]] ![![1442, 37, -34]]
  ![![1732156, 44148, -40773]] where
 M := ![![![1732156, 44148, -40773]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI2N1 : IdealMulLeCertificate' Table 
  ![![1732156, 44148, -40773]] ![![1442, 37, -34]]
  ![![2, 0, 0]] where
 M := ![![![2082439598, 53077042, -49018570]]]
 hmul := by decide  
 g := ![![![![1041219799, 26538521, -24509285]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-35, -6, 2]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![-35, -6, 2]] 
 ![![3, 0, 0], ![0, 1, 0], ![2, 0, 1]] where
  M :=![![![-35, -6, 2], ![276, 57, -18], ![-828, -184, 57]]]
  hmulB := by decide  
  f := ![![![63, 26, 6]], ![![276, 113, 26]], ![![1238, 508, 117]]]
  g := ![![![-13, -6, 2], ![104, 57, -18], ![-314, -184, 57]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![57, 13, -4]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![57, 13, -4]] 
 ![![3, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![57, 13, -4], ![-552, -127, 39], ![1794, 414, -127]]]
  hmulB := by decide  
  f := ![![![17, 5, 1]], ![![46, 21, 5]], ![![230, 92, 21]]]
  g := ![![![19, 13, -4], ![-184, -127, 39], ![598, 414, -127]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![-35, -6, 2]] ![![-35, -6, 2]]
  ![![-2087, -500, 152]] where
 M := ![![![-2087, -500, 152]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![-2087, -500, 152]] ![![57, 13, -4]]
  ![![3, 0, 0]] where
 M := ![![![429729, 99297, -30456]]]
 hmul := by decide  
 g := ![![![![143243, 33099, -10152]]]]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![5, 0, 0]] 
 ![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P5P0 : CertificateIrreducibleZModOfList' 5 3 2 2 [4, 4, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 3, 4], [3, 1, 1], [0, 1]]
 g := ![![[0, 3, 1], []], ![[3, 1, 4, 4], [2, 1]], ![[2, 0, 3, 4], [0, 1]]]
 h' := ![![[0, 3, 4], [0, 0, 1], [0, 1]], ![[3, 1, 1], [2, 3, 1], [0, 3, 4]], ![[0, 1], [4, 2, 3], [3, 1, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 4], []]
 b := ![[], [4, 0, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where
  n := 3
  hpos := by decide
  P := [4, 4, 2, 1]
  hirr := P5P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-25250, -10860, -2850]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5050, -2172, -570]
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

instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0]] 
 ![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 3 2 2 [6, 1, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 0, 5], [6, 6, 2], [0, 1]]
 g := ![![[1], [1]], ![[6, 5, 0, 6], [6, 6, 0, 6]], ![[4, 6, 2, 1], [3, 0, 2, 1]]]
 h' := ![![[1, 0, 5], [1, 6], [0, 1]], ![[6, 6, 2], [0, 0, 2], [1, 0, 5]], ![[0, 1], [2, 1, 5], [6, 6, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2], []]
 b := ![[], [3, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 3
  hpos := by decide
  P := [6, 1, 0, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-169736, 4270, 53382]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-24248, 610, 7626]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 343 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def PBC7 : ContainsPrimesAboveP 7 ![I7N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![7, 0, 0]]) timesTableT_eq_Table B_one_repr 7 (by decide) 𝕀

instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13, -4, 0]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![-13, -4, 0]] 
 ![![11, 0, 0], ![6, 1, 0], ![10, 0, 1]] where
  M :=![![![-13, -4, 0], ![0, -13, -12], ![-552, -184, -13]]]
  hmulB := by decide  
  f := ![![![-2039, -52, 48]], ![![-510, -13, 12]], ![![-2506, -64, 59]]]
  g := ![![![1, -4, 0], ![18, -13, -12], ![62, -184, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N0 : Nat.card (O ⧸ I11N0) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N0)

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := prime_ideal_of_norm_prime hp11.out _ NI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-125, -3, 3]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![-125, -3, 3]] 
 ![![11, 0, 0], ![7, 1, 0], ![2, 0, 1]] where
  M :=![![![-125, -3, 3], ![414, 13, -9], ![-414, 0, 13]]]
  hmulB := by decide  
  f := ![![![-169, -39, 12]], ![![43, 10, -3]], ![![-520, -120, 37]]]
  g := ![![![-10, -3, 3], ![31, 13, -9], ![-40, 0, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1

def I11N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, -1, 0]] i)))

def SI11N2: IdealEqSpanCertificate' Table ![![13, -1, 0]] 
 ![![11, 0, 0], ![9, 1, 0], ![6, 0, 1]] where
  M :=![![![13, -1, 0], ![0, 13, -3], ![-138, -46, 13]]]
  hmulB := by decide  
  f := ![![![-31, -13, -3]], ![![-63, -26, -6]], ![![-180, -74, -17]]]
  g := ![![![2, -1, 0], ![-9, 13, -3], ![18, -46, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N2 : Nat.card (O ⧸ I11N2) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N2)

lemma isPrimeI11N2 : Ideal.IsPrime I11N2 := prime_ideal_of_norm_prime hp11.out _ NI11N2
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![-13, -4, 0]] ![![-125, -3, 3]]
  ![![-31, -13, -3]] where
 M := ![![![-31, -13, -3]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI11N1 : IdealMulLeCertificate' Table 
  ![![-31, -13, -3]] ![![13, -1, 0]]
  ![![11, 0, 0]] where
 M := ![![![11, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0]] 
 ![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [10, 1, 11, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 8, 3], [0, 4, 10], [0, 1]]
 g := ![![[5, 9, 3], [4, 4], [1]], ![[8, 0, 5, 9], [12, 12], [11, 12, 10, 1]], ![[0, 12], [10, 10], [2, 4, 2, 12]]]
 h' := ![![[2, 8, 3], [8, 2, 4], [3, 12, 2], [0, 1]], ![[0, 4, 10], [1, 1, 9], [2, 4, 5], [2, 8, 3]], ![[0, 1], [1, 10], [6, 10, 6], [0, 4, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 12], []]
 b := ![[], [3, 11, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [10, 1, 11, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-154076, 21047, -21866]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-11852, 1619, -1682]
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

instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3721, -114, 92]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![-3721, -114, 92]] 
 ![![17, 0, 0], ![0, 17, 0], ![10, 8, 1]] where
  M :=![![![-3721, -114, 92], ![12696, 511, -342], ![-15732, -1012, 511]]]
  hmulB := by decide  
  f := ![![![4999, 2050, 472]], ![![65136, 26711, 6150]], ![![50234, 20600, 4743]]]
  g := ![![![-273, -50, 92], ![948, 191, -342], ![-1226, -300, 511]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 2 2 4 [6, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 16], [0, 1]]
 g := ![![[16, 9], [13], [2], [1]], ![[2, 8], [13], [2], [1]]]
 h' := ![![[6, 16], [5, 3], [7, 8], [11, 6], [0, 1]], ![[0, 1], [6, 14], [4, 9], [13, 11], [6, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [9, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 2
  hpos := by decide
  P := [6, 11, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-810, 151, 378]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-270, -169, 378]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4999, -2050, -472]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![-4999, -2050, -472]] 
 ![![17, 0, 0], ![10, 1, 0], ![12, 0, 1]] where
  M :=![![![-4999, -2050, -472], ![-65136, -26711, -6150], ![-282900, -116012, -26711]]]
  hmulB := by decide  
  f := ![![![3721, 114, -92]], ![![1442, 37, -34]], ![![3552, 140, -95]]]
  g := ![![![1245, -2050, -472], ![16222, -26711, -6150], ![70456, -116012, -26711]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![-3721, -114, 92]] ![![-4999, -2050, -472]]
  ![![17, 0, 0]] where
 M := ![![![-17, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-43, -10, 3]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![-43, -10, 3]] 
 ![![19, 0, 0], ![7, 1, 0], ![9, 0, 1]] where
  M :=![![![-43, -10, 3], ![414, 95, -30], ![-1380, -322, 95]]]
  hmulB := by decide  
  f := ![![![635, 16, -15]], ![![125, 3, -3]], ![![417, 10, -10]]]
  g := ![![![0, -10, 3], ![1, 95, -30], ![1, -322, 95]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N0 : Nat.card (O ⧸ I19N0) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N0)

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := prime_ideal_of_norm_prime hp19.out _ NI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![95, 39, 9]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![95, 39, 9]] 
 ![![19, 0, 0], ![13, 1, 0], ![7, 0, 1]] where
  M :=![![![95, 39, 9], ![1242, 509, 117], ![5382, 2208, 509]]]
  hmulB := by decide  
  f := ![![![-745, -21, 18]], ![![-379, -10, 9]], ![![-427, -15, 11]]]
  g := ![![![-25, 39, 9], ![-326, 509, 117], ![-1415, 2208, 509]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1

def I19N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![20519, 523, -483]] i)))

def SI19N2: IdealEqSpanCertificate' Table ![![20519, 523, -483]] 
 ![![19, 0, 0], ![18, 1, 0], ![6, 0, 1]] where
  M :=![![![20519, 523, -483], ![-66654, -1699, 1569], ![72174, 1840, -1699]]]
  hmulB := by decide  
  f := ![![![359, 143, 30]], ![![558, 227, 51]], ![![1152, 464, 101]]]
  g := ![![![737, 523, -483], ![-2394, -1699, 1569], ![2592, 1840, -1699]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N2 : Nat.card (O ⧸ I19N2) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N2)

lemma isPrimeI19N2 : Ideal.IsPrime I19N2 := prime_ideal_of_norm_prime hp19.out _ NI19N2
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![-43, -10, 3]] ![![95, 39, 9]]
  ![![-359, -143, -30]] where
 M := ![![![-359, -143, -30]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI19N1 : IdealMulLeCertificate' Table 
  ![![-359, -143, -30]] ![![20519, 523, -483]]
  ![![19, 0, 0]] where
 M := ![![![-19, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC19 : ContainsPrimesAboveP 19 ![I19N0, I19N1, I19N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N1
    exact isPrimeI19N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 19 (by decide) (𝕀 ⊙ MulI19N0 ⊙ MulI19N1)

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-23, -6, 1]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![-23, -6, 1]] 
 ![![23, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![-23, -6, 1], ![138, 23, -18], ![-828, -230, 23]]]
  hmulB := by decide  
  f := ![![![3611, 92, -85]], ![![-510, -13, 12]], ![![552, 14, -13]]]
  g := ![![![-1, -6, 1], ![6, 23, -18], ![-36, -230, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N0 : Nat.card (O ⧸ I23N0) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N0)

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := prime_ideal_of_norm_prime hp23.out _ NI23N0
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![-23, -6, 1]] ![![-23, -6, 1]]
  ![![-1127, -230, 108]] where
 M := ![![![-1127, -230, 108]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI23N1 : IdealMulLeCertificate' Table 
  ![![-1127, -230, 108]] ![![-23, -6, 1]]
  ![![23, 0, 0]] where
 M := ![![![-95243, -23368, 5497]]]
 hmul := by decide  
 g := ![![![![-4141, -1016, 239]]]]
 hle2 := by decide  

def PBC23 : ContainsPrimesAboveP 23 ![I23N0, I23N0, I23N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
    exact isPrimeI23N0
    exact isPrimeI23N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 23 (by decide) (𝕀 ⊙ MulI23N0 ⊙ MulI23N1)
instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2351, 544, -166]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![2351, 544, -166]] 
 ![![29, 0, 0], ![0, 29, 0], ![22, 10, 1]] where
  M :=![![![2351, 544, -166], ![-22908, -5285, 1632], ![75072, 17388, -5285]]]
  hmulB := by decide  
  f := ![![![15379, 392, -362]], ![![-49956, -1273, 1176]], ![![-3694, -94, 87]]]
  g := ![![![207, 76, -166], ![-2028, -745, 1632], ![6598, 2422, -5285]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [6, 23, 1] where
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
 g := ![![[28, 5], [25], [21, 1], [6, 1]], ![[0, 24], [25], [27, 28], [12, 28]]]
 h' := ![![[6, 28], [8, 18], [19, 24], [22, 1], [0, 1]], ![[0, 1], [0, 11], [18, 5], [28, 28], [6, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [15, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [6, 23, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![282, 115, 26]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10, -5, 26]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-15379, -392, 362]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![-15379, -392, 362]] 
 ![![29, 0, 0], ![28, 1, 0], ![19, 0, 1]] where
  M :=![![![-15379, -392, 362], ![49956, 1273, -1176], ![-54096, -1380, 1273]]]
  hmulB := by decide  
  f := ![![![-2351, -544, 166]], ![![-1480, -343, 104]], ![![-4129, -956, 291]]]
  g := ![![![-389, -392, 362], ![1264, 1273, -1176], ![-1367, -1380, 1273]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![2351, 544, -166]] ![![-15379, -392, 362]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![138349, 3541, -3260]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![138349, 3541, -3260]] 
 ![![31, 0, 0], ![0, 31, 0], ![7, 11, 1]] where
  M :=![![![138349, 3541, -3260], ![-449880, -11611, 10623], ![488658, 12926, -11611]]]
  hmulB := by decide  
  f := ![![![-80567, -33039, -7607]], ![![-1049766, -430489, -99117]], ![![-537767, -220528, -50775]]]
  g := ![![![5199, 1271, -3260], ![-16911, -4144, 10623], ![18385, 4537, -11611]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [19, 28, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 30], [0, 1]]
 g := ![![[8, 18], [6, 16], [14, 7], [3, 1]], ![[0, 13], [23, 15], [4, 24], [6, 30]]]
 h' := ![![[3, 30], [10, 7], [13, 27], [5, 21], [0, 1]], ![[0, 1], [0, 24], [1, 4], [6, 10], [3, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [18, 19]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [19, 28, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5292, 2364, 1159]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-91, -335, 1159]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![80567, 33039, 7607]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![80567, 33039, 7607]] 
 ![![31, 0, 0], ![29, 1, 0], ![9, 0, 1]] where
  M :=![![![80567, 33039, 7607], ![1049766, 430489, 99117], ![4559382, 1869716, 430489]]]
  hmulB := by decide  
  f := ![![![-138349, -3541, 3260]], ![![-114911, -2938, 2707]], ![![-55929, -1445, 1321]]]
  g := ![![![-30517, 33039, 7607], ![-397628, 430489, 99117], ![-1726993, 1869716, 430489]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![138349, 3541, -3260]] ![![80567, 33039, 7607]]
  ![![31, 0, 0]] where
 M := ![![![-31, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


lemma PB180I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB180I0 : PrimesBelowBoundCertificateInterval O 1 31 180 where
  m := 11
  g := ![3, 3, 1, 1, 3, 1, 2, 3, 3, 2, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB180I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N0, I2N0]
    · exact ![I3N0, I3N0, I3N1]
    · exact ![I5N0]
    · exact ![I7N0]
    · exact ![I11N0, I11N1, I11N2]
    · exact ![I13N0]
    · exact ![I17N0, I17N1]
    · exact ![I19N0, I19N1, I19N2]
    · exact ![I23N0, I23N0, I23N0]
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
    · exact ![343]
    · exact ![11, 11, 11]
    · exact ![2197]
    · exact ![289, 17]
    · exact ![19, 19, 19]
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
      exact NI3N0
      exact NI3N1
    · dsimp ; intro j
      fin_cases j
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
      exact NI19N1
      exact NI19N2
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N0
      exact NI23N0
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
  β := ![I2N0, I3N0, I3N1, I5N0, I11N0, I11N1, I11N2, I17N1, I19N0, I19N1, I19N2, I23N0, I29N1, I31N1]
  Il := ![[I2N0, I2N0, I2N0], [I3N0, I3N0, I3N1], [I5N0], [], [I11N0, I11N1, I11N2], [], [I17N1], [I19N0, I19N1, I19N2], [I23N0, I23N0, I23N0], [I29N1], [I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
