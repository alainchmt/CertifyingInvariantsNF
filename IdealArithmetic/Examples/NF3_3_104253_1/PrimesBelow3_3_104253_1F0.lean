
import IdealArithmetic.Examples.NF3_3_104253_1.RI3_3_104253_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp2 : Fact (Nat.Prime 2) := {out := by norm_num}

def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-18, 0, 1]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![-18, 0, 1]] 
 ![![2, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![-18, 0, 1], ![48, 7, 0], ![-16, 16, 7]]]
  hmulB := by decide  
  f := ![![![-49, -16, 7]], ![![168, 55, -24]], ![![-440, -144, 63]]]
  g := ![![![-9, 0, 1], ![24, 7, 0], ![-8, 16, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-49, -16, 7]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![-49, -16, 7]] 
 ![![2, 0, 0], ![0, 2, 0], ![1, 0, 1]] where
  M :=![![![-49, -16, 7], ![336, 110, -48], ![-880, -288, 126]]]
  hmulB := by decide  
  f := ![![![-18, 0, 1]], ![![48, 7, 0]], ![![-17, 8, 4]]]
  g := ![![![-28, -8, 7], ![192, 55, -48], ![-503, -144, 126]]]
  hle1 := by decide   
  hle2 := by decide  


def P2P1 : CertificateIrreducibleZModOfList' 2 2 2 1 [1, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 1], [0, 1]]
 g := ![![[1]], ![[1]]]
 h' := ![![[1, 1], [0, 1]], ![[0, 1], [1, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], []]
 b := ![[], [1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI2N1 : CertifiedPrimeIdeal' SI2N1 2 where
  n := 2
  hpos := by decide
  P := [1, 1, 1]
  hirr := P2P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![81, 650, 623]
  a := ![-1, 1, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-271, 325, 623]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI2N1 B_one_repr
lemma NI2N1 : Nat.card (O ⧸ I2N1) = 4 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![-18, 0, 1]] ![![-49, -16, 7]]
  ![![2, 0, 0]] where
 M := ![![![2, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11141, -3649, 1594]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![-11141, -3649, 1594]] 
 ![![3, 0, 0], ![0, 1, 0], ![1, 0, 1]] where
  M :=![![![-11141, -3649, 1594], ![76512, 25060, -10947], ![-200656, -65721, 28709]]]
  hmulB := by decide  
  f := ![![![-247, -133, -37]], ![![-592, -435, -133]], ![![-2013, -1350, -403]]]
  g := ![![![-4245, -3649, 1594], ![29153, 25060, -10947], ![-76455, -65721, 28709]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-413, -135, 59]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![-413, -135, 59]] 
 ![![3, 0, 0], ![2, 1, 0], ![2, 0, 1]] where
  M :=![![![-413, -135, 59], ![2832, 927, -405], ![-7424, -2431, 1062]]]
  hmulB := by decide  
  f := ![![![81, 59, 18]], ![![342, 236, 71]], ![![902, 627, 189]]]
  g := ![![![-87, -135, 59], ![596, 927, -405], ![-1562, -2431, 1062]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![-11141, -3649, 1594]] ![![-11141, -3649, 1594]]
  ![![-474916071, -155549705, 67948995]] where
 M := ![![![-474916071, -155549705, 67948995]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![-474916071, -155549705, 67948995]] ![![-413, -135, 59]]
  ![![3, 0, 0]] where
 M := ![![![-748829766117, -245264913795, 107139415026]]]
 hmul := by decide  
 g := ![![![![-249609922039, -81754971265, 35713138342]]]]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, -22, -8]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![-7, -22, -8]] 
 ![![5, 0, 0], ![0, 5, 0], ![4, 4, 1]] where
  M :=![![![-7, -22, -8], ![-384, -229, -66], ![-928, -678, -207]]]
  hmulB := by decide  
  f := ![![![-531, -174, 76]], ![![3648, 1195, -522]], ![![580, 190, -83]]]
  g := ![![![5, 2, -8], ![-24, 7, -66], ![-20, 30, -207]]]
  hle1 := by decide   
  hle2 := by decide  


def P5P0 : CertificateIrreducibleZModOfList' 5 2 2 2 [2, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 4], [0, 1]]
 g := ![![[2, 1], [1]], ![[3, 4], [1]]]
 h' := ![![[1, 4], [3, 1], [0, 1]], ![[0, 1], [4, 4], [1, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [2, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where
  n := 2
  hpos := by decide
  P := [2, 4, 1]
  hirr := P5P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3826, 16, 149]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![646, -116, 149]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI5N0 B_one_repr
lemma NI5N0 : Nat.card (O ⧸ I5N0) = 25 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-531, -174, 76]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![-531, -174, 76]] 
 ![![5, 0, 0], ![3, 1, 0], ![1, 0, 1]] where
  M :=![![![-531, -174, 76], ![3648, 1195, -522], ![-9568, -3134, 1369]]]
  hmulB := by decide  
  f := ![![![-7, -22, -8]], ![![-81, -59, -18]], ![![-187, -140, -43]]]
  g := ![![![-17, -174, 76], ![117, 1195, -522], ![-307, -3134, 1369]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![-7, -22, -8]] ![![-531, -174, 76]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0]] 
 ![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 3 2 2 [4, 0, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 5, 3], [1, 1, 4], [0, 1]]
 g := ![![[0, 1, 1], [1]], ![[5, 1, 2, 3], [5, 2, 1, 6]], ![[2, 3, 4, 2], [4, 4, 0, 1]]]
 h' := ![![[0, 5, 3], [3, 0, 1], [0, 1]], ![[1, 1, 4], [1, 6, 1], [0, 5, 3]], ![[0, 1], [6, 1, 5], [1, 1, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2], []]
 b := ![[], [0, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 3
  hpos := by decide
  P := [4, 0, 6, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-475125, -451528, -218295]
  a := ![1, -2, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-67875, -64504, -31185]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19, -7, 3]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![-19, -7, 3]] 
 ![![11, 0, 0], ![0, 11, 0], ![1, 5, 1]] where
  M :=![![![-19, -7, 3], ![144, 49, -21], ![-384, -127, 56]]]
  hmulB := by decide  
  f := ![![![7, 1, 0]], ![![0, 8, 3]], ![![5, 6, 2]]]
  g := ![![![-2, -2, 3], ![15, 14, -21], ![-40, -37, 56]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [2, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 10], [0, 1]]
 g := ![![[2, 1], [7, 5], [1]], ![[9, 10], [9, 6], [1]]]
 h' := ![![[7, 10], [8, 10], [9, 7], [0, 1]], ![[0, 1], [1, 1], [3, 4], [7, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [5, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 2
  hpos := by decide
  P := [2, 4, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![562, 896, 617]
  a := ![0, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5, -199, 617]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 1, 0]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![7, 1, 0]] 
 ![![11, 0, 0], ![7, 1, 0], ![7, 0, 1]] where
  M :=![![![7, 1, 0], ![0, 8, 3], ![48, 25, 7]]]
  hmulB := by decide  
  f := ![![![-19, -7, 3]], ![![1, 0, 0]], ![![-47, -16, 7]]]
  g := ![![![0, 1, 0], ![-7, 8, 3], ![-16, 25, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![-19, -7, 3]] ![![7, 1, 0]]
  ![![11, 0, 0]] where
 M := ![![![11, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![27, 9, -4]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![27, 9, -4]] 
 ![![13, 0, 0], ![0, 13, 0], ![3, 1, 1]] where
  M :=![![![27, 9, -4], ![-192, -64, 27], ![496, 161, -73]]]
  hmulB := by decide  
  f := ![![![-25, -1, 1]], ![![48, -1, -3]], ![![-7, -1, 0]]]
  g := ![![![3, 1, -4], ![-21, -7, 27], ![55, 18, -73]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [1, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 12], [0, 1]]
 g := ![![[7, 1], [3], [6, 1]], ![[0, 12], [3], [12, 12]]]
 h' := ![![[6, 12], [7, 1], [7, 9], [0, 1]], ![[0, 1], [0, 12], [9, 4], [6, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [1, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 2
  hpos := by decide
  P := [1, 7, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![51833, 68476, 43594]
  a := ![1, 20, 41]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-6073, 1914, 43594]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![25, 1, -1]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![25, 1, -1]] 
 ![![13, 0, 0], ![10, 1, 0], ![11, 0, 1]] where
  M :=![![![25, 1, -1], ![-48, 1, 3], ![64, 9, 0]]]
  hmulB := by decide  
  f := ![![![-27, -9, 4]], ![![-6, -2, 1]], ![![-61, -20, 9]]]
  g := ![![![2, 1, -1], ![-7, 1, 3], ![-2, 9, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![27, 9, -4]] ![![25, 1, -1]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0]] 
 ![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [7, 0, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 12, 15], [16, 4, 2], [0, 1]]
 g := ![![[15, 8, 16], [10, 1], [13, 1], []], ![[7, 1, 5, 9], [5, 15], [3, 16], [4, 4]], ![[11, 8, 15, 8], [8, 13], [5, 8], [0, 4]]]
 h' := ![![[14, 12, 15], [0, 9, 4], [11, 10, 16], [0, 0, 1], [0, 1]], ![[16, 4, 2], [16, 14, 15], [0, 16, 10], [15, 2, 4], [14, 12, 15]], ![[0, 1], [12, 11, 15], [0, 8, 8], [1, 15, 12], [16, 4, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 13], []]
 b := ![[], [10, 16, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [7, 0, 4, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![76330, 59024, 21981]
  a := ![-1, 2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4490, 3472, 1293]
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


def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![22695, 7433, -3247]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![22695, 7433, -3247]] 
 ![![19, 0, 0], ![4, 1, 0], ![6, 0, 1]] where
  M :=![![![22695, 7433, -3247], ![-155856, -51047, 22299], ![408736, 133873, -58480]]]
  hmulB := by decide  
  f := ![![![-5467, -3791, -1142]], ![![-4036, -2788, -839]], ![![-10342, -7147, -2151]]]
  g := ![![![655, 7433, -3247], ![-4498, -51047, 22299], ![11796, 133873, -58480]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N0 : Nat.card (O ⧸ I19N0) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N0)

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := prime_ideal_of_norm_prime hp19.out _ NI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2183, -714, 312]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![-2183, -714, 312]] 
 ![![19, 0, 0], ![10, 1, 0], ![14, 0, 1]] where
  M :=![![![-2183, -714, 312], ![14976, 4903, -2142], ![-39264, -12858, 5617]]]
  hmulB := by decide  
  f := ![![![-1685, -1158, -348]], ![![-1766, -1217, -366]], ![![-3874, -2670, -803]]]
  g := ![![![31, -714, 312], ![-214, 4903, -2142], ![562, -12858, 5617]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![22695, 7433, -3247]] ![![22695, 7433, -3247]]
  ![![-1970580415, -645426047, 281942362]] where
 M := ![![![-1970580415, -645426047, 281942362]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI19N1 : IdealMulLeCertificate' Table 
  ![![-1970580415, -645426047, 281942362]] ![![-2183, -714, 312]]
  ![![19, 0, 0]] where
 M := ![![![-16434308335495, -5382744382727, 2351351750548]]]
 hmul := by decide  
 g := ![![![![-864963596605, -283302335933, 123755355292]]]]
 hle2 := by decide  


def PBC19 : ContainsPrimesAboveP 19 ![I19N0, I19N0, I19N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N0
    exact isPrimeI19N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 19 (by decide) (𝕀 ⊙ MulI19N0 ⊙ MulI19N1)
instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5653, 4041, 1227]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![5653, 4041, 1227]] 
 ![![23, 0, 0], ![0, 23, 0], ![8, 2, 1]] where
  M :=![![![5653, 4041, 1227], ![58896, 40369, 12123], ![174336, 120657, 36328]]]
  hmulB := by decide  
  f := ![![![165227, 54117, -23640]], ![![-1134720, -371656, 162351]], ![![88184, 28883, -12617]]]
  g := ![![![-181, 69, 1227], ![-1656, 701, 12123], ![-5056, 2087, 36328]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [13, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 22], [0, 1]]
 g := ![![[19, 16], [7, 18], [14, 13], [1]], ![[0, 7], [0, 5], [0, 10], [1]]]
 h' := ![![[6, 22], [1, 19], [2, 15], [10, 6], [0, 1]], ![[0, 1], [0, 4], [0, 8], [0, 17], [6, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [14, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 2
  hpos := by decide
  P := [13, 17, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1293, 2284, 1763]
  a := ![0, 3, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-557, -54, 1763]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![165227, 54117, -23640]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![165227, 54117, -23640]] 
 ![![23, 0, 0], ![17, 1, 0], ![13, 0, 1]] where
  M :=![![![165227, 54117, -23640], ![-1134720, -371656, 162351], ![2975856, 974685, -425773]]]
  hmulB := by decide  
  f := ![![![5653, 4041, 1227]], ![![6739, 4742, 1434]], ![![10775, 7530, 2273]]]
  g := ![![![-19454, 54117, -23640], ![133603, -371656, 162351], ![-350380, 974685, -425773]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![5653, 4041, 1227]] ![![165227, 54117, -23640]]
  ![![23, 0, 0]] where
 M := ![![![23, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-49, -7, 4]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![-49, -7, 4]] 
 ![![29, 0, 0], ![0, 29, 0], ![24, 20, 1]] where
  M :=![![![-49, -7, 4], ![192, 44, -21], ![-400, -111, 51]]]
  hmulB := by decide  
  f := ![![![3, 3, 1]], ![![48, 31, 9]], ![![40, 27, 8]]]
  g := ![![![-5, -3, 4], ![24, 16, -21], ![-56, -39, 51]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [19, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [27, 28], [0, 1]]
 g := ![![[23, 5], [1], [5, 22], [27, 1]], ![[13, 24], [1], [19, 7], [25, 28]]]
 h' := ![![[27, 28], [16, 11], [21, 1], [9, 14], [0, 1]], ![[0, 1], [23, 18], [19, 28], [10, 15], [27, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [25, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [19, 2, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7643, 8752, 5008]
  a := ![2, -8, -14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3881, -3152, 5008]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, -3, -1]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![-3, -3, -1]] 
 ![![29, 0, 0], ![27, 1, 0], ![9, 0, 1]] where
  M :=![![![-3, -3, -1], ![-48, -31, -9], ![-128, -91, -28]]]
  hmulB := by decide  
  f := ![![![49, 7, -4]], ![![39, 5, -3]], ![![29, 6, -3]]]
  g := ![![![3, -3, -1], ![30, -31, -9], ![89, -91, -28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![-49, -7, 4]] ![![-3, -3, -1]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-295, -96, 42]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![-295, -96, 42]] 
 ![![31, 0, 0], ![9, 1, 0], ![1, 0, 1]] where
  M :=![![![-295, -96, 42], ![2016, 659, -288], ![-5280, -1728, 755]]]
  hmulB := by decide  
  f := ![![![119, 96, 30]], ![![81, 59, 18]], ![![137, 96, 29]]]
  g := ![![![17, -96, 42], ![-117, 659, -288], ![307, -1728, 755]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N0 : Nat.card (O ⧸ I31N0) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N0)

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := prime_ideal_of_norm_prime hp31.out _ NI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8911, 6144, 1848]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![8911, 6144, 1848]] 
 ![![31, 0, 0], ![12, 1, 0], ![10, 0, 1]] where
  M :=![![![8911, 6144, 1848], ![88704, 61255, 18432], ![265344, 183168, 55111]]]
  hmulB := by decide  
  f := ![![![-328271, -107520, 46968]], ![![-54348, -17801, 7776]], ![![-296618, -97152, 42439]]]
  g := ![![![-2687, 6144, 1848], ![-26796, 61255, 18432], ![-80122, 183168, 55111]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![-295, -96, 42]] ![![-295, -96, 42]]
  ![![-328271, -107520, 46968]] where
 M := ![![![-328271, -107520, 46968]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI31N1 : IdealMulLeCertificate' Table 
  ![![-328271, -107520, 46968]] ![![8911, 6144, 1848]]
  ![![31, 0, 0]] where
 M := ![![![31, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N0, I31N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N0
    exact isPrimeI31N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0 ⊙ MulI31N1)


lemma PB72I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB72I0 : PrimesBelowBoundCertificateInterval O 1 31 72 where
  m := 11
  g := ![2, 3, 2, 1, 2, 2, 1, 3, 2, 2, 3]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB72I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1]
    · exact ![I3N0, I3N0, I3N1]
    · exact ![I5N0, I5N1]
    · exact ![I7N0]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1]
    · exact ![I17N0]
    · exact ![I19N0, I19N0, I19N1]
    · exact ![I23N0, I23N1]
    · exact ![I29N0, I29N1]
    · exact ![I31N0, I31N0, I31N1]
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
    · exact ![2, 4]
    · exact ![3, 3, 3]
    · exact ![25, 5]
    · exact ![343]
    · exact ![121, 11]
    · exact ![169, 13]
    · exact ![4913]
    · exact ![19, 19, 19]
    · exact ![529, 23]
    · exact ![841, 29]
    · exact ![31, 31, 31]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
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
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N0
      exact NI19N1
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N0
      exact NI31N1
  β := ![I2N0, I2N1, I3N0, I3N1, I5N0, I5N1, I11N1, I13N1, I19N0, I19N1, I23N1, I29N1, I31N0, I31N1]
  Il := ![[I2N0, I2N1], [I3N0, I3N0, I3N1], [I5N0, I5N1], [], [I11N1], [I13N1], [], [I19N0, I19N0, I19N1], [I23N1], [I29N1], [I31N0, I31N0, I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
