
import IdealArithmetic.Examples.NF3_1_273239_1.RI3_1_273239_1
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


def P2P0 : CertificateIrreducibleZModOfList' 2 3 2 1 [1, 0, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 0, 1], [1, 1, 1], [0, 1]]
 g := ![![[]], ![[1, 1]], ![[1, 1]]]
 h' := ![![[0, 0, 1], [0, 1]], ![[1, 1, 1], [0, 0, 1]], ![[0, 1], [1, 1, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1], []]
 b := ![[], [0, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI2N0 : CertifiedPrimeIdeal' SI2N0 2 where
  n := 3
  hpos := by decide
  P := [1, 0, 1, 1]
  hirr := P2P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7221600, 256964, -168370]
  a := ![0, 9, -20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3610800, 128482, -84185]
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


def P3P0 : CertificateIrreducibleZModOfList' 3 3 2 1 [2, 1, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 2, 2], [1, 0, 1], [0, 1]]
 g := ![![[1]], ![[0, 0, 1, 2]], ![[2, 0, 2, 1]]]
 h' := ![![[1, 2, 2], [0, 1]], ![[1, 0, 1], [1, 2, 2]], ![[0, 1], [1, 0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 2], []]
 b := ![[], [0, 0, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : CertifiedPrimeIdeal' SI3N0 3 where
  n := 3
  hpos := by decide
  P := [2, 1, 1, 1]
  hirr := P3P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3065553, -105252, 54759]
  a := ![-1, -7, 15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1021851, -35084, 18253]
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


def P5P0 : CertificateIrreducibleZModOfList' 5 3 2 2 [4, 1, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 0, 2], [0, 4, 3], [0, 1]]
 g := ![![[3, 3, 1], []], ![[2, 4, 3, 2], [2, 4]], ![[0, 2], [1, 4]]]
 h' := ![![[3, 0, 2], [0, 0, 1], [0, 1]], ![[0, 4, 3], [1, 2, 4], [3, 0, 2]], ![[0, 1], [1, 3], [0, 4, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 3], []]
 b := ![[], [2, 0, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where
  n := 3
  hpos := by decide
  P := [4, 1, 2, 1]
  hirr := P5P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-261385, 4830, -23165]
  a := ![-64, 1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-52277, 966, -4633]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3049, 119, 309]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![3049, 119, 309]] 
 ![![7, 0, 0], ![0, 7, 0], ![4, 0, 1]] where
  M :=![![![3049, 119, 309], ![31209, 1218, 3163], ![43228, 1687, 4381]]]
  hmulB := by decide  
  f := ![![![11, -8, 5]], ![![505, 31, -58]], ![![-37, 5, -1]]]
  g := ![![![259, 17, 309], ![2651, 174, 3163], ![3672, 241, 4381]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 2 2 2 [4, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 6], [0, 1]]
 g := ![![[2, 2], [6, 1]], ![[0, 5], [5, 6]]]
 h' := ![![[6, 6], [4, 4], [0, 1]], ![[0, 1], [0, 3], [6, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [1, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 2
  hpos := by decide
  P := [4, 1, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4854, 5572, -757]
  a := ![1, 11, -24]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1126, 796, -757]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11, 8, -5]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![-11, 8, -5]] 
 ![![7, 0, 0], ![1, 1, 0], ![1, 0, 1]] where
  M :=![![![-11, 8, -5], ![-505, -31, 58], ![303, -67, 27]]]
  hmulB := by decide  
  f := ![![![-3049, -119, -309]], ![![-4894, -191, -496]], ![![-6611, -258, -670]]]
  g := ![![![-2, 8, -5], ![-76, -31, 58], ![49, -67, 27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![3049, 119, 309]] ![![-11, 8, -5]]
  ![![7, 0, 0]] where
 M := ![![![-7, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-37, 5, -1]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![-37, 5, -1]] 
 ![![11, 0, 0], ![0, 1, 0], ![4, 0, 1]] where
  M :=![![![-37, 5, -1], ![-101, -58, 49], ![404, -27, -9]]]
  hmulB := by decide  
  f := ![![![1845, 72, 187]], ![![1717, 67, 174]], ![![3049, 119, 309]]]
  g := ![![![-3, 5, -1], ![-27, -58, 49], ![40, -27, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N0 : Nat.card (O ⧸ I11N0) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N0)

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := prime_ideal_of_norm_prime hp11.out _ NI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-633739, -24733, -64227]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![-633739, -24733, -64227]] 
 ![![11, 0, 0], ![5, 1, 0], ![9, 0, 1]] where
  M :=![![![-633739, -24733, -64227], ![-6486927, -253166, -657425], ![-8984960, -350657, -910591]]]
  hmulB := by decide  
  f := ![![![-2881, 64, 157]], ![![132, -319, 221]], ![![-328, 129, -70]]]
  g := ![![![6179, -24733, -64227], ![63248, -253166, -657425], ![87604, -350657, -910591]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1

def I11N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-26, -3, 4]] i)))

def SI11N2: IdealEqSpanCertificate' Table ![![-26, -3, 4]] 
 ![![11, 0, 0], ![5, 1, 0], ![0, 0, 1]] where
  M :=![![![-26, -3, 4], ![404, -27, -9], ![101, 40, -36]]]
  hmulB := by decide  
  f := ![![![1332, 52, 135]], ![![1845, 72, 187]], ![![1717, 67, 174]]]
  g := ![![![-1, -3, 4], ![49, -27, -9], ![-9, 40, -36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N2 : Nat.card (O ⧸ I11N2) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N2)

lemma isPrimeI11N2 : Ideal.IsPrime I11N2 := prime_ideal_of_norm_prime hp11.out _ NI11N2
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![-37, 5, -1]] ![![-633739, -24733, -64227]]
  ![![-1332, -52, -135]] where
 M := ![![![-1332, -52, -135]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI11N1 : IdealMulLeCertificate' Table 
  ![![-1332, -52, -135]] ![![-26, -3, 4]]
  ![![11, 0, 0]] where
 M := ![![![-11, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-79, -3, -8]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![-79, -3, -8]] 
 ![![13, 0, 0], ![0, 13, 0], ![5, 2, 1]] where
  M :=![![![-79, -3, -8], ![-808, -32, -81], ![-1111, -44, -113]]]
  hmulB := by decide  
  f := ![![![-4, -1, 1]], ![![101, -3, -5]], ![![14, 0, -1]]]
  g := ![![![-3, 1, -8], ![-31, 10, -81], ![-42, 14, -113]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [5, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 12], [0, 1]]
 g := ![![[1, 1], [10], [8, 1]], ![[9, 12], [10], [3, 12]]]
 h' := ![![[8, 12], [3, 1], [12, 7], [0, 1]], ![[0, 1], [11, 12], [3, 6], [8, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [12, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 2
  hpos := by decide
  P := [5, 5, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4045, 3880, -569]
  a := ![0, 9, -20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![530, 386, -569]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4, 1, -1]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![4, 1, -1]] 
 ![![13, 0, 0], ![11, 1, 0], ![7, 0, 1]] where
  M :=![![![4, 1, -1], ![-101, 3, 5], ![0, -11, 8]]]
  hmulB := by decide  
  f := ![![![79, 3, 8]], ![![129, 5, 13]], ![![128, 5, 13]]]
  g := ![![![0, 1, -1], ![-13, 3, 5], ![5, -11, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![-79, -3, -8]] ![![4, 1, -1]]
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


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [3, 16, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 11, 12], [8, 5, 5], [0, 1]]
 g := ![![[14, 7, 15], [11, 1], [0, 1], []], ![[6, 3, 6, 10], [16, 9], [11, 8], [9, 8]], ![[3, 0, 8, 11], [3, 16], [3, 2], [16, 8]]]
 h' := ![![[9, 11, 12], [1, 8, 10], [0, 14, 1], [0, 0, 1], [0, 1]], ![[8, 5, 5], [1, 14, 10], [10, 14, 3], [3, 13, 5], [9, 11, 12]], ![[0, 1], [4, 12, 14], [9, 6, 13], [16, 4, 11], [8, 5, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 3], []]
 b := ![[], [16, 3, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [3, 16, 0, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5435593073, -192719089, 135210452]
  a := ![1, -81, 182]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![319740769, -11336417, 7953556]
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


def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-61137, -2386, -6196]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![-61137, -2386, -6196]] 
 ![![19, 0, 0], ![11, 1, 0], ![13, 0, 1]] where
  M :=![![![-61137, -2386, -6196], ![-625796, -24423, -63422], ![-866782, -33828, -87845]]]
  hmulB := by decide  
  f := ![![![981, -118, 16]], ![![653, 11, -54]], ![![129, -50, 27]]]
  g := ![![![2403, -2386, -6196], ![24597, -24423, -63422], ![34069, -33828, -87845]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N0 : Nat.card (O ⧸ I19N0) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N0)

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := prime_ideal_of_norm_prime hp19.out _ NI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-33681461, -1314490, -3413486]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![-33681461, -1314490, -3413486]] 
 ![![19, 0, 0], ![15, 1, 0], ![14, 0, 1]] where
  M :=![![![-33681461, -1314490, -3413486], ![-344762086, -13455067, -34940306], ![-477525576, -18636442, -48395373]]]
  hmulB := by decide  
  f := ![![![26261, -2042, -378]], ![![18723, 387, -1600]], ![![6486, -1214, 419]]]
  g := ![![![1780247, -1314490, -3413486], ![18222537, -13455067, -34940306], ![25239804, -18636442, -48395373]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![-61137, -2386, -6196]] ![![-61137, -2386, -6196]]
  ![![10601463297, 413744448, 1074417364]] where
 M := ![![![10601463297, 413744448, 1074417364]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI19N1 : IdealMulLeCertificate' Table 
  ![![10601463297, 413744448, 1074417364]] ![![-33681461, -1314490, -3413486]]
  ![![19, 0, 0]] where
 M := ![![![-1012777942152737109, -39525793645970434, -102641133251201202]]]
 hmul := by decide  
 g := ![![![![-53304102218565111, -2080304928735286, -5402164907957958]]]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6046259, 235968, 612765]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![6046259, 235968, 612765]] 
 ![![23, 0, 0], ![1, 1, 0], ![15, 0, 1]] where
  M :=![![![6046259, 235968, 612765], ![61889265, 2415359, 6272238], ![85722033, 3345483, 8687597]]]
  hmulB := by decide  
  f := ![![![1369, 1599, -1251]], ![![-5434, -1, 384]], ![![2421, 384, -448]]]
  g := ![![![-147008, 235968, 612765], ![-1504768, 2415359, 6272238], ![-2084235, 3345483, 8687597]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N0 : Nat.card (O ⧸ I23N0) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N0)

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := prime_ideal_of_norm_prime hp23.out _ NI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![196676246, 7675705, 19932378]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![196676246, 7675705, 19932378]] 
 ![![23, 0, 0], ![9, 1, 0], ![3, 0, 1]] where
  M :=![![![196676246, 7675705, 19932378], ![2013170178, 78568209, 204027023], ![2788416383, 108823826, 282595232]]]
  hmulB := by decide  
  f := ![![![-70510, -332, 5213]], ![![-4699, -4030, 3241]], ![![12237, 1601, -2019]]]
  g := ![![![2947729, 7675705, 19932378], ![30172836, 78568209, 204027023], ![41792011, 108823826, 282595232]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1

def I23N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![128, 5, 13]] i)))

def SI23N2: IdealEqSpanCertificate' Table ![![128, 5, 13]] 
 ![![23, 0, 0], ![12, 1, 0], ![7, 0, 1]] where
  M :=![![![128, 5, 13], ![1313, 51, 133], ![1818, 71, 184]]]
  hmulB := by decide  
  f := ![![![-59, 3, 2]], ![![-22, -2, 3]], ![![4, 1, -1]]]
  g := ![![![-1, 5, 13], ![-10, 51, 133], ![-14, 71, 184]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N2 : Nat.card (O ⧸ I23N2) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N2)

lemma isPrimeI23N2 : Ideal.IsPrime I23N2 := prime_ideal_of_norm_prime hp23.out _ NI23N2
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![6046259, 235968, 612765]] ![![196676246, 7675705, 19932378]]
  ![![3372843227955013, 131632315317797, 341824635773646]] where
 M := ![![![3372843227955013, 131632315317797, 341824635773646]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI23N1 : IdealMulLeCertificate' Table 
  ![![3372843227955013, 131632315317797, 341824635773646]] ![![128, 5, 13]]
  ![![23, 0, 0]] where
 M := ![![![1225994351026997553, 47847013360911578, 124249792883033034]]]
 hmul := by decide  
 g := ![![![![53304102218565111, 2080304928735286, 5402164907957958]]]]
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

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-59, 21, -11]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![-59, 21, -11]] 
 ![![29, 0, 0], ![3, 1, 0], ![19, 0, 1]] where
  M :=![![![-59, 21, -11], ![-1111, -120, 165], ![1010, -161, 45]]]
  hmulB := by decide  
  f := ![![![21165, 826, 2145]], ![![9660, 377, 979]], ![![24214, 945, 2454]]]
  g := ![![![3, 21, -11], ![-134, -120, 165], ![22, -161, 45]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N0 : Nat.card (O ⧸ I29N0) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N0)

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := prime_ideal_of_norm_prime hp29.out _ NI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![12237, 1601, -2019]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![12237, 1601, -2019]] 
 ![![29, 0, 0], ![4, 1, 0], ![3, 0, 1]] where
  M :=![![![12237, 1601, -2019], ![-203919, 12308, 5497], ![-42218, -20537, 17805]]]
  hmulB := by decide  
  f := ![![![332035829, 12958398, 33650549]], ![![162994785, 6361215, 16518892]], ![![196676246, 7675705, 19932378]]]
  g := ![![![410, 1601, -2019], ![-9298, 12308, 5497], ![-465, -20537, 17805]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1

def I29N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![328, -129, 70]] i)))

def SI29N2: IdealEqSpanCertificate' Table ![![328, -129, 70]] 
 ![![29, 0, 0], ![21, 1, 0], ![9, 0, 1]] where
  M :=![![![328, -129, 70], ![7070, 693, -999], ![-5959, 1006, -306]]]
  hmulB := by decide  
  f := ![![![792936, 30946, 80361]], ![![854073, 33332, 86557]], ![![633739, 24733, 64227]]]
  g := ![![![83, -129, 70], ![52, 693, -999], ![-839, 1006, -306]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N2 : Nat.card (O ⧸ I29N2) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N2)

lemma isPrimeI29N2 : Ideal.IsPrime I29N2 := prime_ideal_of_norm_prime hp29.out _ NI29N2
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![-59, 21, -11]] ![![12237, 1601, -2019]]
  ![![-4539884, 389916, 38703]] where
 M := ![![![-4539884, 389916, 38703]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI29N1 : IdealMulLeCertificate' Table 
  ![![-4539884, 389916, 38703]] ![![328, -129, 70]]
  ![![29, 0, 0]] where
 M := ![![![1036992991, 894792042, -719161082]]]
 hmul := by decide  
 g := ![![![![35758379, 30854898, -24798658]]]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8456, -330, -857]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![-8456, -330, -857]] 
 ![![31, 0, 0], ![0, 31, 0], ![26, 1, 1]] where
  M :=![![![-8456, -330, -857], ![-86557, -3378, -8772], ![-119887, -4679, -12150]]]
  hmulB := by decide  
  f := ![![![48, -13, 6]], ![![606, 89, -107]], ![![37, -5, 1]]]
  g := ![![![446, 17, -857], ![4565, 174, -8772], ![6323, 241, -12150]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [18, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [30, 30], [0, 1]]
 g := ![![[19, 19], [15, 19], [29, 10], [30, 1]], ![[0, 12], [27, 12], [19, 21], [29, 30]]]
 h' := ![![[30, 30], [9, 9], [5, 22], [18, 14], [0, 1]], ![[0, 1], [0, 22], [14, 9], [4, 17], [30, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [7, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [18, 1, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3250, 2450, -309]
  a := ![-1, -7, 16]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![364, 89, -309]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![48, -13, 6]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![48, -13, 6]] 
 ![![31, 0, 0], ![14, 1, 0], ![28, 0, 1]] where
  M :=![![![48, -13, 6], ![606, 89, -107], ![-707, 94, -18]]]
  hmulB := by decide  
  f := ![![![-8456, -330, -857]], ![![-6611, -258, -670]], ![![-11505, -449, -1166]]]
  g := ![![![2, -13, 6], ![76, 89, -107], ![-49, 94, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![-8456, -330, -857]] ![![48, -13, 6]]
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


lemma PB148I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB148I0 : PrimesBelowBoundCertificateInterval O 1 31 148 where
  m := 11
  g := ![1, 1, 1, 2, 3, 2, 1, 3, 3, 3, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB148I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0]
    · exact ![I3N0]
    · exact ![I5N0]
    · exact ![I7N0, I7N1]
    · exact ![I11N0, I11N1, I11N2]
    · exact ![I13N0, I13N1]
    · exact ![I17N0]
    · exact ![I19N0, I19N0, I19N1]
    · exact ![I23N0, I23N1, I23N2]
    · exact ![I29N0, I29N1, I29N2]
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
    · exact ![27]
    · exact ![125]
    · exact ![49, 7]
    · exact ![11, 11, 11]
    · exact ![169, 13]
    · exact ![4913]
    · exact ![19, 19, 19]
    · exact ![23, 23, 23]
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
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N1
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
      exact NI11N2
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
      exact NI23N2
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
      exact NI29N2
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
  β := ![I2N0, I3N0, I5N0, I7N0, I7N1, I11N0, I11N1, I11N2, I13N1, I19N0, I19N1, I23N0, I23N1, I23N2, I29N0, I29N1, I29N2, I31N1]
  Il := ![[I2N0], [I3N0], [I5N0], [I7N0, I7N1], [I11N0, I11N1, I11N2], [I13N1], [], [I19N0, I19N0, I19N1], [I23N0, I23N1, I23N2], [I29N0, I29N1, I29N2], [I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
