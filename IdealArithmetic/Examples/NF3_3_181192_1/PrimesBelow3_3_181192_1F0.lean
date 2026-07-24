
import IdealArithmetic.Examples.NF3_3_181192_1.RI3_3_181192_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 13, -5]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![29, 13, -5]] 
 ![![2, 0, 0], ![0, 1, 0], ![1, 0, 1]] where
  M :=![![![29, 13, -5], ![-244, -109, 42], ![437, 195, -75]]]
  hmulB := by decide  
  f := ![![![-15, 0, 1]], ![![27, 5, 1]], ![![19, 13, 6]]]
  g := ![![![17, 13, -5], ![-143, -109, 42], ![256, 195, -75]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1414, -631, 243]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![-1414, -631, 243]] 
 ![![2, 0, 0], ![1, 1, 0], ![1, 0, 1]] where
  M :=![![![-1414, -631, 243], ![11860, 5292, -2038], ![-21195, -9457, 3642]]]
  hmulB := by decide  
  f := ![![![-98, -51, -22]], ![![-694, -324, -135]], ![![-2009, -949, -397]]]
  g := ![![![-513, -631, 243], ![4303, 5292, -2038], ![-7690, -9457, 3642]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![29, 13, -5]] ![![29, 13, -5]]
  ![![-4516, -2015, 776]] where
 M := ![![![-4516, -2015, 776]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI2N1 : IdealMulLeCertificate' Table 
  ![![-4516, -2015, 776]] ![![-1414, -631, 243]]
  ![![2, 0, 0]] where
 M := ![![![-33959596, -15152416, 5835374]]]
 hmul := by decide  
 g := ![![![![-16979798, -7576208, 2917687]]]]
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


def P3P0 : CertificateIrreducibleZModOfList' 3 3 2 1 [1, 1, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 2, 1], [2, 0, 2], [0, 1]]
 g := ![![[1]], ![[0, 0, 1, 1]], ![[2, 0, 2, 2]]]
 h' := ![![[2, 2, 1], [0, 1]], ![[2, 0, 2], [2, 2, 1]], ![[0, 1], [2, 0, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 2], []]
 b := ![[], [0, 0, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : CertifiedPrimeIdeal' SI3N0 3 where
  n := 3
  hpos := by decide
  P := [1, 1, 2, 1]
  hirr := P3P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-455139, -219048, -160224]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-151713, -73016, -53408]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![435, 12, -16]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![435, 12, -16]] 
 ![![5, 0, 0], ![0, 5, 0], ![0, 3, 1]] where
  M :=![![![435, 12, -16], ![-840, 23, 16], ![-200, -116, 43]]]
  hmulB := by decide  
  f := ![![![-569, -268, -112]], ![![-6584, -3101, -1296]], ![![-8032, -3783, -1581]]]
  g := ![![![87, 12, -16], ![-168, -5, 16], ![-40, -49, 43]]]
  hle1 := by decide   
  hle2 := by decide  


def P5P0 : CertificateIrreducibleZModOfList' 5 2 2 2 [3, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 4], [0, 1]]
 g := ![![[4, 4], [1]], ![[1, 1], [1]]]
 h' := ![![[3, 4], [2, 3], [0, 1]], ![[0, 1], [1, 2], [3, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [4, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where
  n := 2
  hpos := by decide
  P := [3, 2, 1]
  hirr := P5P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![365, 191, 1282]
  a := ![3, -3, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![73, -731, 1282]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI5N0 B_one_repr
lemma NI5N0 : Nat.card (O ⧸ I5N0) = 25 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![569, 268, 112]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![569, 268, 112]] 
 ![![5, 0, 0], ![1, 1, 0], ![3, 0, 1]] where
  M :=![![![569, 268, 112], ![6584, 3101, 1296], ![20408, 9612, 4017]]]
  hmulB := by decide  
  f := ![![![-435, -12, 16]], ![![81, -7, 0]], ![![-221, 16, 1]]]
  g := ![![![-7, 268, 112], ![-81, 3101, 1296], ![-251, 9612, 4017]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![435, 12, -16]] ![![569, 268, 112]]
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


def P7P0 : CertificateIrreducibleZModOfList' 7 3 2 2 [1, 3, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 4], [6, 2], [0, 1]]
 g := ![![[3, 2, 2], [1]], ![[1, 2, 4], [1]], ![[3, 3, 1], [1]]]
 h' := ![![[4, 4], [6, 4, 3], [0, 1]], ![[6, 2], [0, 0, 6], [4, 4]], ![[0, 1], [5, 3, 5], [6, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4], []]
 b := ![[], [1, 5, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 3
  hpos := by decide
  P := [1, 3, 4, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-823810575, -393377446, -244901020]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-117687225, -56196778, -34985860]
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


def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-51, -24, -10]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![-51, -24, -10]] 
 ![![11, 0, 0], ![1, 1, 0], ![6, 0, 1]] where
  M :=![![![-51, -24, -10], ![-588, -277, -116], ![-1826, -860, -359]]]
  hmulB := by decide  
  f := ![![![-317, -16, 14]], ![![37, 3, -2]], ![![-184, -12, 9]]]
  g := ![![![3, -24, -10], ![35, -277, -116], ![108, -860, -359]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N0 : Nat.card (O ⧸ I11N0) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N0)

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := prime_ideal_of_norm_prime hp11.out _ NI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![274, 122, -47]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![274, 122, -47]] 
 ![![11, 0, 0], ![8, 1, 0], ![3, 0, 1]] where
  M :=![![![274, 122, -47], ![-2294, -1023, 394], ![4097, 1828, -704]]]
  hmulB := by decide  
  f := ![![![-40, -28, -13]], ![![-98, -51, -22]], ![![-211, -102, -43]]]
  g := ![![![-51, 122, -47], ![428, -1023, 394], ![-765, 1828, -704]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![-51, -24, -10]] ![![-51, -24, -10]]
  ![![34973, 16472, 6884]] where
 M := ![![![34973, 16472, 6884]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI11N1 : IdealMulLeCertificate' Table 
  ![![34973, 16472, 6884]] ![![274, 122, -47]]
  ![![11, 0, 0]] where
 M := ![![![-418, -198, -99]]]
 hmul := by decide  
 g := ![![![![-38, -18, -9]]]]
 hle2 := by decide  


def PBC11 : ContainsPrimesAboveP 11 ![I11N0, I11N0, I11N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
    exact isPrimeI11N0
    exact isPrimeI11N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 11 (by decide) (𝕀 ⊙ MulI11N0 ⊙ MulI11N1)
instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1084, 52, -47]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![1084, 52, -47]] 
 ![![13, 0, 0], ![0, 13, 0], ![1, 0, 1]] where
  M :=![![![1084, 52, -47], ![-2434, -143, 114], ![317, 78, -34]]]
  hmulB := by decide  
  f := ![![![310, 146, 61]], ![![3586, 1689, 706]], ![![879, 414, 173]]]
  g := ![![![87, 4, -47], ![-196, -11, 114], ![27, 6, -34]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [2, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [7, 12], [0, 1]]
 g := ![![[3, 9], [12], [7, 1]], ![[1, 4], [12], [1, 12]]]
 h' := ![![[7, 12], [3, 3], [12, 8], [0, 1]], ![[0, 1], [11, 10], [3, 5], [7, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [10, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 2
  hpos := by decide
  P := [2, 6, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1389, 741, 2052]
  a := ![-4, 3, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-51, 57, 2052]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![310, 146, 61]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![310, 146, 61]] 
 ![![13, 0, 0], ![11, 1, 0], ![12, 0, 1]] where
  M :=![![![310, 146, 61], ![3586, 1689, 706], ![11117, 5236, 2188]]]
  hmulB := by decide  
  f := ![![![1084, 52, -47]], ![![730, 33, -31]], ![![1025, 54, -46]]]
  g := ![![![-156, 146, 61], ![-1805, 1689, 706], ![-5595, 5236, 2188]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![1084, 52, -47]] ![![310, 146, 61]]
  ![![13, 0, 0]] where
 M := ![![![13, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 6, -2]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![13, 6, -2]] 
 ![![17, 0, 0], ![0, 17, 0], ![2, 14, 1]] where
  M :=![![![13, 6, -2], ![-96, -43, 20], ![218, 98, -27]]]
  hmulB := by decide  
  f := ![![![-47, -2, 2]], ![![104, 5, -4]], ![![80, 4, -3]]]
  g := ![![![1, 2, -2], ![-8, -19, 20], ![16, 28, -27]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 2 2 4 [14, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 16], [0, 1]]
 g := ![![[13, 1], [4], [8], [1]], ![[1, 16], [4], [8], [1]]]
 h' := ![![[5, 16], [13, 16], [16, 2], [3, 5], [0, 1]], ![[0, 1], [8, 1], [9, 15], [11, 12], [5, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [13, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 2
  hpos := by decide
  P := [14, 12, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![94117, 45867, 50314]
  a := ![22, -1, 43]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-383, -38737, 50314]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 2, -2]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![47, 2, -2]] 
 ![![17, 0, 0], ![10, 1, 0], ![12, 0, 1]] where
  M :=![![![47, 2, -2], ![-104, -5, 4], ![2, -2, -1]]]
  hmulB := by decide  
  f := ![![![-13, -6, 2]], ![![-2, -1, 0]], ![![-22, -10, 3]]]
  g := ![![![3, 2, -2], ![-6, -5, 4], ![2, -2, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![13, 6, -2]] ![![47, 2, -2]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-422, -196, 75]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![-422, -196, 75]] 
 ![![19, 0, 0], ![0, 19, 0], ![4, 6, 1]] where
  M :=![![![-422, -196, 75], ![3658, 1649, -634], ![-6609, -2950, 1136]]]
  hmulB := by decide  
  f := ![![![-156, -74, -31]], ![![-1822, -857, -358]], ![![-905, -426, -178]]]
  g := ![![![-38, -34, 75], ![326, 287, -634], ![-587, -514, 1136]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [18, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 18], [0, 1]]
 g := ![![[3, 11], [13, 6], [9], [1]], ![[17, 8], [12, 13], [9], [1]]]
 h' := ![![[3, 18], [13, 12], [10, 14], [1, 3], [0, 1]], ![[0, 1], [11, 7], [14, 5], [10, 16], [3, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [9, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [18, 16, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![181, 91, 50]
  a := ![0, 1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1, -11, 50]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![156, 74, 31]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![156, 74, 31]] 
 ![![19, 0, 0], ![12, 1, 0], ![15, 0, 1]] where
  M :=![![![156, 74, 31], ![1822, 857, 358], ![5639, 2656, 1110]]]
  hmulB := by decide  
  f := ![![![422, 196, -75]], ![![74, 37, -14]], ![![681, 310, -119]]]
  g := ![![![-63, 74, 31], ![-728, 857, 358], ![-2257, 2656, 1110]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![-422, -196, 75]] ![![156, 74, 31]]
  ![![19, 0, 0]] where
 M := ![![![-19, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-312, -14, 13]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![-312, -14, 13]] 
 ![![23, 0, 0], ![0, 23, 0], ![22, 6, 1]] where
  M :=![![![-312, -14, 13], ![674, 27, -30], ![-67, -12, -2]]]
  hmulB := by decide  
  f := ![![![-18, -8, 3]], ![![146, 65, -26]], ![![9, 4, -2]]]
  g := ![![![-26, -4, 13], ![58, 9, -30], ![-1, 0, -2]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [20, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 22], [0, 1]]
 g := ![![[13, 3], [3, 1], [6, 3], [1]], ![[15, 20], [19, 22], [8, 20], [1]]]
 h' := ![![[16, 22], [9, 7], [18, 22], [3, 16], [0, 1]], ![[0, 1], [6, 16], [2, 1], [6, 7], [16, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [21, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 2
  hpos := by decide
  P := [20, 7, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3228, 1562, 2706]
  a := ![5, -2, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2448, -638, 2706]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-18, -8, 3]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![-18, -8, 3]] 
 ![![23, 0, 0], ![20, 1, 0], ![9, 0, 1]] where
  M :=![![![-18, -8, 3], ![146, 65, -26], ![-273, -122, 44]]]
  hmulB := by decide  
  f := ![![![-312, -14, 13]], ![![-242, -11, 10]], ![![-125, -6, 5]]]
  g := ![![![5, -8, 3], ![-40, 65, -26], ![77, -122, 44]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![-312, -14, 13]] ![![-18, -8, 3]]
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

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-450, -20, 19]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![-450, -20, 19]] 
 ![![29, 0, 0], ![16, 1, 0], ![13, 0, 1]] where
  M :=![![![-450, -20, 19], ![986, 45, -42], ![-73, -6, 4]]]
  hmulB := by decide  
  f := ![![![72, 34, 15]], ![![70, 33, 14]], ![![123, 58, 25]]]
  g := ![![![-13, -20, 19], ![28, 45, -42], ![-1, -6, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N0 : Nat.card (O ⧸ I29N0) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N0)

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := prime_ideal_of_norm_prime hp29.out _ NI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2, -2, -1]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![-2, -2, -1]] 
 ![![29, 0, 0], ![25, 1, 0], ![10, 0, 1]] where
  M :=![![![-2, -2, -1], ![-58, -25, -10], ![-161, -76, -32]]]
  hmulB := by decide  
  f := ![![![40, 12, -5]], ![![26, 7, -3]], ![![27, 10, -4]]]
  g := ![![![2, -2, -1], ![23, -25, -10], ![71, -76, -32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![-450, -20, 19]] ![![-450, -20, 19]]
  ![![181393, 7986, -7634]] where
 M := ![![![181393, 7986, -7634]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI29N1 : IdealMulLeCertificate' Table 
  ![![181393, 7986, -7634]] ![![-2, -2, -1]]
  ![![29, 0, 0]] where
 M := ![![![403100, 17748, -16965]]]
 hmul := by decide  
 g := ![![![![13900, 612, -585]]]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2337, 46, -80]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![2337, 46, -80]] 
 ![![31, 0, 0], ![4, 1, 0], ![13, 0, 1]] where
  M :=![![![2337, 46, -80], ![-4228, 291, 24], ![-1756, -930, 349]]]
  hmulB := by decide  
  f := ![![![123879, 58346, 24384]], ![![62224, 29307, 12248]], ![![195273, 91972, 38437]]]
  g := ![![![103, 46, -80], ![-184, 291, 24], ![-83, -930, 349]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N0 : Nat.card (O ⧸ I31N0) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N0)

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := prime_ideal_of_norm_prime hp31.out _ NI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4, 2, 1]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![4, 2, 1]] 
 ![![31, 0, 0], ![7, 1, 0], ![21, 0, 1]] where
  M :=![![![4, 2, 1], ![58, 27, 10], ![161, 76, 34]]]
  hmulB := by decide  
  f := ![![![-158, -8, 7]], ![![-24, -1, 1]], ![![-109, -6, 5]]]
  g := ![![![-1, 2, 1], ![-11, 27, 10], ![-35, 76, 34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1

def I31N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1966, 926, 387]] i)))

def SI31N2: IdealEqSpanCertificate' Table ![![1966, 926, 387]] 
 ![![31, 0, 0], ![19, 1, 0], ![8, 0, 1]] where
  M :=![![![1966, 926, 387], ![22750, 10715, 4478], ![70515, 33212, 13880]]]
  hmulB := by decide  
  f := ![![![-864, -164, 77]], ![![-406, -61, 31]], ![![-377, -110, 46]]]
  g := ![![![-604, 926, 387], ![-6989, 10715, 4478], ![-21663, 33212, 13880]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N2 : Nat.card (O ⧸ I31N2) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N2)

lemma isPrimeI31N2 : Ideal.IsPrime I31N2 := prime_ideal_of_norm_prime hp31.out _ NI31N2
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![2337, 46, -80]] ![![4, 2, 1]]
  ![![-864, -164, 77]] where
 M := ![![![-864, -164, 77]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI31N1 : IdealMulLeCertificate' Table 
  ![![-864, -164, 77]] ![![1966, 926, 387]]
  ![![31, 0, 0]] where
 M := ![![![31, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


lemma PB95I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB95I0 : PrimesBelowBoundCertificateInterval O 1 31 95 where
  m := 11
  g := ![3, 1, 2, 1, 3, 2, 2, 2, 2, 3, 3]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB95I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N0, I2N1]
    · exact ![I3N0]
    · exact ![I5N0, I5N1]
    · exact ![I7N0]
    · exact ![I11N0, I11N0, I11N1]
    · exact ![I13N0, I13N1]
    · exact ![I17N0, I17N1]
    · exact ![I19N0, I19N1]
    · exact ![I23N0, I23N1]
    · exact ![I29N0, I29N0, I29N1]
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
    · exact ![2, 2, 2]
    · exact ![27]
    · exact ![25, 5]
    · exact ![343]
    · exact ![11, 11, 11]
    · exact ![169, 13]
    · exact ![289, 17]
    · exact ![361, 19]
    · exact ![529, 23]
    · exact ![29, 29, 29]
    · exact ![31, 31, 31]
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
      exact NI31N2
  β := ![I2N0, I2N1, I3N0, I5N0, I5N1, I11N0, I11N1, I13N1, I17N1, I19N1, I23N1, I29N0, I29N1, I31N0, I31N1, I31N2]
  Il := ![[I2N0, I2N0, I2N1], [I3N0], [I5N0, I5N1], [], [I11N0, I11N0, I11N1], [I13N1], [I17N1], [I19N1], [I23N1], [I29N0, I29N0, I29N1], [I31N0, I31N1, I31N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
