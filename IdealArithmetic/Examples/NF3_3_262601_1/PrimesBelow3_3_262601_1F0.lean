
import IdealArithmetic.Examples.NF3_3_262601_1.RI3_3_262601_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-22, -11, -2]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![-22, -11, -2]] 
 ![![2, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![-22, -11, -2], ![-256, -121, -20], ![-1152, -568, -101]]]
  hmulB := by decide  
  f := ![![![861, 25, -22]], ![![-1408, -41, 36]], ![![3008, 88, -77]]]
  g := ![![![-11, -11, -2], ![-128, -121, -20], ![-576, -568, -101]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-29, -1, 1]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![2, 0, 0], ![-29, -1, 1]] 
 ![![2, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![-29, -1, 1], ![128, 14, -3], ![-256, -2, 17]]]
  hmulB := by decide  
  f := ![![![13, 10, 1], ![-8, -2, 0]], ![![21, 6, 0], ![-3, -1, 0]], ![![23, -4, -1], ![6, 1, 0]]]
  g := ![![![1, 0, 0], ![-1, 2, 0], ![0, 0, 2]], ![![-14, -1, 1], ![57, 14, -3], ![-127, -2, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-29, -2, 1]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![2, 0, 0], ![-29, -2, 1]] 
 ![![2, 0, 0], ![1, 1, 0], ![1, 0, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![-29, -2, 1], ![128, 13, -5], ![-384, -46, 18]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![21, 4, -1], ![-3, -1, 0]], ![![15, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![-1, 2, 0], ![-1, 0, 2]], ![![-14, -2, 1], ![60, 13, -5], ![-178, -46, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![-22, -11, -2]] ![![2, 0, 0], ![-29, -1, 1]]
  ![![2, 0, 0], ![-30, -2, 1]] where
 M := ![![![-44, -22, -4], ![-258, -128, -23]]]
 hmul := by decide  
 g := ![![![![8, -9, -3], ![2, 0, 0]], ![![6, -55, -16], ![9, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![2, 0, 0], ![-30, -2, 1]] ![![2, 0, 0], ![-29, -2, 1]]
  ![![2, 0, 0]] where
 M := ![![![4, 0, 0], ![-58, -4, 2]], ![![-60, -4, 2], ![230, -12, -2]]]
 hmul := by decide  
 g := ![![![![2, 0, 0]], ![![-29, -2, 1]]], ![![![-30, -2, 1]], ![![115, -6, -1]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N1, I2N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
    exact isPrimeI2N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1)
instance hp3 : Fact (Nat.Prime 3) := {out := by norm_num}

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-29, -3, 1]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0], ![-29, -3, 1]] 
 ![![3, 0, 0], ![0, 3, 0], ![1, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![-29, -3, 1], ![128, 12, -7], ![-512, -90, 19]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![10, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-1, 0, 3]], ![![-10, -1, 1], ![45, 4, -7], ![-177, -30, 19]]]
  hle1 := by decide   
  hle2 := by decide  


def P3P0 : CertificateIrreducibleZModOfList' 3 2 2 1 [2, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 2], [0, 1]]
 g := ![![[1, 1]], ![[2, 2]]]
 h' := ![![[1, 2], [0, 1]], ![[0, 1], [1, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [2, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : CertifiedPrimeIdeal' SI3N0 3 where
  n := 2
  hpos := by decide
  P := [2, 2, 1]
  hirr := P3P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![386, 906, 395]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3, 302, 395]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N0 B_one_repr
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 9 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![1, 1, 0]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![3, 0, 0], ![1, 1, 0]] 
 ![![3, 0, 0], ![1, 1, 0], ![2, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![1, 1, 0], ![0, 2, 2], ![128, 44, 0]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![3, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, -2, -1], ![2, 2, 0]]]
  g := ![![![1, 0, 0], ![-1, 3, 0], ![-2, 0, 3]], ![![0, 1, 0], ![-2, 2, 2], ![28, 44, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![-29, -3, 1]] ![![3, 0, 0], ![1, 1, 0]]
  ![![3, 0, 0]] where
 M := ![![![9, 0, 0], ![3, 3, 0]], ![![-87, -9, 3], ![99, 9, -6]]]
 hmul := by decide  
 g := ![![![![3, 0, 0]], ![![1, 1, 0]]], ![![![-29, -3, 1]], ![![33, 3, -2]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0)
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


def P5P0 : CertificateIrreducibleZModOfList' 5 3 2 2 [3, 2, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 2, 2], [4, 2, 3], [0, 1]]
 g := ![![[2, 3, 1], []], ![[0, 4, 4, 3], [0, 4]], ![[3, 4, 1, 2], [4, 4]]]
 h' := ![![[4, 2, 2], [0, 0, 1], [0, 1]], ![[4, 2, 3], [1, 4, 2], [4, 2, 2]], ![[0, 1], [4, 1, 2], [4, 2, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 4], []]
 b := ![[], [0, 1, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where
  n := 3
  hpos := by decide
  P := [3, 2, 2, 1]
  hirr := P5P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![251650, 330745, 120950]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![50330, 66149, 24190]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-83, -28, -4]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![-83, -28, -4]] 
 ![![7, 0, 0], ![0, 7, 0], ![5, 0, 1]] where
  M :=![![![-83, -28, -4], ![-512, -287, -52], ![-3072, -1400, -235]]]
  hmulB := by decide  
  f := ![![![-765, -140, 44]], ![![5632, 1031, -324]], ![![-3911, -716, 225]]]
  g := ![![![-9, -4, -4], ![-36, -41, -52], ![-271, -200, -235]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 2 2 2 [6, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 6], [0, 1]]
 g := ![![[1, 4], [1, 1]], ![[5, 3], [2, 6]]]
 h' := ![![[1, 6], [1, 2], [0, 1]], ![[0, 1], [3, 5], [1, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [3, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 2
  hpos := by decide
  P := [6, 6, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-627, 1918, 1073]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-856, 274, 1073]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-229, -6, 6]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![-229, -6, 6]] 
 ![![7, 0, 0], ![1, 1, 0], ![6, 0, 1]] where
  M :=![![![-229, -6, 6], ![768, 29, -18], ![-1536, -12, 47]]]
  hmulB := by decide  
  f := ![![![-1147, -210, 66]], ![![1043, 191, -60]], ![![-6030, -1104, 347]]]
  g := ![![![-37, -6, 6], ![121, 29, -18], ![-258, -12, 47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![-83, -28, -4]] ![![-229, -6, 6]]
  ![![7, 0, 0]] where
 M := ![![![3647, -266, -182]]]
 hmul := by decide  
 g := ![![![![521, -38, -26]]]]
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


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [4, 9, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 5, 9], [10, 5, 2], [0, 1]]
 g := ![![[6, 10, 1], [0, 8, 1], []], ![[1, 4, 7, 4], [6, 2, 9, 5], [1, 4]], ![[8, 2, 9, 10], [7, 6, 6, 6], [8, 4]]]
 h' := ![![[9, 5, 9], [0, 1, 1], [0, 0, 1], [0, 1]], ![[10, 5, 2], [9, 4, 3], [0, 10, 5], [9, 5, 9]], ![[0, 1], [1, 6, 7], [2, 1, 5], [10, 5, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 5], []]
 b := ![[], [10, 0, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [4, 9, 3, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-296956, -205810, -54219]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-26996, -18710, -4929]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0]] 
 ![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [11, 2, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 7, 5], [2, 5, 8], [0, 1]]
 g := ![![[12, 1, 3], [], [1]], ![[5, 6, 6, 11], [7, 9], [7, 10, 5, 8]], ![[3, 8, 7, 7], [8, 9], [8, 12, 11, 5]]]
 h' := ![![[11, 7, 5], [4, 5, 4], [2, 11], [0, 1]], ![[2, 5, 8], [11, 5, 6], [6, 12, 3], [11, 7, 5]], ![[0, 1], [7, 3, 3], [11, 3, 10], [2, 5, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 10], []]
 b := ![[], [0, 9, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [11, 2, 0, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![147829006, 88838204, 20513415]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![11371462, 6833708, 1577955]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0]] 
 ![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [9, 9, 16, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 3, 15], [13, 13, 2], [0, 1]]
 g := ![![[7, 0, 2], [12, 13], [1, 1], []], ![[15, 1, 2, 15], [], [15, 16], [9, 4]], ![[2, 1, 14, 16], [8, 13], [4, 9], [5, 4]]]
 h' := ![![[5, 3, 15], [7, 14, 6], [8, 16, 9], [0, 0, 1], [0, 1]], ![[13, 13, 2], [13, 13, 16], [9, 13], [12, 15, 13], [5, 3, 15]], ![[0, 1], [15, 7, 12], [6, 5, 8], [5, 2, 3], [13, 13, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 11], []]
 b := ![[], [8, 12, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [9, 9, 16, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![39695, 20196, 3774]
  a := ![-1, 2, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2335, 1188, 222]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![-22, -5, 1]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0], ![-22, -5, 1]] 
 ![![19, 0, 0], ![0, 19, 0], ![16, 14, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![-22, -5, 1], ![128, 17, -11], ![-768, -178, 28]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-16, -14, 19]], ![![-2, -1, 1], ![16, 9, -11], ![-64, -30, 28]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [8, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 18], [0, 1]]
 g := ![![[10, 7], [], [16], [1]], ![[1, 12], [], [16], [1]]]
 h' := ![![[15, 18], [0, 11], [12], [11, 15], [0, 1]], ![[0, 1], [13, 8], [12], [8, 4], [15, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [5, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [8, 4, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![648, 2391, 1133]
  a := ![0, 3, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-920, -709, 1133]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![-8, 1, 0]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![19, 0, 0], ![-8, 1, 0]] 
 ![![19, 0, 0], ![11, 1, 0], ![10, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![-8, 1, 0], ![0, -7, 2], ![128, 44, -9]]]
  hmulB := by decide  
  f := ![![![129, -16, 0], ![304, 0, 0]], ![![73, -9, 0], ![172, 0, 0]], ![![62, -4, -1], ![146, 10, 0]]]
  g := ![![![1, 0, 0], ![-11, 19, 0], ![-10, 0, 19]], ![![-1, 1, 0], ![3, -7, 2], ![-14, 44, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![19, 0, 0], ![-22, -5, 1]] ![![19, 0, 0], ![-8, 1, 0]]
  ![![19, 0, 0]] where
 M := ![![![361, 0, 0], ![-152, 19, 0]], ![![-418, -95, 19], ![304, 57, -19]]]
 hmul := by decide  
 g := ![![![![19, 0, 0]], ![![-8, 1, 0]]], ![![![-22, -5, 1]], ![![16, 3, -1]]]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![-27, -4, 1]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0], ![-27, -4, 1]] 
 ![![23, 0, 0], ![0, 23, 0], ![19, 19, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![-27, -4, 1], ![128, 13, -9], ![-640, -134, 22]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-19, -19, 23]], ![![-2, -1, 1], ![13, 8, -9], ![-46, -24, 22]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [8, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 22], [0, 1]]
 g := ![![[7, 3], [20, 2], [11, 8], [1]], ![[0, 20], [0, 21], [0, 15], [1]]]
 h' := ![![[13, 22], [1, 7], [4, 5], [15, 13], [0, 1]], ![[0, 1], [0, 16], [0, 18], [0, 10], [13, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [10, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 2
  hpos := by decide
  P := [8, 10, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7712, 5688, 1568]
  a := ![2, -8, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-960, -1048, 1568]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![9, 1, 0]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![23, 0, 0], ![9, 1, 0]] 
 ![![23, 0, 0], ![9, 1, 0], ![1, 0, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![9, 1, 0], ![0, 10, 2], ![128, 44, 8]]]
  hmulB := by decide  
  f := ![![![109, 12, 0], ![-276, 0, 0]], ![![45, 5, 0], ![-114, 0, 0]], ![![-7, -6, -1], ![18, 12, 0]]]
  g := ![![![1, 0, 0], ![-9, 23, 0], ![-1, 0, 23]], ![![0, 1, 0], ![-4, 10, 2], ![-12, 44, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![23, 0, 0], ![-27, -4, 1]] ![![23, 0, 0], ![9, 1, 0]]
  ![![23, 0, 0]] where
 M := ![![![529, 0, 0], ![207, 23, 0]], ![![-621, -92, 23], ![-115, -23, 0]]]
 hmul := by decide  
 g := ![![![![23, 0, 0]], ![![9, 1, 0]]], ![![![-27, -4, 1]], ![![-5, -1, 0]]]]
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

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0]] 
 ![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 3 2 4 [6, 12, 17, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [16, 23, 9], [25, 5, 20], [0, 1]]
 g := ![![[7, 21, 25], [2, 5], [8, 19, 28], [1]], ![[27, 5, 26, 23], [26, 9], [2, 16, 2, 1], [6, 14, 11, 4]], ![[22, 10, 15, 4], [20, 6], [27, 27, 2, 23], [17, 22, 7, 25]]]
 h' := ![![[16, 23, 9], [1, 4, 5], [10, 0, 18], [23, 17, 12], [0, 1]], ![[25, 5, 20], [17, 20, 3], [17, 25, 3], [0, 21, 10], [16, 23, 9]], ![[0, 1], [24, 5, 21], [17, 4, 8], [8, 20, 7], [25, 5, 20]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 18], []]
 b := ![[], [5, 18, 27], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 3
  hpos := by decide
  P := [6, 12, 17, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2320, 6090, 5336]
  a := ![13, 0, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-80, 210, 184]
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


def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1175, 34, -30]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![1175, 34, -30]] 
 ![![31, 0, 0], ![6, 1, 0], ![10, 0, 1]] where
  M :=![![![1175, 34, -30], ![-3840, -111, 98], ![8192, 236, -209]]]
  hmulB := by decide  
  f := ![![![-71, -26, -2]], ![![-22, -11, -2]], ![![-122, -48, -5]]]
  g := ![![![41, 34, -30], ![-134, -111, 98], ![286, 236, -209]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N0 : Nat.card (O ⧸ I31N0) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N0)

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := prime_ideal_of_norm_prime hp31.out _ NI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5247, 152, -134]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![5247, 152, -134]] 
 ![![31, 0, 0], ![28, 1, 0], ![28, 0, 1]] where
  M :=![![![5247, 152, -134], ![-17152, -497, 438], ![36608, 1060, -935]]]
  hmulB := by decide  
  f := ![![![-415, -80, 22]], ![![-284, -57, 14]], ![![-796, -156, 41]]]
  g := ![![![153, 152, -134], ![-500, -497, 438], ![1068, 1060, -935]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![1175, 34, -30]] ![![5247, 152, -134]]
  ![![4483817, 129902, -114508]] where
 M := ![![![4483817, 129902, -114508]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI31N1 : IdealMulLeCertificate' Table 
  ![![4483817, 129902, -114508]] ![![5247, 152, -134]]
  ![![31, 0, 0]] where
 M := ![![![17106599831, 495600410, -436869422]]]
 hmul := by decide  
 g := ![![![![551825801, 15987110, -14092562]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N1, I31N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N1
    exact isPrimeI31N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0 ⊙ MulI31N1)


lemma PB114I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB114I0 : PrimesBelowBoundCertificateInterval O 1 31 114 where
  m := 11
  g := ![3, 2, 1, 2, 1, 1, 1, 2, 2, 1, 3]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB114I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N2]
    · exact ![I3N0, I3N1]
    · exact ![I5N0]
    · exact ![I7N0, I7N1]
    · exact ![I11N0]
    · exact ![I13N0]
    · exact ![I17N0]
    · exact ![I19N0, I19N1]
    · exact ![I23N0, I23N1]
    · exact ![I29N0]
    · exact ![I31N0, I31N1, I31N1]
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
    · exact ![9, 3]
    · exact ![125]
    · exact ![49, 7]
    · exact ![1331]
    · exact ![2197]
    · exact ![4913]
    · exact ![361, 19]
    · exact ![529, 23]
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
      exact NI2N1
      exact NI2N2
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
      exact NI31N1
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I7N0, I7N1, I19N1, I23N1, I31N0, I31N1]
  Il := ![[I2N0, I2N1, I2N2], [I3N0, I3N1], [], [I7N0, I7N1], [], [], [], [I19N1], [I23N1], [], [I31N0, I31N1, I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
