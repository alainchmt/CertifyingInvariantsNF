
import IdealArithmetic.Examples.NF3_1_27559_1.RI3_1_27559_1
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
  c := ![-40620, -30410, -8454]
  a := ![0, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-20310, -15205, -4227]
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


def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9, -5, 0]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![-9, -5, 0]] 
 ![![3, 0, 0], ![0, 1, 0], ![0, 0, 3]] where
  M :=![![![-9, -5, 0], ![0, -14, -15], ![105, 50, -9]]]
  hmulB := by decide  
  f := ![![![-292, 15, -25]], ![![175, -9, 15]], ![![-490, 25, -42]]]
  g := ![![![-3, -5, 0], ![0, -14, -5], ![35, 50, -3]]]
  hle1 := by decide   
  hle2 := by decide  


def P3P0 : CertificateIrreducibleZModOfList' 3 2 2 1 [2, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 2], [0, 1]]
 g := ![![[2, 1]], ![[1, 2]]]
 h' := ![![[2, 2], [0, 1]], ![[0, 1], [2, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [1, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : CertifiedPrimeIdeal' SI3N0 3 where
  n := 2
  hpos := by decide
  P := [2, 1, 1]
  hirr := P3P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-33, -275, -252]
  a := ![-1, 1, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-11, -275, -84]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N0 B_one_repr
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 9 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-292, 15, -25]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![-292, 15, -25]] 
 ![![3, 0, 0], ![2, 1, 0], ![1, 0, 1]] where
  M :=![![![-292, 15, -25], ![525, -27, 45], ![-490, 25, -42]]]
  hmulB := by decide  
  f := ![![![-9, -5, 0]], ![![-6, -8, -5]], ![![32, 15, -3]]]
  g := ![![![-99, 15, -25], ![178, -27, 45], ![-166, 25, -42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![-9, -5, 0]] ![![-292, 15, -25]]
  ![![3, 0, 0]] where
 M := ![![![3, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P5P0 : CertificateIrreducibleZModOfList' 5 3 2 2 [3, 1, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 3, 3], [2, 1, 2], [0, 1]]
 g := ![![[3, 3, 1], []], ![[3, 4, 1, 3], [0, 4]], ![[4, 0, 0, 3], [1, 4]]]
 h' := ![![[1, 3, 3], [0, 0, 1], [0, 1]], ![[2, 1, 2], [1, 4, 1], [1, 3, 3]], ![[0, 1], [1, 1, 3], [2, 1, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 3], []]
 b := ![[], [4, 4, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where
  n := 3
  hpos := by decide
  P := [3, 1, 2, 1]
  hirr := P5P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-255420, 1190, -10240]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-51084, 238, -2048]
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


def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-175, 9, -15]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![-175, 9, -15]] 
 ![![7, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![-175, 9, -15], ![315, -16, 27], ![-294, 15, -25]]]
  hmulB := by decide  
  f := ![![![5, 0, -3]], ![![9, 5, 0]], ![![-3, 3, 5]]]
  g := ![![![-25, 9, -15], ![45, -16, 27], ![-42, 15, -25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N0)

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := prime_ideal_of_norm_prime hp7.out _ NI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![117, -6, 10]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![117, -6, 10]] 
 ![![7, 0, 0], ![3, 1, 0], ![3, 0, 1]] where
  M :=![![![117, -6, 10], ![-210, 11, -18], ![196, -10, 17]]]
  hmulB := by decide  
  f := ![![![7, 2, -2]], ![![9, 5, 0]], ![![-5, 0, 3]]]
  g := ![![![15, -6, 10], ![-27, 11, -18], ![25, -10, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![-175, 9, -15]] ![![117, -6, 10]]
  ![![-25305, 1299, -2167]] where
 M := ![![![-25305, 1299, -2167]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI7N1 : IdealMulLeCertificate' Table 
  ![![-25305, 1299, -2167]] ![![117, -6, 10]]
  ![![7, 0, 0]] where
 M := ![![![-3658207, 187789, -313271]]]
 hmul := by decide  
 g := ![![![![-522601, 26827, -44753]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N1, I7N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N1
    exact isPrimeI7N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0 ⊙ MulI7N1)
instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 1, -2]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![5, 1, -2]] 
 ![![11, 0, 0], ![0, 11, 0], ![3, 5, 1]] where
  M :=![![![5, 1, -2], ![42, 26, 3], ![-35, 4, 25]]]
  hmulB := by decide  
  f := ![![![-58, 3, -5]], ![![105, -5, 9]], ![![23, -1, 2]]]
  g := ![![![1, 1, -2], ![3, 1, 3], ![-10, -11, 25]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [2, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 10], [0, 1]]
 g := ![![[3, 3], [6, 3], [1]], ![[7, 8], [10, 8], [1]]]
 h' := ![![[5, 10], [10, 6], [9, 5], [0, 1]], ![[0, 1], [7, 5], [1, 6], [5, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [10, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 2
  hpos := by decide
  P := [2, 6, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-243, -383, -268]
  a := ![0, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![51, 87, -268]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![58, -3, 5]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![58, -3, 5]] 
 ![![11, 0, 0], ![7, 1, 0], ![7, 0, 1]] where
  M :=![![![58, -3, 5], ![-105, 5, -9], ![98, -5, 8]]]
  hmulB := by decide  
  f := ![![![-5, -1, 2]], ![![-7, -3, 1]], ![![0, -1, -1]]]
  g := ![![![4, -3, 5], ![-7, 5, -9], ![7, -5, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![5, 1, -2]] ![![58, -3, 5]]
  ![![11, 0, 0]] where
 M := ![![![-11, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0]] 
 ![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [2, 12, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [7, 1, 1], [2, 11, 12], [0, 1]]
 g := ![![[3, 7, 3], [6, 3], [1]], ![[9, 2, 3, 3], [1, 3], [2, 3, 12, 1]], ![[10, 10], [1, 12], [12, 1, 11, 12]]]
 h' := ![![[7, 1, 1], [5, 9, 9], [11, 1, 9], [0, 1]], ![[2, 11, 12], [12, 8, 4], [1, 0, 9], [7, 1, 1]], ![[0, 1], [7, 9], [10, 12, 8], [2, 11, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 10], []]
 b := ![[], [2, 12, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [2, 12, 4, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![25824825, 17783831, 3696160]
  a := ![1, 20, 41]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1986525, 1367987, 284320]
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


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [10, 0, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 12, 16], [5, 4, 1], [0, 1]]
 g := ![![[10, 14, 2], [0, 4], [7, 1], []], ![[5, 9, 11, 2], [9, 4], [8, 16], [0, 1]], ![[2, 13, 1, 16], [], [11, 8], [15, 1]]]
 h' := ![![[2, 12, 16], [4, 0, 6], [15, 7, 15], [0, 0, 1], [0, 1]], ![[5, 4, 1], [11, 7, 7], [4, 8, 2], [4, 4, 4], [2, 12, 16]], ![[0, 1], [2, 10, 4], [11, 2], [11, 13, 12], [5, 4, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 6], []]
 b := ![[], [10, 0, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [10, 0, 10, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11611, 6545, 102]
  a := ![-1, 2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![683, 385, 6]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -8, -8]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![-1, -8, -8]] 
 ![![19, 0, 0], ![0, 19, 0], ![12, 1, 1]] where
  M :=![![![-1, -8, -8], ![168, 71, -24], ![112, 136, 79]]]
  hmulB := by decide  
  f := ![![![-467, 24, -40]], ![![840, -43, 72]], ![![-292, 15, -25]]]
  g := ![![![5, 0, -8], ![24, 5, -24], ![-44, 3, 79]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [17, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 18], [0, 1]]
 g := ![![[4, 9], [7, 11], [7], [1]], ![[0, 10], [0, 8], [7], [1]]]
 h' := ![![[8, 18], [14, 3], [18, 12], [2, 8], [0, 1]], ![[0, 1], [0, 16], [0, 7], [9, 11], [8, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [17, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [17, 11, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-543, -886, -525]
  a := ![0, 3, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![303, -19, -525]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-467, 24, -40]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![-467, 24, -40]] 
 ![![19, 0, 0], ![16, 1, 0], ![17, 0, 1]] where
  M :=![![![-467, 24, -40], ![840, -43, 72], ![-784, 40, -67]]]
  hmulB := by decide  
  f := ![![![-1, -8, -8]], ![![8, -3, -8]], ![![5, 0, -3]]]
  g := ![![![-9, 24, -40], ![16, -43, 72], ![-15, 40, -67]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![-1, -8, -8]] ![![-467, 24, -40]]
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


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [5, 21, 21, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 19, 22], [19, 3, 1], [0, 1]]
 g := ![![[8, 3, 4], [20, 10, 6], [6, 2, 1], []], ![[6, 8, 20, 15], [9, 12, 9, 5], [12, 19, 6, 14], [10, 1]], ![[3, 8, 5, 18], [3, 7, 19, 16], [9, 20, 0, 16], [8, 1]]]
 h' := ![![[6, 19, 22], [15, 16, 2], [16, 2, 11], [0, 0, 1], [0, 1]], ![[19, 3, 1], [14, 8, 13], [12, 20, 8], [9, 13, 3], [6, 19, 22]], ![[0, 1], [18, 22, 8], [20, 1, 4], [22, 10, 19], [19, 3, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 3], []]
 b := ![[], [8, 11, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [5, 21, 21, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1256697, -853116, -165094]
  a := ![2, -8, -14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-54639, -37092, -7178]
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


def P29P0 : CertificateIrreducibleZModOfList' 29 3 2 4 [18, 22, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 26, 7], [18, 2, 22], [0, 1]]
 g := ![![[8, 3, 7], [14, 5], [10, 20, 13], [1]], ![[18, 12, 20, 7], [4, 24], [16, 6], [11, 6, 15, 24]], ![[16, 6, 17, 28], [22, 4], [10, 7, 28, 25], [23, 12, 12, 5]]]
 h' := ![![[1, 26, 7], [16, 6, 23], [23, 5, 18], [11, 7, 19], [0, 1]], ![[18, 2, 22], [9, 17, 1], [9, 25, 13], [6, 18], [1, 26, 7]], ![[0, 1], [4, 6, 5], [9, 28, 27], [24, 4, 10], [18, 2, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 13], []]
 b := ![[], [25, 21, 23], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 3
  hpos := by decide
  P := [18, 22, 10, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4611, -203, 406]
  a := ![13, 0, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![159, -7, 14]
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


def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 1, 0]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![1, 1, 0]] 
 ![![31, 0, 0], ![1, 1, 0], ![20, 0, 1]] where
  M :=![![![1, 1, 0], ![0, 2, 3], ![-21, -10, 1]]]
  hmulB := by decide  
  f := ![![![-32, 1, -3]], ![![1, 0, 0]], ![![-22, 1, -2]]]
  g := ![![![0, 1, 0], ![-2, 2, 3], ![-1, -10, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N0 : Nat.card (O ⧸ I31N0) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N0)

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := prime_ideal_of_norm_prime hp31.out _ NI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, -3, -5]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![3, -3, -5]] 
 ![![31, 0, 0], ![30, 1, 0], ![0, 0, 1]] where
  M :=![![![3, -3, -5], ![105, 50, -9], ![28, 65, 53]]]
  hmulB := by decide  
  f := ![![![3235, -166, 277]], ![![2943, -151, 252]], ![![175, -9, 15]]]
  g := ![![![3, -3, -5], ![-45, 50, -9], ![-62, 65, 53]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![1, 1, 0]] ![![3, -3, -5]]
  ![![108, 47, -14]] where
 M := ![![![108, 47, -14]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI31N1 : IdealMulLeCertificate' Table 
  ![![108, 47, -14]] ![![3, -3, -5]]
  ![![31, 0, 0]] where
 M := ![![![4867, 1116, -1705]]]
 hmul := by decide  
 g := ![![![![157, 36, -55]]]]
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


lemma PB47I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB47I0 : PrimesBelowBoundCertificateInterval O 1 31 47 where
  m := 11
  g := ![1, 2, 1, 3, 2, 1, 1, 2, 1, 1, 3]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB47I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0]
    · exact ![I3N0, I3N1]
    · exact ![I5N0]
    · exact ![I7N0, I7N1, I7N1]
    · exact ![I11N0, I11N1]
    · exact ![I13N0]
    · exact ![I17N0]
    · exact ![I19N0, I19N1]
    · exact ![I23N0]
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
    · exact ![8]
    · exact ![9, 3]
    · exact ![125]
    · exact ![7, 7, 7]
    · exact ![121, 11]
    · exact ![2197]
    · exact ![4913]
    · exact ![361, 19]
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
      exact NI3N1
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N1
      exact NI7N1
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
      exact NI31N1
  β := ![I2N0, I3N0, I3N1, I7N0, I7N1, I11N1, I19N1, I31N0, I31N1]
  Il := ![[I2N0], [I3N0, I3N1], [], [I7N0, I7N1, I7N1], [I11N1], [], [], [I19N1], [], [], [I31N0, I31N1, I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
