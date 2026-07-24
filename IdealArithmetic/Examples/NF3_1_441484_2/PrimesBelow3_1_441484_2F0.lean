
import IdealArithmetic.Examples.NF3_1_441484_2.RI3_1_441484_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![1, 1, 0]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0], ![1, 1, 0]] 
 ![![2, 0, 0], ![1, 1, 0], ![1, 0, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![1, 1, 0], ![3, 6, 11], ![-129, -2, -3]]]
  hmulB := by decide  
  f := ![![![-1, -5, -11], ![-2, 2, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, -2, -5], ![-2, 1, 0]]]
  g := ![![![1, 0, 0], ![-1, 2, 0], ![-1, 0, 2]], ![![0, 1, 0], ![-7, 6, 11], ![-62, -2, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![2, 0, 0], ![1, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![2, 0, 0], ![0, 1, 1]] where
 M := ![![![4, 0, 0], ![2, 2, 0]], ![![2, 2, 0], ![4, 7, 11]]]
 hmul := by decide  
 g := ![![![![2, 0, 0], ![0, 0, 0]], ![![1, 0, -1], ![2, 0, 0]]], ![![![1, 0, -1], ![2, 0, 0]], ![![2, 2, 4], ![3, 0, 0]]]]
 hle2 := by decide  
def MulI2N1 : IdealMulLeCertificate' Table 
  ![![2, 0, 0], ![0, 1, 1]] ![![2, 0, 0], ![1, 1, 0]]
  ![![2, 0, 0]] where
 M := ![![![4, 0, 0], ![2, 2, 0]], ![![0, 2, 2], ![-126, 4, 8]]]
 hmul := by decide  
 g := ![![![![2, 0, 0]], ![![1, 1, 0]]], ![![![0, 1, 1]], ![![-63, 2, 4]]]]
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
instance hp3 : Fact (Nat.Prime 3) := {out := by norm_num}

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![0, 1, 0]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0], ![0, 1, 0]] 
 ![![3, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![0, 1, 0], ![3, 5, 11], ![-129, -2, -4]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![1, 1, 4], ![2, -1, 0]]]
  g := ![![![1, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![0, 1, 0], ![1, 5, 11], ![-43, -2, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![1, -1, 1]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![3, 0, 0], ![1, -1, 1]] 
 ![![3, 0, 0], ![0, 3, 0], ![1, 2, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![1, -1, 1], ![-132, -6, -15], ![234, -9, 6]]]
  hmulB := by decide  
  f := ![![![0, 1, -1], ![3, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-1, -2, 3]], ![![0, -1, 1], ![-39, 8, -15], ![76, -7, 6]]]
  hle1 := by decide   
  hle2 := by decide  


def P3P1 : CertificateIrreducibleZModOfList' 3 2 2 1 [2, 1, 1] where
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

def PI3N1 : CertifiedPrimeIdeal' SI3N1 3 where
  n := 2
  hpos := by decide
  P := [2, 1, 1]
  hirr := P3P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4207, -1385, 44]
  a := ![-3, -6, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1417, -491, 44]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N1 B_one_repr
lemma NI3N1 : Nat.card (O ⧸ I3N1) = 9 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![0, 1, 0]] ![![3, 0, 0], ![1, -1, 1]]
  ![![3, 0, 0]] where
 M := ![![![9, 0, 0], ![3, -3, 3]], ![![0, 3, 0], ![-132, -6, -15]]]
 hmul := by decide  
 g := ![![![![3, 0, 0]], ![![1, -1, 1]]], ![![![0, 1, 0]], ![![-44, -2, -5]]]]
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


def P5P0 : CertificateIrreducibleZModOfList' 5 3 2 2 [1, 3, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 2, 4], [2, 2, 1], [0, 1]]
 g := ![![[3, 4, 1], []], ![[0, 2, 4, 1], [0, 1]], ![[2, 2, 1, 4], [3, 1]]]
 h' := ![![[2, 2, 4], [0, 0, 1], [0, 1]], ![[2, 2, 1], [4, 2, 2], [2, 2, 4]], ![[0, 1], [1, 3, 2], [2, 2, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 4], []]
 b := ![[], [0, 4, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where
  n := 3
  hpos := by decide
  P := [1, 3, 1, 1]
  hirr := P5P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![26266800, 72350, 322565]
  a := ![7, 9, 26]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5253360, 14470, 64513]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![-3, 1, 1]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0], ![-3, 1, 1]] 
 ![![7, 0, 0], ![0, 7, 0], ![4, 1, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![-3, 1, 1], ![-126, 0, 7], ![-24, -13, -6]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-4, -1, 7]], ![![-1, 0, 1], ![-22, -1, 7], ![0, -1, -6]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 2 2 2 [5, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 6], [0, 1]]
 g := ![![[2, 2], [4, 1]], ![[3, 5], [1, 6]]]
 h' := ![![[4, 6], [1, 4], [0, 1]], ![[0, 1], [3, 3], [4, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [6, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 2
  hpos := by decide
  P := [5, 3, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8448642, -2389511, 118442]
  a := ![-131, -260, -459]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1274630, -358279, 118442]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![0, 1, 0]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![7, 0, 0], ![0, 1, 0]] 
 ![![7, 0, 0], ![0, 1, 0], ![6, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![0, 1, 0], ![3, 5, 11], ![-129, -2, -4]]]
  hmulB := by decide  
  f := ![![![-14, -25, -55], ![0, 35, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-12, -21, -47], ![-3, 30, 0]]]
  g := ![![![1, 0, 0], ![0, 7, 0], ![-6, 0, 7]], ![![0, 1, 0], ![-9, 5, 11], ![-15, -2, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![7, 0, 0], ![-3, 1, 1]] ![![7, 0, 0], ![0, 1, 0]]
  ![![7, 0, 0]] where
 M := ![![![49, 0, 0], ![0, 7, 0]], ![![-21, 7, 7], ![-126, 0, 7]]]
 hmul := by decide  
 g := ![![![![7, 0, 0]], ![![0, 1, 0]]], ![![![-3, 1, 1]], ![![-18, 0, 1]]]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-77, 10, 12]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![-77, 10, 12]] 
 ![![11, 0, 0], ![2, 1, 0], ![2, 0, 1]] where
  M :=![![![-77, 10, 12], ![-1518, -51, 62], ![-30, -152, -105]]]
  hmulB := by decide  
  f := ![![![-14779, 774, -1232]], ![![11972, -627, 998]], ![![-23524, 1232, -1961]]]
  g := ![![![-11, 10, 12], ![-140, -51, 62], ![44, -152, -105]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N0 : Nat.card (O ⧸ I11N0) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N0)

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := prime_ideal_of_norm_prime hp11.out _ NI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![90526742, -4741060, 7546449]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![90526742, -4741060, 7546449]] 
 ![![11, 0, 0], ![4, 1, 0], ![2, 0, 1]] where
  M :=![![![90526742, -4741060, 7546449], ![-987715101, 51728544, -82337456], ![1403973885, -73528819, 117037431]]]
  hmulB := by decide  
  f := ![![![-14000, 3129, 3104]], ![![-40639, 723, 3129]], ![![-9611, -3104, -1564]]]
  g := ![![![8581644, -4741060, 7546449], ![-93632215, 51728544, -82337456], ![133092209, -73528819, 117037431]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1

def I11N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![166, 1, -10]] i)))

def SI11N2: IdealEqSpanCertificate' Table ![![166, 1, -10]] 
 ![![11, 0, 0], ![4, 1, 0], ![8, 0, 1]] where
  M :=![![![166, 1, -10], ![1293, 191, 51], ![-1179, 108, 152]]]
  hmulB := by decide  
  f := ![![![-23524, 1232, -1961]], ![![14779, -774, 1232]], ![![-50275, 2633, -4191]]]
  g := ![![![22, 1, -10], ![11, 191, 51], ![-257, 108, 152]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N2 : Nat.card (O ⧸ I11N2) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N2)

lemma isPrimeI11N2 : Ideal.IsPrime I11N2 := prime_ideal_of_norm_prime hp11.out _ NI11N2
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![-77, 10, 12]] ![![90526742, -4741060, 7546449]]
  ![![-23524, 1232, -1961]] where
 M := ![![![-23524, 1232, -1961]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI11N1 : IdealMulLeCertificate' Table 
  ![![-23524, 1232, -1961]] ![![166, 1, -10]]
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


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [6, 5, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 5, 7], [6, 7, 6], [0, 1]]
 g := ![![[4, 0, 9], [3, 12], [1]], ![[12, 4, 12, 2], [2, 12], [7, 0, 8, 5]], ![[3, 0, 0, 7], [10, 9], [6, 3, 1, 8]]]
 h' := ![![[2, 5, 7], [5, 12, 10], [7, 8, 8], [0, 1]], ![[6, 7, 6], [0, 12, 11], [5, 12, 8], [2, 5, 7]], ![[0, 1], [9, 2, 5], [11, 6, 10], [6, 7, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 10], []]
 b := ![[], [7, 8, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [6, 5, 5, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-26141791, -24180, -62868]
  a := ![-7, -10, -26]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2010907, -1860, -4836]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![6, 4, 1]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0], ![6, 4, 1]] 
 ![![17, 0, 0], ![0, 17, 0], ![6, 4, 1]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]], ![![6, 4, 1], ![-117, 24, 40], ![-411, -19, -9]]]
  hmulB := by decide  
  f := ![![![-5, -4, -1], ![17, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-6, -4, 17]], ![![0, 0, 1], ![-21, -8, 40], ![-21, 1, -9]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 2 2 4 [11, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 16], [0, 1]]
 g := ![![[12, 9], [15], [16], [1]], ![[14, 8], [15], [16], [1]]]
 h' := ![![[4, 16], [4, 14], [13, 10], [6, 4], [0, 1]], ![[0, 1], [9, 3], [2, 7], [5, 13], [4, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [12, 11]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 2
  hpos := by decide
  P := [11, 13, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4234, -1457, -88]
  a := ![-3, -6, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-218, -65, -88]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![-6, 1, 0]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![17, 0, 0], ![-6, 1, 0]] 
 ![![17, 0, 0], ![11, 1, 0], ![9, 0, 1]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]], ![![-6, 1, 0], ![3, -1, 11], ![-129, -2, -10]]]
  hmulB := by decide  
  f := ![![![559, -198, 2310], ![-204, -3570, 0]], ![![364, -128, 1485], ![-118, -2295, 0]], ![![297, -105, 1223], ![-105, -1890, 0]]]
  g := ![![![1, 0, 0], ![-11, 17, 0], ![-9, 0, 17]], ![![-1, 1, 0], ![-5, -1, 11], ![-1, -2, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![17, 0, 0], ![6, 4, 1]] ![![17, 0, 0], ![-6, 1, 0]]
  ![![17, 0, 0]] where
 M := ![![![289, 0, 0], ![-102, 17, 0]], ![![102, 68, 17], ![-153, 0, 34]]]
 hmul := by decide  
 g := ![![![![17, 0, 0]], ![![-6, 1, 0]]], ![![![6, 4, 1]], ![![-9, 0, 2]]]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![1, 1, 0]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0], ![1, 1, 0]] 
 ![![19, 0, 0], ![1, 1, 0], ![17, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![1, 1, 0], ![3, 6, 11], ![-129, -2, -3]]]
  hmulB := by decide  
  f := ![![![39, 77, 143], ![19, -247, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![35, 69, 128], ![15, -221, 0]]]
  g := ![![![1, 0, 0], ![-1, 19, 0], ![-17, 0, 19]], ![![0, 1, 0], ![-10, 6, 11], ![-4, -2, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N0 : Nat.card (O ⧸ I19N0) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N0)

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := prime_ideal_of_norm_prime hp19.out _ NI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![-1, 1, 0]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![19, 0, 0], ![-1, 1, 0]] 
 ![![19, 0, 0], ![18, 1, 0], ![11, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![-1, 1, 0], ![3, 4, 11], ![-129, -2, -5]]]
  hmulB := by decide  
  f := ![![![596, 791, 2178], ![19, -3762, 0]], ![![563, 747, 2057], ![20, -3553, 0]], ![![345, 458, 1261], ![10, -2178, 0]]]
  g := ![![![1, 0, 0], ![-18, 19, 0], ![-11, 0, 19]], ![![-1, 1, 0], ![-10, 4, 11], ![-2, -2, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![19, 0, 0], ![1, 1, 0]] ![![19, 0, 0], ![-1, 1, 0]]
  ![![19, 0, 0], ![-5, -3, 1]] where
 M := ![![![361, 0, 0], ![-19, 19, 0]], ![![19, 19, 0], ![2, 5, 11]]]
 hmul := by decide  
 g := ![![![![19, 0, 0], ![0, 0, 0]], ![![4, 4, -1], ![19, 0, 0]]], ![![![1, 1, 0], ![0, 0, 0]], ![![-2, -1, 1], ![-8, 0, 0]]]]
 hle2 := by decide  

def MulI19N1 : IdealMulLeCertificate' Table 
  ![![19, 0, 0], ![-5, -3, 1]] ![![19, 0, 0], ![-1, 1, 0]]
  ![![19, 0, 0]] where
 M := ![![![361, 0, 0], ![-19, 19, 0]], ![![-95, -57, 19], ![-133, -19, -38]]]
 hmul := by decide  
 g := ![![![![19, 0, 0]], ![![-1, 1, 0]]], ![![![-5, -3, 1]], ![![-7, -1, -2]]]]
 hle2 := by decide  


def PBC19 : ContainsPrimesAboveP 19 ![I19N0, I19N1, I19N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N1
    exact isPrimeI19N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 19 (by decide) (𝕀 ⊙ MulI19N0 ⊙ MulI19N1)
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


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [13, 0, 21, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 15, 1], [5, 7, 22], [0, 1]]
 g := ![![[2, 3, 18], [22, 11, 2], [4, 2, 1], []], ![[10, 3, 13, 2], [15, 14, 6, 18], [0, 17, 12, 3], [9, 1]], ![[5, 1, 12, 14], [1, 7, 3, 14], [11, 3, 13, 5], [11, 1]]]
 h' := ![![[20, 15, 1], [13, 8, 8], [17, 20, 18], [0, 0, 1], [0, 1]], ![[5, 7, 22], [22, 9, 18], [14, 10, 8], [7, 12, 7], [20, 15, 1]], ![[0, 1], [6, 6, 20], [17, 16, 20], [20, 11, 15], [5, 7, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19, 18], []]
 b := ![[], [13, 16, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [13, 0, 21, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8121369, -4095564, -2357638]
  a := ![5, 28, 18]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-353103, -178068, -102506]
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

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2467, -219, 5]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![-2467, -219, 5]] 
 ![![29, 0, 0], ![0, 29, 0], ![17, 20, 1]] where
  M :=![![![-2467, -219, 5], ![-1302, -3572, -2429], ![28776, 383, -1586]]]
  hmulB := by decide  
  f := ![![![227431, -11911, 18959]], ![![-2481444, 129958, -206857]], ![![-1456391, 76274, -121407]]]
  g := ![![![-88, -11, 5], ![1379, 1552, -2429], ![1922, 1107, -1586]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [8, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 28], [0, 1]]
 g := ![![[28, 22], [28], [27, 4], [8, 1]], ![[1, 7], [28], [1, 25], [16, 28]]]
 h' := ![![[8, 28], [3, 14], [16, 17], [23, 27], [0, 1]], ![[0, 1], [28, 15], [7, 12], [7, 2], [8, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [22, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [8, 21, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6192, -3882, -342]
  a := ![-5, -6, -18]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![414, 102, -342]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227431, -11911, 18959]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![227431, -11911, 18959]] 
 ![![29, 0, 0], ![16, 1, 0], ![4, 0, 1]] where
  M :=![![![227431, -11911, 18959], ![-2481444, 129958, -206857], ![3527214, -184727, 294034]]]
  hmulB := by decide  
  f := ![![![-2467, -219, 5]], ![![-1406, -244, -81]], ![![652, -17, -54]]]
  g := ![![![11799, -11911, 18959], ![-128736, 129958, -206857], ![182990, -184727, 294034]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![-2467, -219, 5]] ![![227431, -11911, 18959]]
  ![![29, 0, 0]] where
 M := ![![![29, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![14, 1, 0]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0], ![14, 1, 0]] 
 ![![31, 0, 0], ![14, 1, 0], ![24, 0, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![14, 1, 0], ![3, 19, 11], ![-129, -2, 10]]]
  hmulB := by decide  
  f := ![![![125, 1136, 660], ![124, -1860, 0]], ![![53, 511, 297], ![63, -837, 0]], ![![104, 880, 511], ![80, -1440, 0]]]
  g := ![![![1, 0, 0], ![-14, 31, 0], ![-24, 0, 31]], ![![0, 1, 0], ![-17, 19, 11], ![-11, -2, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N0 : Nat.card (O ⧸ I31N0) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N0)

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := prime_ideal_of_norm_prime hp31.out _ NI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![-9, 1, 0]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![31, 0, 0], ![-9, 1, 0]] 
 ![![31, 0, 0], ![22, 1, 0], ![28, 0, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![-9, 1, 0], ![3, -4, 11], ![-129, -2, -13]]]
  hmulB := by decide  
  f := ![![![730, -1049, 2904], ![-217, -8184, 0]], ![![517, -743, 2057], ![-154, -5797, 0]], ![![655, -947, 2623], ![-211, -7392, 0]]]
  g := ![![![1, 0, 0], ![-22, 31, 0], ![-28, 0, 31]], ![![-1, 1, 0], ![-7, -4, 11], ![9, -2, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1

def I31N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![409, -8, -32]] i)))

def SI31N2: IdealEqSpanCertificate' Table ![![409, -8, -32]] 
 ![![31, 0, 0], ![25, 1, 0], ![11, 0, 1]] where
  M :=![![![409, -8, -32], ![4104, 433, 40], ![-2328, 368, 409]]]
  hmulB := by decide  
  f := ![![![-162377, 8504, -13536]], ![![-73799, 3865, -6152]], ![![-138853, 7272, -11575]]]
  g := ![![![31, -8, -32], ![-231, 433, 40], ![-517, 368, 409]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N2 : Nat.card (O ⧸ I31N2) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N2)

lemma isPrimeI31N2 : Ideal.IsPrime I31N2 := prime_ideal_of_norm_prime hp31.out _ NI31N2
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![31, 0, 0], ![14, 1, 0]] ![![31, 0, 0], ![-9, 1, 0]]
  ![![162377, -8504, 13536]] where
 M := ![![![961, 0, 0], ![-279, 31, 0]], ![![434, 31, 0], ![-123, 10, 11]]]
 hmul := by decide  
 g := ![![![![-12679, 248, 992]], ![![-423, -505, -328]]], ![![![-9830, -321, 408]], ![![1125, -302, -285]]]]
 hle2 := by decide  

def MulI31N1 : IdealMulLeCertificate' Table 
  ![![162377, -8504, 13536]] ![![409, -8, -32]]
  ![![31, 0, 0]] where
 M := ![![![-31, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


lemma PB189I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB189I0 : PrimesBelowBoundCertificateInterval O 1 31 189 where
  m := 11
  g := ![3, 2, 1, 2, 3, 1, 2, 3, 1, 2, 3]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB189I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N0, I2N0]
    · exact ![I3N0, I3N1]
    · exact ![I5N0]
    · exact ![I7N0, I7N1]
    · exact ![I11N0, I11N1, I11N2]
    · exact ![I13N0]
    · exact ![I17N0, I17N1]
    · exact ![I19N0, I19N1, I19N1]
    · exact ![I23N0]
    · exact ![I29N0, I29N1]
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
    · exact ![3, 9]
    · exact ![125]
    · exact ![49, 7]
    · exact ![11, 11, 11]
    · exact ![2197]
    · exact ![289, 17]
    · exact ![19, 19, 19]
    · exact ![12167]
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
      exact NI2N0
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
      exact NI31N1
      exact NI31N2
  β := ![I2N0, I3N0, I3N1, I5N0, I7N0, I7N1, I11N0, I11N1, I11N2, I17N1, I19N0, I19N1, I29N1, I31N0, I31N1, I31N2]
  Il := ![[I2N0, I2N0, I2N0], [I3N0, I3N1], [I5N0], [I7N0, I7N1], [I11N0, I11N1, I11N2], [], [I17N1], [I19N0, I19N1, I19N1], [], [I29N1], [I31N0, I31N1, I31N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
