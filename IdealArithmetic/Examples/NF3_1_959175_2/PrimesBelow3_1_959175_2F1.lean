
import IdealArithmetic.Examples.NF3_1_959175_2.RI3_1_959175_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![15, -2, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![15, -2, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![15, 35, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![15, -2, 1], ![195, 11, -24], ![-310, 29, 4]]]
  hmulB := by decide  
  f := ![![![-14, 2, -1], ![37, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-15, -35, 37]], ![![0, -1, 1], ![15, 23, -24], ![-10, -3, 4]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [8, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 36], [0, 1]]
 g := ![![[25, 33], [3], [3, 26], [3], [1]], ![[11, 4], [3], [20, 11], [3], [1]]]
 h' := ![![[22, 36], [34, 12], [13, 15], [3, 10], [29, 22], [0, 1]], ![[0, 1], [2, 25], [10, 22], [1, 27], [32, 15], [22, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [12, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [8, 15, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5433, 2428, -1547]
  a := ![5, 1, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![774, 1529, -1547]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-13, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-13, 1, 0]] 
 ![![37, 0, 0], ![24, 1, 0], ![33, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-13, 1, 0], ![-5, -15, 13], ![185, -8, -11]]]
  hmulB := by decide  
  f := ![![![2186, 7155, -6188], ![-555, 17612, 0]], ![![1411, 4630, -4004], ![-369, 11396, 0]], ![![1956, 6381, -5519], ![-477, 15708, 0]]]
  g := ![![![1, 0, 0], ![-24, 37, 0], ![-33, 0, 37]], ![![-1, 1, 0], ![-2, -15, 13], ![20, -8, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![15, -2, 1]] ![![37, 0, 0], ![-13, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-481, 37, 0]], ![![555, -74, 37], ![0, 37, -37]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-13, 1, 0]]], ![![![15, -2, 1]], ![![0, 1, -1]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0]] 
 ![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [26, 29, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 28, 8], [26, 12, 33], [0, 1]]
 g := ![![[25, 30, 21], [27, 5], [0, 5], [11, 32, 1], []], ![[20, 2, 5, 4], [40, 39], [24, 40], [40, 38, 23, 4], [36, 23]], ![[2, 12, 13, 25], [21, 2], [4, 33], [14, 16, 33, 1], [11, 23]]]
 h' := ![![[6, 28, 8], [37, 4, 12], [1, 28, 13], [1, 38, 13], [0, 0, 1], [0, 1]], ![[26, 12, 33], [3, 20, 12], [31, 1, 11], [9, 35, 9], [2, 6, 12], [6, 28, 8]], ![[0, 1], [24, 17, 17], [18, 12, 17], [32, 9, 19], [21, 35, 28], [26, 12, 33]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28, 25], []]
 b := ![[], [36, 18, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [26, 29, 9, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![88238191, -7176599, 633491]
  a := ![-12, -7, 31]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2152151, -175039, 15451]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 68921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def PBC41 : ContainsPrimesAboveP 41 ![I41N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![41, 0, 0]]) timesTableT_eq_Table B_one_repr 41 (by decide) 𝕀

instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![24, -21, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![24, -21, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![24, 22, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![24, -21, 1], ![290, 58, -271], ![-3825, 181, -25]]]
  hmulB := by decide  
  f := ![![![-23, 21, -1], ![43, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-24, -22, 43]], ![![0, -1, 1], ![158, 140, -271], ![-75, 17, -25]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [42, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 42], [0, 1]]
 g := ![![[14, 36], [38, 9], [16], [20, 24], [1]], ![[2, 7], [35, 34], [16], [12, 19], [1]]]
 h' := ![![[14, 42], [38, 6], [29, 40], [20, 4], [1, 14], [0, 1]], ![[0, 1], [36, 37], [30, 3], [33, 39], [25, 29], [14, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [22, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [42, 29, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3544869, 4165288, -2233793]
  a := ![197, 67, -525]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1329207, 1239738, -2233793]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![13, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![13, 1, 0]] 
 ![![43, 0, 0], ![13, 1, 0], ![25, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![13, 1, 0], ![-5, 11, 13], ![185, -8, 15]]]
  hmulB := by decide  
  f := ![![![1434, -3419, -4030], ![387, 13330, 0]], ![![426, -1026, -1209], ![130, 3999, 0]], ![![831, -1988, -2343], ![234, 7750, 0]]]
  g := ![![![1, 0, 0], ![-13, 43, 0], ![-25, 0, 43]], ![![0, 1, 0], ![-11, 11, 13], ![-2, -8, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![24, -21, 1]] ![![43, 0, 0], ![13, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![559, 43, 0]], ![![1032, -903, 43], ![602, -215, -258]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![13, 1, 0]]], ![![![24, -21, 1]], ![![14, -5, -6]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![9, 1, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![9, 1, 0]] 
 ![![47, 0, 0], ![9, 1, 0], ![2, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![9, 1, 0], ![-5, 7, 13], ![185, -8, 11]]]
  hmulB := by decide  
  f := ![![![1321, -1916, -3549], ![235, 12831, 0]], ![![251, -365, -676], ![48, 2444, 0]], ![![52, -82, -151], ![32, 546, 0]]]
  g := ![![![1, 0, 0], ![-9, 47, 0], ![-2, 0, 47]], ![![0, 1, 0], ![-2, 7, 13], ![5, -8, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N0 : Nat.card (O ⧸ I47N0) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N0)

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := prime_ideal_of_norm_prime hp47.out _ NI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![10, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![10, 1, 0]] 
 ![![47, 0, 0], ![10, 1, 0], ![26, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![10, 1, 0], ![-5, 8, 13], ![185, -8, 12]]]
  hmulB := by decide  
  f := ![![![3491, -5822, -9438], ![658, 34122, 0]], ![![740, -1235, -2002], ![142, 7238, 0]], ![![1928, -3221, -5221], ![379, 18876, 0]]]
  g := ![![![1, 0, 0], ![-10, 47, 0], ![-26, 0, 47]], ![![0, 1, 0], ![-9, 8, 13], ![-1, -8, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1

def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-19, 1, 0]] i)))

def SI47N2: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-19, 1, 0]] 
 ![![47, 0, 0], ![28, 1, 0], ![34, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-19, 1, 0], ![-5, -21, 13], ![185, -8, -17]]]
  hmulB := by decide  
  f := ![![![8616, 40627, -25116], ![-2585, 90804, 0]], ![![5124, 24183, -14950], ![-1550, 54050, 0]], ![![6228, 29390, -18169], ![-1882, 65688, 0]]]
  g := ![![![1, 0, 0], ![-28, 47, 0], ![-34, 0, 47]], ![![-1, 1, 0], ![3, -21, 13], ![21, -8, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N2 : Nat.card (O ⧸ I47N2) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N2)

lemma isPrimeI47N2 : Ideal.IsPrime I47N2 := prime_ideal_of_norm_prime hp47.out _ NI47N2
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![9, 1, 0]] ![![47, 0, 0], ![10, 1, 0]]
  ![![47, 0, 0], ![21, 23, 1]] where
 M := ![![![2209, 0, 0], ![470, 47, 0]], ![![423, 47, 0], ![85, 17, 13]]]
 hmul := by decide  
 g := ![![![![26, -23, -1], ![47, 0, 0]], ![![-11, -22, -1], ![47, 0, 0]]], ![![![-12, -22, -1], ![47, 0, 0]], ![![-4, -6, 0], ![13, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![21, 23, 1]] ![![47, 0, 0], ![-19, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![-893, 47, 0]], ![![987, 1081, 47], ![-329, -470, 282]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![-19, 1, 0]]], ![![![21, 23, 1]], ![![-7, -10, 6]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1, I47N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
    exact isPrimeI47N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0 ⊙ MulI47N1)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![14, -19, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![14, -19, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![14, 34, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![14, -19, 1], ![280, 44, -245], ![-3455, 165, -31]]]
  hmulB := by decide  
  f := ![![![-13, 19, -1], ![53, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-14, -34, 53]], ![![0, -1, 1], ![70, 158, -245], ![-57, 23, -31]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [40, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [47, 52], [0, 1]]
 g := ![![[24, 4], [11], [36, 4], [16], [47, 1]], ![[0, 49], [11], [12, 49], [16], [41, 52]]]
 h' := ![![[47, 52], [12, 2], [44, 8], [38, 51], [28, 49], [0, 1]], ![[0, 1], [0, 51], [49, 45], [50, 2], [52, 4], [47, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [18, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [40, 6, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5420, 2419, -1430]
  a := ![5, 1, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![480, 963, -1430]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-20, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-20, 1, 0]] 
 ![![53, 0, 0], ![33, 1, 0], ![31, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-20, 1, 0], ![-5, -22, 13], ![185, -8, -18]]]
  hmulB := by decide  
  f := ![![![1231, 5946, -3510], ![-318, 14310, 0]], ![![761, 3700, -2184], ![-211, 8904, 0]], ![![717, 3478, -2053], ![-194, 8370, 0]]]
  g := ![![![1, 0, 0], ![-33, 53, 0], ![-31, 0, 53]], ![![-1, 1, 0], ![6, -22, 13], ![19, -8, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![14, -19, 1]] ![![53, 0, 0], ![-20, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-1060, 53, 0]], ![![742, -1007, 53], ![0, 424, -265]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-20, 1, 0]]], ![![![14, -19, 1]], ![![0, 8, -5]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-19, 12, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-19, 12, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![40, 12, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-19, 12, 1], ![125, -51, 158], ![2280, -83, -2]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-40, -12, 59]], ![![-1, 0, 1], ![-105, -33, 158], ![40, -1, -2]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [50, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [49, 58], [0, 1]]
 g := ![![[12, 46], [0, 48], [28], [43, 22], [49, 1]], ![[24, 13], [51, 11], [28], [0, 37], [39, 58]]]
 h' := ![![[49, 58], [0, 39], [43, 44], [33, 21], [28, 50], [0, 1]], ![[0, 1], [23, 20], [16, 15], [0, 38], [0, 9], [49, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [6, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [50, 10, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-20146, 7833, -3669]
  a := ![8, 6, -21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2146, 879, -3669]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![19, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![19, 1, 0]] 
 ![![59, 0, 0], ![19, 1, 0], ![2, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![19, 1, 0], ![-5, 17, 13], ![185, -8, 21]]]
  hmulB := by decide  
  f := ![![![383, -1430, -1092], ![118, 4956, 0]], ![![116, -460, -351], ![60, 1593, 0]], ![![3, -49, -37], ![35, 168, 0]]]
  g := ![![![1, 0, 0], ![-19, 59, 0], ![-2, 0, 59]], ![![0, 1, 0], ![-6, 17, 13], ![5, -8, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-19, 12, 1]] ![![59, 0, 0], ![19, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![1121, 59, 0]], ![![-1121, 708, 59], ![-236, 177, 177]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![19, 1, 0]]], ![![![-19, 12, 1]], ![![-4, 3, 3]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-19, 20, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-19, 20, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![42, 20, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-19, 20, 1], ![85, -67, 262], ![3760, -147, 14]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-42, -20, 61]], ![![-1, 0, 1], ![-179, -87, 262], ![52, -7, 14]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [7, 49, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 60], [0, 1]]
 g := ![![[7, 14], [41], [23, 12], [58, 42], [12, 1]], ![[53, 47], [41], [45, 49], [13, 19], [24, 60]]]
 h' := ![![[12, 60], [14, 40], [22, 23], [21, 16], [38, 15], [0, 1]], ![[0, 1], [6, 21], [54, 38], [30, 45], [35, 46], [12, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [59, 41]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [7, 49, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11272, 9931, -4173]
  a := ![-10, -3, 26]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3058, 1531, -4173]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-18, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-18, 1, 0]] 
 ![![61, 0, 0], ![43, 1, 0], ![47, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-18, 1, 0], ![-5, -20, 13], ![185, -8, -16]]]
  hmulB := by decide  
  f := ![![![8885, 37872, -24596], ![-1952, 115412, 0]], ![![6252, 26683, -17329], ![-1402, 81313, 0]], ![![6847, 29180, -18951], ![-1500, 88924, 0]]]
  g := ![![![1, 0, 0], ![-43, 61, 0], ![-47, 0, 61]], ![![-1, 1, 0], ![4, -20, 13], ![21, -8, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-19, 20, 1]] ![![61, 0, 0], ![-18, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-1098, 61, 0]], ![![-1159, 1220, 61], ![427, -427, 244]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-18, 1, 0]]], ![![![-19, 20, 1]], ![![7, -7, 4]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0)
instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0]] 
 ![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [36, 44, 25, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [61, 46, 4], [48, 20, 63], [0, 1]]
 g := ![![[56, 17, 21], [44, 25, 59], [23, 40], [44, 15], [42, 1], []], ![[21, 11, 18, 47], [3, 56, 20, 64], [40, 39], [16, 9], [61, 65], [35, 16]], ![[66, 20, 1, 31], [49, 15, 55, 28], [51, 9], [27, 22], [65, 39], [43, 16]]]
 h' := ![![[61, 46, 4], [24, 55, 50], [12, 65, 27], [61, 8, 43], [29, 59, 45], [0, 0, 1], [0, 1]], ![[48, 20, 63], [0, 48, 14], [7, 31, 63], [43, 13, 21], [4, 38, 64], [49, 12, 20], [61, 46, 4]], ![[0, 1], [63, 31, 3], [27, 38, 44], [56, 46, 3], [31, 37, 25], [19, 55, 46], [48, 20, 63]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 48], []]
 b := ![[], [41, 18, 55], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [36, 44, 25, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-159067179, 15755720, -5496010]
  a := ![15, 5, -40]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2374137, 235160, -82030]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 300763 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def PBC67 : ContainsPrimesAboveP 67 ![I67N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![67, 0, 0]]) timesTableT_eq_Table B_one_repr 67 (by decide) 𝕀

instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![221, 9, 13]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![221, 9, 13]] 
 ![![71, 0, 0], ![0, 71, 0], ![17, 28, 1]] where
  M :=![![![221, 9, 13], ![2360, 99, 143], ![2445, 97, 148]]]
  hmulB := by decide  
  f := ![![![11, -1, 0]], ![![5, 13, -13]], ![![2, 5, -5]]]
  g := ![![![0, -5, 13], ![-1, -55, 143], ![-1, -57, 148]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [22, 63, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 70], [0, 1]]
 g := ![![[19, 30], [48, 6], [], [40], [64], [1]], ![[46, 41], [25, 65], [], [40], [64], [1]]]
 h' := ![![[8, 70], [9, 39], [0, 19], [44], [70, 18], [49, 8], [0, 1]], ![[0, 1], [37, 32], [10, 52], [44], [1, 53], [42, 63], [8, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [47, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [22, 63, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-144810, 32676, -10406]
  a := ![-16, -16, 42]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![452, 4564, -10406]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![-11, 1, 0]] 
 ![![71, 0, 0], ![60, 1, 0], ![5, 0, 1]] where
  M :=![![![-11, 1, 0], ![-5, -13, 13], ![185, -8, -9]]]
  hmulB := by decide  
  f := ![![![-221, -9, -13]], ![![-220, -9, -13]], ![![-50, -2, -3]]]
  g := ![![![-1, 1, 0], ![10, -13, 13], ![10, -8, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![221, 9, 13]] ![![-11, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![-71, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0)
instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![21, -5, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![21, -5, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![21, 68, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![21, -5, 1], ![210, 23, -63], ![-865, 53, 4]]]
  hmulB := by decide  
  f := ![![![-20, 5, -1], ![73, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-21, -68, 73]], ![![0, -1, 1], ![21, 59, -63], ![-13, -3, 4]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [55, 34, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 72], [0, 1]]
 g := ![![[63, 4], [23], [55], [60, 23], [61], [1]], ![[0, 69], [23], [55], [8, 50], [61], [1]]]
 h' := ![![[39, 72], [68, 2], [47, 13], [58, 37], [35, 60], [18, 39], [0, 1]], ![[0, 1], [0, 71], [43, 60], [41, 36], [39, 13], [6, 34], [39, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34]]
 b := ![[], [70, 17]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [55, 34, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![127915, 208261, -106301]
  a := ![-44, -16, 117]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![32332, 101873, -106301]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-10, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-10, 1, 0]] 
 ![![73, 0, 0], ![63, 1, 0], ![69, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-10, 1, 0], ![-5, -12, 13], ![185, -8, -8]]]
  hmulB := by decide  
  f := ![![![756, 1837, -1989], ![-73, 11169, 0]], ![![661, 1584, -1716], ![1, 9636, 0]], ![![718, 1736, -1880], ![-44, 10557, 0]]]
  g := ![![![1, 0, 0], ![-63, 73, 0], ![-69, 0, 73]], ![![-1, 1, 0], ![-2, -12, 13], ![17, -8, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![21, -5, 1]] ![![73, 0, 0], ![-10, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-730, 73, 0]], ![![1533, -365, 73], ![0, 73, -73]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-10, 1, 0]]], ![![![21, -5, 1]], ![![0, 1, -1]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0)
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-2, -9, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-2, -9, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![77, 70, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-2, -9, 1], ![230, 8, -115], ![-1605, 85, -27]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-77, -70, 79]], ![![-1, -1, 1], ![115, 102, -115], ![6, 25, -27]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [27, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [73, 78], [0, 1]]
 g := ![![[9, 19], [72, 51], [27, 23], [57, 51], [36], [1]], ![[53, 60], [3, 28], [47, 56], [67, 28], [36], [1]]]
 h' := ![![[73, 78], [31, 16], [61, 29], [41, 55], [73, 29], [52, 73], [0, 1]], ![[0, 1], [14, 63], [45, 50], [27, 24], [57, 50], [9, 6], [73, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22]]
 b := ![[], [33, 11]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [27, 6, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7048, 37, -48]
  a := ![2, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![136, 43, -48]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![36, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![36, 1, 0]] 
 ![![79, 0, 0], ![36, 1, 0], ![27, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![36, 1, 0], ![-5, 34, 13], ![185, -8, 38]]]
  hmulB := by decide  
  f := ![![![3330, -26570, -10153], ![1264, 61699, 0]], ![![1523, -12077, -4615], ![554, 28045, 0]], ![![1134, -9081, -3470], ![441, 21087, 0]]]
  g := ![![![1, 0, 0], ![-36, 79, 0], ![-27, 0, 79]], ![![0, 1, 0], ![-20, 34, 13], ![-7, -8, 38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-2, -9, 1]] ![![79, 0, 0], ![36, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![2844, 79, 0]], ![![-158, -711, 79], ![158, -316, -79]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![36, 1, 0]]], ![![![-2, -9, 1]], ![![2, -4, -1]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0)


lemma PB278I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB278I1 : PrimesBelowBoundCertificateInterval O 31 79 278 where
  m := 11
  g := ![2, 1, 2, 3, 2, 2, 2, 1, 2, 2, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB278I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1, I47N2]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1]
    · exact ![I67N0]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1]
    · exact ![I79N0, I79N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC37
    · exact PBC41
    · exact PBC43
    · exact PBC47
    · exact PBC53
    · exact PBC59
    · exact PBC61
    · exact PBC67
    · exact PBC71
    · exact PBC73
    · exact PBC79
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![1369, 37]
    · exact ![68921]
    · exact ![1849, 43]
    · exact ![47, 47, 47]
    · exact ![2809, 53]
    · exact ![3481, 59]
    · exact ![3721, 61]
    · exact ![300763]
    · exact ![5041, 71]
    · exact ![5329, 73]
    · exact ![6241, 79]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
      exact NI47N2
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I37N1, I43N1, I47N0, I47N1, I47N2, I53N1, I59N1, I61N1, I71N1, I73N1, I79N1]
  Il := ![[I37N1], [], [I43N1], [I47N0, I47N1, I47N2], [I53N1], [I59N1], [I61N1], [], [I71N1], [I73N1], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
