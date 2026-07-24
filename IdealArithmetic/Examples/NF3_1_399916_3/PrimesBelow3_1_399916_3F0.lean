
import IdealArithmetic.Examples.NF3_1_399916_3.RI3_1_399916_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 0, 1]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0], ![0, 0, 1]] 
 ![![2, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![0, 0, 1], ![122, 0, 1], ![61, 61, 0]]]
  hmulB := by decide  
  f := ![![![-60, 61, 0], ![-2, 2, -2]], ![![-30, 31, 0], ![-1, 1, -1]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![-1, 2, 0], ![0, 0, 2]], ![![0, 0, 1], ![61, 0, 1], ![0, 61, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![2, 0, 0], ![0, 0, 1]] ![![2, 0, 0], ![0, 0, 1]]
  ![![2, 0, 0], ![1, 1, 0]] where
 M := ![![![4, 0, 0], ![0, 0, 2]], ![![0, 0, 2], ![61, 61, 0]]]
 hmul := by decide  
 g := ![![![![1, -1, 0], ![2, 0, 0]], ![![0, 0, 1], ![0, 0, 0]]], ![![![0, 0, 1], ![0, 0, 0]], ![![20, 20, 0], ![21, 0, 0]]]]
 hle2 := by decide  
def MulI2N1 : IdealMulLeCertificate' Table 
  ![![2, 0, 0], ![1, 1, 0]] ![![2, 0, 0], ![0, 0, 1]]
  ![![2, 0, 0]] where
 M := ![![![4, 0, 0], ![0, 0, 2]], ![![2, 2, 0], ![122, 0, 2]]]
 hmul := by decide  
 g := ![![![![2, 0, 0]], ![![0, 0, 1]]], ![![![1, 1, 0]], ![![61, 0, 1]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![63, 62, -22]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![63, 62, -22]] 
 ![![3, 0, 0], ![0, 3, 0], ![0, 1, 1]] where
  M :=![![![63, 62, -22], ![-2622, 63, 102], ![6222, -1342, 125]]]
  hmulB := by decide  
  f := ![![![48253, 7258, 2570]], ![![320798, 48253, 17086]], ![![454348, 68341, 24199]]]
  g := ![![![21, 28, -22], ![-874, -13, 102], ![2074, -489, 125]]]
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
  c := ![735, 245, 8]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![245, 79, 8]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N0 B_one_repr
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 9 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![48253, 7258, 2570]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![48253, 7258, 2570]] 
 ![![3, 0, 0], ![0, 1, 0], ![2, 0, 1]] where
  M :=![![![48253, 7258, 2570], ![320798, 48253, 17086], ![1042246, 156770, 55511]]]
  hmulB := by decide  
  f := ![![![63, 62, -22]], ![![-874, 21, 34]], ![![2116, -406, 27]]]
  g := ![![![14371, 7258, 2570], ![95542, 48253, 17086], ![310408, 156770, 55511]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![63, 62, -22]] ![![48253, 7258, 2570]]
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


def P5P0 : CertificateIrreducibleZModOfList' 5 3 2 2 [2, 0, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 2, 2], [1, 2, 3], [0, 1]]
 g := ![![[1, 4, 1], []], ![[1, 2, 2, 3], [4, 4]], ![[0, 2, 3, 2], [3, 4]]]
 h' := ![![[3, 2, 2], [0, 0, 1], [0, 1]], ![[1, 2, 3], [1, 4, 2], [3, 2, 2]], ![[0, 1], [0, 1, 2], [1, 2, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 3], []]
 b := ![[], [1, 1, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where
  n := 3
  hpos := by decide
  P := [2, 0, 1, 1]
  hirr := P5P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![920105, 8805, -3010]
  a := ![2, -2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![184021, 1761, -602]
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


def P7P0 : CertificateIrreducibleZModOfList' 7 3 2 2 [6, 0, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 2, 2], [3, 4, 5], [0, 1]]
 g := ![![[6, 1, 4], [1]], ![[3, 4, 6, 2], [1, 1, 5, 1]], ![[1, 0, 0, 3], [4, 4, 4, 6]]]
 h' := ![![[6, 2, 2], [1, 0, 2], [0, 1]], ![[3, 4, 5], [0, 0, 1], [6, 2, 2]], ![[0, 1], [3, 0, 4], [3, 4, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5], []]
 b := ![[], [1, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 3
  hpos := by decide
  P := [6, 0, 5, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2186451960, -49701022, -34249362]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-312350280, -7100146, -4892766]
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


def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![2, 1, 0]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0], ![2, 1, 0]] 
 ![![11, 0, 0], ![2, 1, 0], ![4, 0, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![2, 1, 0], ![1, 2, 2], ![122, 0, 3]]]
  hmulB := by decide  
  f := ![![![-17, -36, -36], ![0, 198, 0]], ![![-3, -6, -6], ![1, 33, 0]], ![![-6, -13, -13], ![-1, 72, 0]]]
  g := ![![![1, 0, 0], ![-2, 11, 0], ![-4, 0, 11]], ![![0, 1, 0], ![-1, 2, 2], ![10, 0, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N0 : Nat.card (O ⧸ I11N0) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N0)

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := prime_ideal_of_norm_prime hp11.out _ NI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![4, 1, 0]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![11, 0, 0], ![4, 1, 0]] 
 ![![11, 0, 0], ![4, 1, 0], ![9, 0, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![4, 1, 0], ![1, 4, 2], ![122, 0, 5]]]
  hmulB := by decide  
  f := ![![![0, 11, 6], ![11, -33, 0]], ![![1, 4, 2], ![1, -11, 0]], ![![0, 9, 5], ![9, -27, 0]]]
  g := ![![![1, 0, 0], ![-4, 11, 0], ![-9, 0, 11]], ![![0, 1, 0], ![-3, 4, 2], ![7, 0, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![11, 0, 0], ![2, 1, 0]] ![![11, 0, 0], ![4, 1, 0]]
  ![![11, 0, 0], ![-1, 3, 1]] where
 M := ![![![121, 0, 0], ![44, 11, 0]], ![![22, 11, 0], ![9, 6, 2]]]
 hmul := by decide  
 g := ![![![![11, 0, 0], ![0, 0, 0]], ![![4, 1, 0], ![0, 0, 0]]], ![![![3, -2, -1], ![11, 0, 0]], ![![1, 0, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI11N1 : IdealMulLeCertificate' Table 
  ![![11, 0, 0], ![-1, 3, 1]] ![![11, 0, 0], ![4, 1, 0]]
  ![![11, 0, 0]] where
 M := ![![![121, 0, 0], ![44, 11, 0]], ![![-11, 33, 11], ![121, 11, 11]]]
 hmul := by decide  
 g := ![![![![11, 0, 0]], ![![4, 1, 0]]], ![![![-1, 3, 1]], ![![11, 1, 1]]]]
 hle2 := by decide  


def PBC11 : ContainsPrimesAboveP 11 ![I11N0, I11N1, I11N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
    exact isPrimeI11N1
    exact isPrimeI11N1
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


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [10, 9, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 1, 6], [9, 11, 7], [0, 1]]
 g := ![![[4, 4, 1], [4, 12], [1]], ![[12, 3, 1, 6], [5, 12], [2, 5, 3, 8]], ![[9, 2], [5, 9], [12, 6, 6, 5]]]
 h' := ![![[12, 1, 6], [8, 11, 1], [3, 4, 8], [0, 1]], ![[9, 11, 7], [1, 4, 12], [5, 0, 8], [12, 1, 6]], ![[0, 1], [6, 11], [11, 9, 10], [9, 11, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 12], []]
 b := ![[], [12, 3, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [10, 9, 5, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-927563, 1222, -6110]
  a := ![-2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-71351, 94, -470]
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


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [13, 8, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 6, 8], [12, 10, 9], [0, 1]]
 g := ![![[13, 10, 16], [14, 13], [13, 1], []], ![[12, 4, 13, 13], [7, 2], [11, 15], [10, 13]], ![[12, 11, 3, 9], [4, 4], [14, 2], [9, 13]]]
 h' := ![![[1, 6, 8], [6, 12, 13], [1, 2, 8], [0, 0, 1], [0, 1]], ![[12, 10, 9], [7, 0, 5], [8, 3, 11], [7, 1, 10], [1, 6, 8]], ![[0, 1], [8, 5, 16], [3, 12, 15], [10, 16, 6], [12, 10, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12, 11], []]
 b := ![[], [15, 9, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [13, 8, 4, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-60503, -1224, -2448]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3559, -72, -144]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![3, 1, 1]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0], ![3, 1, 1]] 
 ![![19, 0, 0], ![0, 19, 0], ![3, 1, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![3, 1, 1], ![123, 3, 3], ![183, 61, 4]]]
  hmulB := by decide  
  f := ![![![-2, -1, -1], ![19, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-3, -1, 19]], ![![0, 0, 1], ![6, 0, 3], ![9, 3, 4]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [14, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 18], [0, 1]]
 g := ![![[6, 6], [5, 9], [7], [1]], ![[15, 13], [9, 10], [7], [1]]]
 h' := ![![[11, 18], [6, 14], [3, 16], [5, 11], [0, 1]], ![[0, 1], [8, 5], [8, 3], [12, 8], [11, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [18, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [14, 8, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![14852, 777, 872]
  a := ![2, 19, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![644, -5, 872]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![-3, 1, 0]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![19, 0, 0], ![-3, 1, 0]] 
 ![![19, 0, 0], ![16, 1, 0], ![15, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![-3, 1, 0], ![1, -3, 2], ![122, 0, -2]]]
  hmulB := by decide  
  f := ![![![-95, 304, -204], ![38, 1938, 0]], ![![-78, 253, -170], ![39, 1615, 0]], ![![-75, 240, -161], ![30, 1530, 0]]]
  g := ![![![1, 0, 0], ![-16, 19, 0], ![-15, 0, 19]], ![![-1, 1, 0], ![1, -3, 2], ![8, 0, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![19, 0, 0], ![3, 1, 1]] ![![19, 0, 0], ![-3, 1, 0]]
  ![![19, 0, 0]] where
 M := ![![![361, 0, 0], ![-57, 19, 0]], ![![57, 19, 19], ![114, 0, 0]]]
 hmul := by decide  
 g := ![![![![19, 0, 0]], ![![-3, 1, 0]]], ![![![3, 1, 1]], ![![6, 0, 0]]]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![2, 1, 0]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0], ![2, 1, 0]] 
 ![![23, 0, 0], ![2, 1, 0], ![10, 0, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![2, 1, 0], ![1, 2, 2], ![122, 0, 3]]]
  hmulB := by decide  
  f := ![![![-83, -168, -168], ![0, 1932, 0]], ![![-7, -14, -14], ![1, 161, 0]], ![![-36, -73, -73], ![-1, 840, 0]]]
  g := ![![![1, 0, 0], ![-2, 23, 0], ![-10, 0, 23]], ![![0, 1, 0], ![-1, 2, 2], ![4, 0, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N0 : Nat.card (O ⧸ I23N0) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N0)

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := prime_ideal_of_norm_prime hp23.out _ NI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![3, 1, 0]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![23, 0, 0], ![3, 1, 0]] 
 ![![23, 0, 0], ![3, 1, 0], ![19, 0, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![3, 1, 0], ![1, 3, 2], ![122, 0, 4]]]
  hmulB := by decide  
  f := ![![![-108, -335, -224], ![-23, 2576, 0]], ![![-14, -42, -28], ![1, 322, 0]], ![![-90, -277, -185], ![-13, 2128, 0]]]
  g := ![![![1, 0, 0], ![-3, 23, 0], ![-19, 0, 23]], ![![0, 1, 0], ![-2, 3, 2], ![2, 0, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1

def I23N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1000, -103, 78]] i)))

def SI23N2: IdealEqSpanCertificate' Table ![![-1000, -103, 78]] 
 ![![23, 0, 0], ![17, 1, 0], ![17, 0, 1]] where
  M :=![![![-1000, -103, 78], ![9413, -1000, -128], ![-7808, 4758, -1103]]]
  hmulB := by decide  
  f := ![![![1712024, 257515, 91184]], ![![1760277, 264773, 93754]], ![![2873194, 432173, 153029]]]
  g := ![![![-25, -103, 78], ![1243, -1000, -128], ![-3041, 4758, -1103]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N2 : Nat.card (O ⧸ I23N2) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N2)

lemma isPrimeI23N2 : Ideal.IsPrime I23N2 := prime_ideal_of_norm_prime hp23.out _ NI23N2
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![23, 0, 0], ![2, 1, 0]] ![![23, 0, 0], ![3, 1, 0]]
  ![![-1712024, -257515, -91184]] where
 M := ![![![529, 0, 0], ![69, 23, 0]], ![![46, 23, 0], ![7, 5, 2]]]
 hmul := by decide  
 g := ![![![![23000, 2369, -1794]], ![![-6413, 1309, -106]]], ![![![-7413, 1206, -28]], ![![-1063, -165, 100]]]]
 hle2 := by decide  

def MulI23N1 : IdealMulLeCertificate' Table 
  ![![-1712024, -257515, -91184]] ![![-1000, -103, 78]]
  ![![23, 0, 0]] where
 M := ![![![-23, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![4, 1, 0]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0], ![4, 1, 0]] 
 ![![29, 0, 0], ![4, 1, 0], ![7, 0, 1]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![4, 1, 0], ![1, 4, 2], ![122, 0, 5]]]
  hmulB := by decide  
  f := ![![![-445, -1844, -924], ![-116, 13398, 0]], ![![-63, -252, -126], ![1, 1827, 0]], ![![-111, -446, -223], ![-2, 3234, 0]]]
  g := ![![![1, 0, 0], ![-4, 29, 0], ![-7, 0, 29]], ![![0, 1, 0], ![-1, 4, 2], ![3, 0, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N0 : Nat.card (O ⧸ I29N0) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N0)

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := prime_ideal_of_norm_prime hp29.out _ NI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![9, 1, 0]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![29, 0, 0], ![9, 1, 0]] 
 ![![29, 0, 0], ![9, 1, 0], ![18, 0, 1]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![9, 1, 0], ![1, 9, 2], ![122, 0, 10]]]
  hmulB := by decide  
  f := ![![![-240, -2569, -572], ![-145, 8294, 0]], ![![-79, -791, -176], ![-28, 2552, 0]], ![![-153, -1595, -355], ![-77, 5148, 0]]]
  g := ![![![1, 0, 0], ![-9, 29, 0], ![-18, 0, 29]], ![![0, 1, 0], ![-4, 9, 2], ![-2, 0, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1

def I29N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![128, -29, 3]] i)))

def SI29N2: IdealEqSpanCertificate' Table ![![128, -29, 3]] 
 ![![29, 0, 0], ![15, 1, 0], ![4, 0, 1]] where
  M :=![![![128, -29, 3], ![337, 128, -55], ![-3355, 183, 99]]]
  hmulB := by decide  
  f := ![![![-22737, -3420, -1211]], ![![-16973, -2553, -904]], ![![-20071, -3019, -1069]]]
  g := ![![![19, -29, 3], ![-47, 128, -55], ![-224, 183, 99]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N2 : Nat.card (O ⧸ I29N2) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N2)

lemma isPrimeI29N2 : Ideal.IsPrime I29N2 := prime_ideal_of_norm_prime hp29.out _ NI29N2
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![29, 0, 0], ![4, 1, 0]] ![![29, 0, 0], ![9, 1, 0]]
  ![![-22737, -3420, -1211]] where
 M := ![![![841, 0, 0], ![261, 29, 0]], ![![116, 29, 0], ![37, 13, 2]]]
 hmul := by decide  
 g := ![![![![3712, -841, 87]], ![![1489, -133, -28]]], ![![![849, 12, -43]], ![![83, 33, -14]]]]
 hle2 := by decide  

def MulI29N1 : IdealMulLeCertificate' Table 
  ![![-22737, -3420, -1211]] ![![128, -29, 3]]
  ![![29, 0, 0]] where
 M := ![![![29, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![-7, 10, 1]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0], ![-7, 10, 1]] 
 ![![31, 0, 0], ![0, 31, 0], ![24, 10, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![-7, 10, 1], ![132, -7, 21], ![1281, 61, 3]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-24, -10, 31]], ![![-1, 0, 1], ![-12, -7, 21], ![39, 1, 3]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [25, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [7, 30], [0, 1]]
 g := ![![[27, 5], [7, 4], [3, 18], [7, 1]], ![[0, 26], [4, 27], [5, 13], [14, 30]]]
 h' := ![![[7, 30], [11, 25], [18, 2], [11, 24], [0, 1]], ![[0, 1], [0, 6], [1, 29], [24, 7], [7, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [26, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [25, 24, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1657, 609, -60]
  a := ![-2, 3, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-7, 39, -60]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![10, 1, 0]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![31, 0, 0], ![10, 1, 0]] 
 ![![31, 0, 0], ![10, 1, 0], ![28, 0, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![10, 1, 0], ![1, 10, 2], ![122, 0, 11]]]
  hmulB := by decide  
  f := ![![![-431, -5310, -1064], ![-310, 16492, 0]], ![![-141, -1707, -342], ![-92, 5301, 0]], ![![-398, -4797, -961], ![-253, 14896, 0]]]
  g := ![![![1, 0, 0], ![-10, 31, 0], ![-28, 0, 31]], ![![0, 1, 0], ![-5, 10, 2], ![-6, 0, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![31, 0, 0], ![-7, 10, 1]] ![![31, 0, 0], ![10, 1, 0]]
  ![![31, 0, 0]] where
 M := ![![![961, 0, 0], ![310, 31, 0]], ![![-217, 310, 31], ![62, 93, 31]]]
 hmul := by decide  
 g := ![![![![31, 0, 0]], ![![10, 1, 0]]], ![![![-7, 10, 1]], ![![2, 3, 1]]]]
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


lemma PB179I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB179I0 : PrimesBelowBoundCertificateInterval O 1 31 179 where
  m := 11
  g := ![3, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB179I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N0, I2N0]
    · exact ![I3N0, I3N1]
    · exact ![I5N0]
    · exact ![I7N0]
    · exact ![I11N0, I11N1, I11N1]
    · exact ![I13N0]
    · exact ![I17N0]
    · exact ![I19N0, I19N1]
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
    · exact ![2, 2, 2]
    · exact ![9, 3]
    · exact ![125]
    · exact ![343]
    · exact ![11, 11, 11]
    · exact ![2197]
    · exact ![4913]
    · exact ![361, 19]
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
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
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
  β := ![I2N0, I3N0, I3N1, I5N0, I11N0, I11N1, I19N1, I23N0, I23N1, I23N2, I29N0, I29N1, I29N2, I31N1]
  Il := ![[I2N0, I2N0, I2N0], [I3N0, I3N1], [I5N0], [], [I11N0, I11N1, I11N1], [], [], [I19N1], [I23N0, I23N1, I23N2], [I29N0, I29N1, I29N2], [I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
