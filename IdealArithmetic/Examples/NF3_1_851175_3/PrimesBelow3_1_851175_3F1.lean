
import IdealArithmetic.Examples.NF3_1_851175_3.RI3_1_851175_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0]] 
 ![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [31, 24, 12, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 21, 8], [16, 15, 29], [0, 1]]
 g := ![![[20, 14, 21], [34, 7], [17, 28, 7], [25, 1], []], ![[10, 15, 29, 24], [22, 11], [0, 27, 1, 31], [13, 3], [12, 27]], ![[14, 13, 13, 18], [6, 25], [22, 15, 22, 19], [34, 34], [28, 27]]]
 h' := ![![[9, 21, 8], [26, 33, 13], [28, 23, 9], [2, 35, 9], [0, 0, 1], [0, 1]], ![[16, 15, 29], [18, 10, 15], [21, 13, 23], [29, 6, 8], [5, 30, 15], [9, 21, 8]], ![[0, 1], [35, 31, 9], [31, 1, 5], [12, 33, 20], [17, 7, 21], [16, 15, 29]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22, 21], []]
 b := ![[], [23, 7, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [31, 24, 12, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![14023, 24864, -38961]
  a := ![1, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![379, 672, -1053]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 50653 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def PBC37 : ContainsPrimesAboveP 37 ![I37N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![37, 0, 0]]) timesTableT_eq_Table B_one_repr 37 (by decide) 𝕀

instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![7, 11, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![7, 11, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![7, 11, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![7, 11, 1], ![101, -17, 32], ![1169, -336, -38]]]
  hmulB := by decide  
  f := ![![![-6, -11, -1], ![41, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-7, -11, 41]], ![![0, 0, 1], ![-3, -9, 32], ![35, 2, -38]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [38, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 40], [0, 1]]
 g := ![![[11, 40], [40], [8], [14, 23], [1]], ![[19, 1], [40], [8], [35, 18], [1]]]
 h' := ![![[33, 40], [7, 9], [25, 32], [1, 7], [3, 33], [0, 1]], ![[0, 1], [17, 32], [15, 9], [27, 34], [26, 8], [33, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [15, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [38, 8, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4009, 3136, -2160]
  a := ![-3, 0, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![271, 656, -2160]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![9, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![9, 1, 0]] 
 ![![41, 0, 0], ![9, 1, 0], ![38, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![9, 1, 0], ![-1, 10, 3], ![112, -35, 8]]]
  hmulB := by decide  
  f := ![![![1281, -12800, -3840], ![0, 52480, 0]], ![![280, -2800, -840], ![1, 11480, 0]], ![![1191, -11863, -3559], ![-17, 48640, 0]]]
  g := ![![![1, 0, 0], ![-9, 41, 0], ![-38, 0, 41]], ![![0, 1, 0], ![-5, 10, 3], ![3, -35, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![7, 11, 1]] ![![41, 0, 0], ![9, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![369, 41, 0]], ![![287, 451, 41], ![164, 82, 41]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![9, 1, 0]]], ![![![7, 11, 1]], ![![4, 2, 1]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0]] 
 ![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [21, 31, 18, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 30, 7], [18, 12, 36], [0, 1]]
 g := ![![[14, 20, 17], [15, 4, 14], [29, 6], [35, 25, 1], []], ![[27, 35, 10, 34], [11, 36, 18, 39], [32, 4], [14, 17, 38, 19], [11, 6]], ![[32, 5, 11, 23], [14, 5, 18, 17], [40, 38], [11, 34, 13, 21], [25, 6]]]
 h' := ![![[7, 30, 7], [29, 5, 24], [9, 30, 10], [39, 24, 36], [0, 0, 1], [0, 1]], ![[18, 12, 36], [39, 11, 22], [33, 0, 29], [19, 17, 41], [33, 39, 12], [7, 30, 7]], ![[0, 1], [25, 27, 40], [1, 13, 4], [29, 2, 9], [14, 4, 30], [18, 12, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27, 36], []]
 b := ![[], [42, 10, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [21, 31, 18, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1019201738, -62987260, -387507400]
  a := ![1, -64, -67]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![23702366, -1464820, -9011800]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 79507 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def PBC43 : ContainsPrimesAboveP 43 ![I43N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![43, 0, 0]]) timesTableT_eq_Table B_one_repr 43 (by decide) 𝕀

instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0]] 
 ![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [2, 13, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [44, 31, 8], [0, 15, 39], [0, 1]]
 g := ![![[25, 16, 34], [35, 19, 32], [5, 32, 4], [43, 44, 1], []], ![[35, 2, 40, 28], [31, 4], [27, 46, 27, 2], [43, 12, 32, 14], [22, 17]], ![[0, 20, 5, 15], [22, 26, 16, 26], [22, 23, 30, 44], [25, 34, 24, 20], [38, 17]]]
 h' := ![![[44, 31, 8], [24, 30, 38], [37, 29, 19], [8, 11, 2], [0, 0, 1], [0, 1]], ![[0, 15, 39], [14, 32, 11], [37, 27], [46, 34, 24], [12, 11, 15], [44, 31, 8]], ![[0, 1], [3, 32, 45], [3, 38, 28], [44, 2, 21], [18, 36, 31], [0, 15, 39]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32, 45], []]
 b := ![[], [21, 34, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [2, 13, 3, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3191300, 1533563, -593516]
  a := ![3, -1, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-67900, 32629, -12628]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 103823 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def PBC47 : ContainsPrimesAboveP 47 ![I47N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![47, 0, 0]]) timesTableT_eq_Table B_one_repr 47 (by decide) 𝕀

instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![15, -3, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![15, -3, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![15, 50, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![15, -3, 1], ![115, -23, -10], ![-399, 154, -16]]]
  hmulB := by decide  
  f := ![![![-14, 3, -1], ![53, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-15, -50, 53]], ![![0, -1, 1], ![5, 9, -10], ![-3, 18, -16]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [25, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [35, 52], [0, 1]]
 g := ![![[41, 17], [4], [18, 10], [43], [35, 1]], ![[0, 36], [4], [50, 43], [43], [17, 52]]]
 h' := ![![[35, 52], [46, 32], [27, 51], [25, 40], [26, 34], [0, 1]], ![[0, 1], [0, 21], [10, 2], [47, 13], [50, 19], [35, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [25, 44]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [25, 18, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![817, -15, -366]
  a := ![1, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![119, 345, -366]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![10, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![10, 1, 0]] 
 ![![53, 0, 0], ![10, 1, 0], ![16, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![10, 1, 0], ![-1, 11, 3], ![112, -35, 9]]]
  hmulB := by decide  
  f := ![![![-41, 351, 96], ![53, -1696, 0]], ![![-6, 66, 18], ![1, -318, 0]], ![![-12, 106, 29], ![14, -512, 0]]]
  g := ![![![1, 0, 0], ![-10, 53, 0], ![-16, 0, 53]], ![![0, 1, 0], ![-3, 11, 3], ![6, -35, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![15, -3, 1]] ![![53, 0, 0], ![10, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![530, 53, 0]], ![![795, -159, 53], ![265, -53, 0]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![10, 1, 0]]], ![![![15, -3, 1]], ![![5, -1, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![7, -8, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![7, -8, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![7, 51, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![7, -8, 1], ![120, -36, -25], ![-959, 329, -19]]]
  hmulB := by decide  
  f := ![![![-6, 8, -1], ![59, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-7, -51, 59]], ![![0, -1, 1], ![5, 21, -25], ![-14, 22, -19]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [24, 31, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [28, 58], [0, 1]]
 g := ![![[48, 20], [19, 19], [4], [42, 49], [28, 1]], ![[18, 39], [20, 40], [4], [57, 10], [56, 58]]]
 h' := ![![[28, 58], [16, 43], [47, 14], [54, 57], [36, 52], [0, 1]], ![[0, 1], [40, 16], [26, 45], [57, 2], [17, 7], [28, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [34, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [24, 31, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![17361, -4046, 727]
  a := ![-1, 21, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![208, -697, 727]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![25, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![25, 1, 0]] 
 ![![59, 0, 0], ![25, 1, 0], ![19, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![25, 1, 0], ![-1, 26, 3], ![112, -35, 24]]]
  hmulB := by decide  
  f := ![![![-1116, 28391, 3276], ![59, -64428, 0]], ![![-487, 12011, 1386], ![60, -27258, 0]], ![![-356, 9143, 1055], ![11, -20748, 0]]]
  g := ![![![1, 0, 0], ![-25, 59, 0], ![-19, 0, 59]], ![![0, 1, 0], ![-12, 26, 3], ![9, -35, 24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![7, -8, 1]] ![![59, 0, 0], ![25, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![1475, 59, 0]], ![![413, -472, 59], ![295, -236, 0]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![25, 1, 0]]], ![![![7, -8, 1]], ![![5, -4, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0]] 
 ![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [58, 54, 26, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [51, 25, 28], [45, 35, 33], [0, 1]]
 g := ![![[17, 47, 34], [58, 4], [46, 51, 58], [23, 55, 5], [1]], ![[59, 32, 60, 53], [8, 12], [53, 18, 23, 31], [43, 33, 58, 44], [6, 13, 21, 53]], ![[47, 51, 18, 26], [28, 13], [24, 43, 32, 17], [31, 60, 48, 38], [46, 34, 6, 8]]]
 h' := ![![[51, 25, 28], [3, 37, 20], [16, 51, 59], [8, 30, 27], [3, 7, 35], [0, 1]], ![[45, 35, 33], [60, 33, 28], [55, 10, 16], [13, 46, 16], [55, 17, 18], [51, 25, 28]], ![[0, 1], [35, 52, 13], [16, 0, 47], [41, 46, 18], [7, 37, 8], [45, 35, 33]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 44], []]
 b := ![[], [21, 60, 42], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [58, 54, 26, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-727303, 302377, -72773]
  a := ![1, 1, -4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-11923, 4957, -1193]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 226981 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def PBC61 : ContainsPrimesAboveP 61 ![I61N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![61, 0, 0]]) timesTableT_eq_Table B_one_repr 61 (by decide) 𝕀

instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-269, 89, 3]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![-269, 89, 3]] 
 ![![67, 0, 0], ![0, 1, 0], ![22, 0, 1]] where
  M :=![![![-269, 89, 3], ![247, -285, 264], ![9779, -2968, -460]]]
  hmulB := by decide  
  f := ![![![-914652, -32036, -24351]], ![![-40228, -1409, -1071]], ![![-330989, -11593, -8812]]]
  g := ![![![-5, 89, 3], ![-83, -285, 264], ![297, -2968, -460]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N0 : Nat.card (O ⧸ I67N0) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N0)

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := prime_ideal_of_norm_prime hp67.out _ NI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![30, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![30, 1, 0]] 
 ![![67, 0, 0], ![30, 1, 0], ![47, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![30, 1, 0], ![-1, 31, 3], ![112, -35, 29]]]
  hmulB := by decide  
  f := ![![![1255, -38874, -3762], ![0, 84018, 0]], ![![561, -17391, -1683], ![1, 37587, 0]], ![![875, -27270, -2639], ![12, 58938, 0]]]
  g := ![![![1, 0, 0], ![-30, 67, 0], ![-47, 0, 67]], ![![0, 1, 0], ![-16, 31, 3], ![-3, -35, 29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1

def I67N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-30, 1, 0]] i)))

def SI67N2: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-30, 1, 0]] 
 ![![67, 0, 0], ![37, 1, 0], ![0, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-30, 1, 0], ![-1, -29, 3], ![112, -35, -31]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]], ![![15, 19, -2], ![32, 45, 0]]]
  g := ![![![1, 0, 0], ![-37, 67, 0], ![0, 0, 67]], ![![-1, 1, 0], ![16, -29, 3], ![21, -35, -31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N2 : Nat.card (O ⧸ I67N2) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N2)

lemma isPrimeI67N2 : Ideal.IsPrime I67N2 := prime_ideal_of_norm_prime hp67.out _ NI67N2
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![-269, 89, 3]] ![![67, 0, 0], ![30, 1, 0]]
  ![![67, 0, 0], ![22, -12, 1]] where
 M := ![![![-18023, 5963, 201], ![-7823, 2385, 354]]]
 hmul := by decide  
 g := ![![![![-247, 77, 4], ![-67, 0, 0]], ![![-123, 39, 5], ![19, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![22, -12, 1]] ![![67, 0, 0], ![-30, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-2010, 67, 0]], ![![1474, -804, 67], ![-536, 335, -67]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-30, 1, 0]]], ![![![22, -12, 1]], ![![-8, 5, -1]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1, I67N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
    exact isPrimeI67N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0 ⊙ MulI67N1)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![15, 29, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![15, 29, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![15, 29, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![15, 29, 1], ![83, 9, 86], ![3185, -966, -48]]]
  hmulB := by decide  
  f := ![![![-14, -29, -1], ![71, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-15, -29, 71]], ![![0, 0, 1], ![-17, -35, 86], ![55, 6, -48]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [30, 33, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 70], [0, 1]]
 g := ![![[65, 45], [49, 12], [64, 10], [6], [24], [1]], ![[0, 26], [8, 59], [18, 61], [6], [24], [1]]]
 h' := ![![[38, 70], [21, 20], [68, 56], [57, 62], [38, 52], [41, 38], [0, 1]], ![[0, 1], [0, 51], [66, 15], [70, 9], [26, 19], [65, 33], [38, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [7, 37]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [30, 33, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1723, 600, -1059]
  a := ![-2, 3, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![248, 441, -1059]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-15, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-15, 1, 0]] 
 ![![71, 0, 0], ![56, 1, 0], ![48, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-15, 1, 0], ![-1, -14, 3], ![112, -35, -16]]]
  hmulB := by decide  
  f := ![![![-2220, -31305, 6708], ![71, -158756, 0]], ![![-1747, -24683, 5289], ![72, -125173, 0]], ![![-1500, -21164, 4535], ![52, -107328, 0]]]
  g := ![![![1, 0, 0], ![-56, 71, 0], ![-48, 0, 71]], ![![-1, 1, 0], ![9, -14, 3], ![40, -35, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![15, 29, 1]] ![![71, 0, 0], ![-15, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-1065, 71, 0]], ![![1065, 2059, 71], ![-142, -426, 71]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-15, 1, 0]]], ![![![15, 29, 1]], ![![-2, -6, 1]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-2, -22, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-2, -22, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![71, 51, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-2, -22, 1], ![134, -59, -67], ![-2527, 819, -14]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-71, -51, 73]], ![![-1, -1, 1], ![67, 46, -67], ![-21, 21, -14]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [2, 60, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 72], [0, 1]]
 g := ![![[30, 37], [4], [48], [29, 54], [23], [1]], ![[0, 36], [4], [48], [1, 19], [23], [1]]]
 h' := ![![[13, 72], [62, 57], [56, 2], [15, 62], [31, 28], [71, 13], [0, 1]], ![[0, 1], [0, 16], [9, 71], [18, 11], [30, 45], [21, 60], [13, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [63]]
 b := ![[], [69, 68]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [2, 60, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4002, -800, -1125]
  a := ![0, -5, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1149, 775, -1125]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-6, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-6, 1, 0]] 
 ![![73, 0, 0], ![67, 1, 0], ![14, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-6, 1, 0], ![-1, -5, 3], ![112, -35, -7]]]
  hmulB := by decide  
  f := ![![![-245, -1261, 756], ![73, -18396, 0]], ![![-224, -1156, 693], ![74, -16863, 0]], ![![-46, -242, 145], ![26, -3528, 0]]]
  g := ![![![1, 0, 0], ![-67, 73, 0], ![-14, 0, 73]], ![![-1, 1, 0], ![4, -5, 3], ![35, -35, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-2, -22, 1]] ![![73, 0, 0], ![-6, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-438, 73, 0]], ![![-146, -1606, 73], ![146, 73, -73]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-6, 1, 0]]], ![![![-2, -22, 1]], ![![2, 1, -1]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![2, 1, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![2, 1, 0]] 
 ![![79, 0, 0], ![2, 1, 0], ![24, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![2, 1, 0], ![-1, 3, 3], ![112, -35, 1]]]
  hmulB := by decide  
  f := ![![![-2721, 8159, 8160], ![79, -214880, 0]], ![![-68, 204, 204], ![1, -5372, 0]], ![![-828, 2478, 2479], ![78, -65280, 0]]]
  g := ![![![1, 0, 0], ![-2, 79, 0], ![-24, 0, 79]], ![![0, 1, 0], ![-1, 3, 3], ![2, -35, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N0 : Nat.card (O ⧸ I79N0) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N0)

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := prime_ideal_of_norm_prime hp79.out _ NI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![33, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![33, 1, 0]] 
 ![![79, 0, 0], ![33, 1, 0], ![47, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![33, 1, 0], ![-1, 34, 3], ![112, -35, 32]]]
  hmulB := by decide  
  f := ![![![-836, 27335, 2412], ![79, -63516, 0]], ![![-368, 11389, 1005], ![80, -26465, 0]], ![![-484, 16263, 1435], ![15, -37788, 0]]]
  g := ![![![1, 0, 0], ![-33, 79, 0], ![-47, 0, 79]], ![![0, 1, 0], ![-16, 34, 3], ![-3, -35, 32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1

def I79N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-164, 125, -91]] i)))

def SI79N2: IdealEqSpanCertificate' Table ![![-164, 125, -91]] 
 ![![79, 0, 0], ![44, 1, 0], ![77, 0, 1]] where
  M :=![![![-164, 125, -91], ![-10317, 3146, 466], ![19733, -8834, 2805]]]
  hmulB := by decide  
  f := ![![![12941174, 453269, 344536]], ![![7690461, 269361, 204745]], ![![12981402, 454678, 345607]]]
  g := ![![![17, 125, -91], ![-2337, 3146, 466], ![2436, -8834, 2805]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N2 : Nat.card (O ⧸ I79N2) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N2)

lemma isPrimeI79N2 : Ideal.IsPrime I79N2 := prime_ideal_of_norm_prime hp79.out _ NI79N2
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![2, 1, 0]] ![![79, 0, 0], ![33, 1, 0]]
  ![![-12941174, -453269, -344536]] where
 M := ![![![6241, 0, 0], ![2607, 79, 0]], ![![158, 79, 0], ![65, 36, 3]]]
 hmul := by decide  
 g := ![![![![12956, -9875, 7189]], ![![15729, -7271, 2537]]], ![![![10645, -3396, -284]], ![![4087, -1201, -244]]]]
 hle2 := by decide  

def MulI79N1 : IdealMulLeCertificate' Table 
  ![![-12941174, -453269, -344536]] ![![-164, 125, -91]]
  ![![79, 0, 0]] where
 M := ![![![-79, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1, I79N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
    exact isPrimeI79N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0 ⊙ MulI79N1)


lemma PB262I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB262I1 : PrimesBelowBoundCertificateInterval O 31 79 262 where
  m := 11
  g := ![1, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB262I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0, I41N1]
    · exact ![I43N0]
    · exact ![I47N0]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0]
    · exact ![I67N0, I67N1, I67N2]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1]
    · exact ![I79N0, I79N1, I79N2]
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
    · exact ![50653]
    · exact ![1681, 41]
    · exact ![79507]
    · exact ![103823]
    · exact ![2809, 53]
    · exact ![3481, 59]
    · exact ![226981]
    · exact ![67, 67, 67]
    · exact ![5041, 71]
    · exact ![5329, 73]
    · exact ![79, 79, 79]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
      exact NI67N2
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
      exact NI79N2
  β := ![I41N1, I53N1, I59N1, I67N0, I67N1, I67N2, I71N1, I73N1, I79N0, I79N1, I79N2]
  Il := ![[], [I41N1], [], [], [I53N1], [I59N1], [], [I67N0, I67N1, I67N2], [I71N1], [I73N1], [I79N0, I79N1, I79N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
