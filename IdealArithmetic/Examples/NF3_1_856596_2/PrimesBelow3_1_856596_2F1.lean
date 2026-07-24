
import IdealArithmetic.Examples.NF3_1_856596_2.RI3_1_856596_2
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [27, 30, 14, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [32, 36, 35], [28, 0, 2], [0, 1]]
 g := ![![[18, 25, 27], [9, 33], [15, 29, 28], [23, 1], []], ![[30, 36, 26, 18], [2, 12], [29, 33, 18, 23], [], [22, 4]], ![[28, 27, 0, 15], [21, 28], [14, 18, 17, 14], [24, 1], [18, 4]]]
 h' := ![![[32, 36, 35], [20, 9, 8], [2, 15, 12], [8, 23, 18], [0, 0, 1], [0, 1]], ![[28, 0, 2], [11, 32, 19], [18, 28, 7], [11, 23, 28], [23, 19], [32, 36, 35]], ![[0, 1], [29, 33, 10], [2, 31, 18], [22, 28, 28], [2, 18, 36], [28, 0, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27, 2], []]
 b := ![[], [5, 8, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [27, 30, 14, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-605616, -24198, -11766]
  a := ![-3, -2, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-16368, -654, -318]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-8, 19, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-8, 19, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![33, 19, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-8, 19, 1], ![291, 52, 225], ![3276, 71, -61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-33, -19, 41]], ![![-1, 0, 1], ![-174, -103, 225], ![129, 30, -61]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [38, 25, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 40], [0, 1]]
 g := ![![[19, 16], [39], [36], [10, 10], [1]], ![[29, 25], [39], [36], [6, 31], [1]]]
 h' := ![![[16, 40], [37, 4], [24, 11], [30, 35], [3, 16], [0, 1]], ![[0, 1], [19, 37], [36, 30], [16, 6], [13, 25], [16, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [38, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [38, 25, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2083, 350, 245]
  a := ![2, 0, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-248, -105, 245]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-20, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-20, 1, 0]] 
 ![![41, 0, 0], ![21, 1, 0], ![20, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-20, 1, 0], ![6, -17, 12], ![177, 3, -23]]]
  hmulB := by decide  
  f := ![![![-143, 575, -408], ![123, 1394, 0]], ![![-61, 287, -204], ![83, 697, 0]], ![![-60, 280, -199], ![80, 680, 0]]]
  g := ![![![1, 0, 0], ![-21, 41, 0], ![-20, 0, 41]], ![![-1, 1, 0], ![3, -17, 12], ![14, 3, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-8, 19, 1]] ![![41, 0, 0], ![-20, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-820, 41, 0]], ![![-328, 779, 41], ![451, -328, 205]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-20, 1, 0]]], ![![![-8, 19, 1]], ![![11, -8, 5]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-7, 4, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-7, 4, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![36, 4, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-7, 4, 1], ![201, 8, 45], ![621, 26, -15]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-36, -4, 43]], ![![-1, 0, 1], ![-33, -4, 45], ![27, 2, -15]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [37, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 42], [0, 1]]
 g := ![![[41, 6], [35, 9], [10], [20, 15], [1]], ![[12, 37], [13, 34], [10], [12, 28], [1]]]
 h' := ![![[31, 42], [38, 36], [12, 40], [34, 15], [6, 31], [0, 1]], ![[0, 1], [36, 7], [5, 3], [26, 28], [21, 12], [31, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [3, 22]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [37, 12, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1160638, 629432, 172924]
  a := ![-129, -64, -194]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-117782, -1448, 172924]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-2, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-2, 1, 0]] 
 ![![43, 0, 0], ![41, 1, 0], ![15, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-2, 1, 0], ![6, 1, 12], ![177, 3, -5]]]
  hmulB := by decide  
  f := ![![![1385, 232, 2772], ![-43, -9933, 0]], ![![1319, 221, 2640], ![-42, -9460, 0]], ![![483, 81, 967], ![-18, -3465, 0]]]
  g := ![![![1, 0, 0], ![-41, 43, 0], ![-15, 0, 43]], ![![-1, 1, 0], ![-5, 1, 12], ![3, 3, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-7, 4, 1]] ![![43, 0, 0], ![-2, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-86, 43, 0]], ![![-301, 172, 43], ![215, 0, 43]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-2, 1, 0]]], ![![![-7, 4, 1]], ![![5, 0, 1]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-15, 19, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-15, 19, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![32, 19, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-15, 19, 1], ![291, 45, 225], ![3276, 71, -68]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-32, -19, 47]], ![![-1, 0, 1], ![-147, -90, 225], ![116, 29, -68]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [20, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 46], [0, 1]]
 g := ![![[20, 4], [32, 9], [23, 3], [14, 12], [1]], ![[18, 43], [4, 38], [45, 44], [8, 35], [1]]]
 h' := ![![[23, 46], [18, 45], [10, 3], [2, 12], [27, 23], [0, 1]], ![[0, 1], [19, 2], [32, 44], [43, 35], [39, 24], [23, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36]]
 b := ![[], [28, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [20, 24, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1822, 713, 40]
  a := ![-3, -1, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-66, -1, 40]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![10, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![10, 1, 0]] 
 ![![47, 0, 0], ![10, 1, 0], ![21, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![10, 1, 0], ![6, 13, 12], ![177, 3, 7]]]
  hmulB := by decide  
  f := ![![![2999, 6847, 6336], ![799, -24816, 0]], ![![632, 1452, 1344], ![189, -5264, 0]], ![![1337, 3059, 2831], ![371, -11088, 0]]]
  g := ![![![1, 0, 0], ![-10, 47, 0], ![-21, 0, 47]], ![![0, 1, 0], ![-8, 13, 12], ![0, 3, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![-15, 19, 1]] ![![47, 0, 0], ![10, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![470, 47, 0]], ![![-705, 893, 47], ![141, 235, 235]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![10, 1, 0]]], ![![![-15, 19, 1]], ![![3, 5, 5]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0]] 
 ![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [29, 38, 51, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [48, 36, 28], [7, 16, 25], [0, 1]]
 g := ![![[2, 24, 11], [49, 43], [46, 37, 10], [15, 4], [1]], ![[7, 2, 21, 28], [34, 25], [3, 47, 19, 6], [29, 42], [27, 48, 51, 10]], ![[36, 49, 38, 6], [43, 37], [37, 20, 7, 4], [10, 52], [23, 21, 35, 43]]]
 h' := ![![[48, 36, 28], [38, 20, 8], [44, 47, 34], [35, 34, 40], [24, 15, 2], [0, 1]], ![[7, 16, 25], [8, 6, 52], [27, 9, 5], [3, 39, 2], [46, 17, 28], [48, 36, 28]], ![[0, 1], [9, 27, 46], [39, 50, 14], [11, 33, 11], [47, 21, 23], [7, 16, 25]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19, 22], []]
 b := ![[], [4, 35, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [29, 38, 51, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-563125, -2014, -6042]
  a := ![-3, -2, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10625, -38, -114]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 148877 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def PBC53 : ContainsPrimesAboveP 53 ![I53N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![53, 0, 0]]) timesTableT_eq_Table B_one_repr 53 (by decide) 𝕀

instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-292290575933366565535, -32074477638488116392, -22370707828329673012]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-292290575933366565535, -32074477638488116392, -22370707828329673012]] 
 ![![59, 0, 0], ![30, 1, 0], ![36, 0, 1]] where
  M :=![![![-292290575933366565535, -32074477638488116392, -22370707828329673012], ![-4152062151445280821476, -455626132333819933747, -317781608176868377668], ![-3730930960947715049340, -409413342512079771344, -285549974331220908407]]]
  hmulB := by decide  
  f := ![![![167780634763, -2660460584, -10183597892]], ![![54490838178, 837875285, -5201401188]], ![![109409734656, -4175056496, -3925116935]]]
  g := ![![![25004902288832968723, -32074477638488116392, -22370707828329673012], ![355201012083670826898, -455626132333819933747, -317781608176868377668], ![319174040514214081248, -409413342512079771344, -285549974331220908407]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N0 : Nat.card (O ⧸ I59N0) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N0)

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := prime_ideal_of_norm_prime hp59.out _ NI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-20, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-20, 1, 0]] 
 ![![59, 0, 0], ![39, 1, 0], ![41, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-20, 1, 0], ![6, -17, 12], ![177, 3, -23]]]
  hmulB := by decide  
  f := ![![![317, -951, 672], ![-59, -3304, 0]], ![![203, -628, 444], ![-58, -2183, 0]], ![![223, -661, 467], ![-33, -2296, 0]]]
  g := ![![![1, 0, 0], ![-39, 59, 0], ![-41, 0, 59]], ![![-1, 1, 0], ![3, -17, 12], ![17, 3, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-10, 1, 0]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-10, 1, 0]] 
 ![![59, 0, 0], ![49, 1, 0], ![34, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-10, 1, 0], ![6, -7, 12], ![177, 3, -13]]]
  hmulB := by decide  
  f := ![![![17567, -21091, 36252], ![-3304, -178239, 0]], ![![14589, -17510, 30096], ![-2713, -147972, 0]], ![![10122, -12154, 20891], ![-1912, -102714, 0]]]
  g := ![![![1, 0, 0], ![-49, 59, 0], ![-34, 0, 59]], ![![-1, 1, 0], ![-1, -7, 12], ![8, 3, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-292290575933366565535, -32074477638488116392, -22370707828329673012]] ![![59, 0, 0], ![-20, 1, 0]]
  ![![59, 0, 0], ![-20, 6, 1]] where
 M := ![![![-17245143980068627366565, -1892394180670798867128, -1319871761871450707708], ![1693749367222050489224, 185863420435942394093, 129632548389725082572]]]
 hmul := by decide  
 g := ![![![![-263546349567832757775, -40697745548148258720, -23807919146606363400], ![84795467778324732892, 0, 0]], ![![25884472946709585536, 3997170499081319947, 2338319009458208978], ![-8328273168309247130, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-20, 6, 1]] ![![59, 0, 0], ![-10, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-590, 59, 0]], ![![-1180, 354, 59], ![413, -59, 59]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-10, 1, 0]]], ![![![-20, 6, 1]], ![![7, -1, 1]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1, I59N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
    exact isPrimeI59N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0 ⊙ MulI59N1)
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


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [2, 47, 43, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [50, 13], [29, 47], [0, 1]]
 g := ![![[36, 4, 12], [36, 34], [46, 20, 47], [2, 53, 19], [1]], ![[41, 36, 15], [28, 15], [23, 55, 13], [10, 13, 39], [1]], ![[57, 21, 34], [46, 12], [15, 47, 1], [11, 56, 3], [1]]]
 h' := ![![[50, 13], [35, 60, 45], [30, 10, 20], [57, 48, 13], [59, 14, 18], [0, 1]], ![[29, 47], [1, 49, 41], [22, 22, 25], [4, 17, 1], [9, 36, 53], [50, 13]], ![[0, 1], [31, 13, 36], [60, 29, 16], [60, 57, 47], [48, 11, 51], [29, 47]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7], []]
 b := ![[], [40, 7, 35], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [2, 47, 43, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![302499366, 19764549, 13311054]
  a := ![23, 21, 45]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4959006, 324009, 218214]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![3, 33, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![3, 33, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![3, 33, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![3, 33, 1], ![375, 105, 393], ![5754, 113, -92]]]
  hmulB := by decide  
  f := ![![![-2, -33, -1], ![67, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-3, -33, 67]], ![![0, 0, 1], ![-12, -192, 393], ![90, 47, -92]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [54, 25, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [42, 66], [0, 1]]
 g := ![![[29, 36], [27, 39], [16], [36], [22], [1]], ![[0, 31], [57, 28], [16], [36], [22], [1]]]
 h' := ![![[42, 66], [16, 6], [43, 21], [61, 4], [53, 6], [13, 42], [0, 1]], ![[0, 1], [0, 61], [54, 46], [28, 63], [37, 61], [35, 25], [42, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [6, 38]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [54, 25, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-405, 34, -1]
  a := ![-1, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-6, 1, -1]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![9, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![9, 1, 0]] 
 ![![67, 0, 0], ![9, 1, 0], ![25, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![9, 1, 0], ![6, 12, 12], ![177, 3, 6]]]
  hmulB := by decide  
  f := ![![![523, 1078, 1080], ![134, -6030, 0]], ![![63, 143, 144], ![68, -804, 0]], ![![193, 402, 403], ![66, -2250, 0]]]
  g := ![![![1, 0, 0], ![-9, 67, 0], ![-25, 0, 67]], ![![0, 1, 0], ![-6, 12, 12], ![0, 3, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![3, 33, 1]] ![![67, 0, 0], ![9, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![603, 67, 0]], ![![201, 2211, 67], ![402, 402, 402]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![9, 1, 0]]], ![![![3, 33, 1]], ![![6, 6, 6]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![27, 1, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![27, 1, 0]] 
 ![![71, 0, 0], ![27, 1, 0], ![4, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![27, 1, 0], ![6, 30, 12], ![177, 3, 24]]]
  hmulB := by decide  
  f := ![![![16831, 98890, 39600], ![7810, -234300, 0]], ![![6390, 37578, 15048], ![2983, -89034, 0]], ![![941, 5571, 2231], ![459, -13200, 0]]]
  g := ![![![1, 0, 0], ![-27, 71, 0], ![-4, 0, 71]], ![![0, 1, 0], ![-12, 30, 12], ![0, 3, 24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N0 : Nat.card (O ⧸ I71N0) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N0)

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := prime_ideal_of_norm_prime hp71.out _ NI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-22, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-22, 1, 0]] 
 ![![71, 0, 0], ![49, 1, 0], ![13, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-22, 1, 0], ![6, -19, 12], ![177, 3, -25]]]
  hmulB := by decide  
  f := ![![![5019, -17607, 11136], ![-1775, -65888, 0]], ![![3467, -12143, 7680], ![-1206, -45440, 0]], ![![923, -3224, 2039], ![-312, -12064, 0]]]
  g := ![![![1, 0, 0], ![-49, 71, 0], ![-13, 0, 71]], ![![-1, 1, 0], ![11, -19, 12], ![5, 3, -25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-112, -2, 11]] i)))

def SI71N2: IdealEqSpanCertificate' Table ![![-112, -2, 11]] 
 ![![71, 0, 0], ![66, 1, 0], ![47, 0, 1]] where
  M :=![![![-112, -2, 11], ![1935, -85, -57], ![-1311, 148, -62]]]
  hmulB := by decide  
  f := ![![![-13706, -1504, -1049]], ![![-15483, -1699, -1185]], ![![-11537, -1266, -883]]]
  g := ![![![-7, -2, 11], ![144, -85, -57], ![-115, 148, -62]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![27, 1, 0]] ![![71, 0, 0], ![-22, 1, 0]]
  ![![13706, 1504, 1049]] where
 M := ![![![5041, 0, 0], ![-1562, 71, 0]], ![![1917, 71, 0], ![-588, 8, 12]]]
 hmul := by decide  
 g := ![![![![7952, 142, -781]], ![![-4399, 41, 299]]], ![![![1089, 139, -240]], ![![-924, -32, 108]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![13706, 1504, 1049]] ![![-112, -2, 11]]
  ![![71, 0, 0]] where
 M := ![![![-71, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1, I71N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
    exact isPrimeI71N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0 ⊙ MulI71N1)
instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-23, -33, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-23, -33, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![50, 40, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-23, -33, 1], ![-21, -119, -399], ![-5928, -85, 80]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-50, -40, 73]], ![![-1, -1, 1], ![273, 217, -399], ![-136, -45, 80]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [23, 34, 1] where
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
 g := ![![[11, 54], [54], [3], [43, 1], [61], [1]], ![[0, 19], [54], [3], [9, 72], [61], [1]]]
 h' := ![![[39, 72], [3, 28], [71, 45], [33, 52], [2, 1], [50, 39], [0, 1]], ![[0, 1], [0, 45], [1, 28], [17, 21], [41, 72], [38, 34], [39, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59]]
 b := ![[], [27, 66]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [23, 34, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2192, 1739, 768]
  a := ![5, 3, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-496, -397, 768]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![34, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![34, 1, 0]] 
 ![![73, 0, 0], ![34, 1, 0], ![66, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![34, 1, 0], ![6, 37, 12], ![177, 3, 31]]]
  hmulB := by decide  
  f := ![![![6305, 49308, 16008], ![3650, -97382, 0]], ![![2910, 22953, 7452], ![1753, -45333, 0]], ![![5706, 44580, 14473], ![3288, -88044, 0]]]
  g := ![![![1, 0, 0], ![-34, 73, 0], ![-66, 0, 73]], ![![0, 1, 0], ![-28, 37, 12], ![-27, 3, 31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-23, -33, 1]] ![![73, 0, 0], ![34, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![2482, 73, 0]], ![![-1679, -2409, 73], ![-803, -1241, -365]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![34, 1, 0]]], ![![![-23, -33, 1]], ![![-11, -17, -5]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0]] 
 ![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [34, 51, 56, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 3, 45], [18, 75, 34], [0, 1]]
 g := ![![[44, 51, 2], [27, 58, 2], [6, 8, 73], [40, 34, 16], [23, 1], []], ![[38, 61, 35, 65], [69, 58, 9, 40], [55, 62, 65, 64], [66, 54, 61, 16], [35, 16], [77, 50]], ![[71, 0, 37, 78], [78, 37, 32, 69], [55, 42, 9, 68], [15, 72, 24, 78], [56, 9], [9, 50]]]
 h' := ![![[5, 3, 45], [30, 31, 9], [33, 27, 9], [62, 28, 28], [8, 57, 4], [0, 0, 1], [0, 1]], ![[18, 75, 34], [74, 43, 16], [57, 31, 73], [41, 25, 42], [33, 61, 21], [14, 12, 75], [5, 3, 45]], ![[0, 1], [39, 5, 54], [49, 21, 76], [43, 26, 9], [0, 40, 54], [18, 67, 3], [18, 75, 34]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 34], []]
 b := ![[], [9, 47, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [34, 51, 56, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9363001, -325480, -164715]
  a := ![-10, -5, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-118519, -4120, -2085]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 493039 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def PBC79 : ContainsPrimesAboveP 79 ![I79N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![79, 0, 0]]) timesTableT_eq_Table B_one_repr 79 (by decide) 𝕀



lemma PB262I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB262I1 : PrimesBelowBoundCertificateInterval O 31 79 262 where
  m := 11
  g := ![1, 2, 2, 2, 1, 3, 1, 2, 3, 2, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB262I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0]
    · exact ![I59N0, I59N1, I59N2]
    · exact ![I61N0]
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1, I71N2]
    · exact ![I73N0, I73N1]
    · exact ![I79N0]
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
    · exact ![1849, 43]
    · exact ![2209, 47]
    · exact ![148877]
    · exact ![59, 59, 59]
    · exact ![226981]
    · exact ![4489, 67]
    · exact ![71, 71, 71]
    · exact ![5329, 73]
    · exact ![493039]
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
      exact NI43N1
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
      exact NI59N2
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
      exact NI71N2
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
  β := ![I41N1, I43N1, I47N1, I59N0, I59N1, I59N2, I67N1, I71N0, I71N1, I71N2, I73N1]
  Il := ![[], [I41N1], [I43N1], [I47N1], [], [I59N0, I59N1, I59N2], [], [I67N1], [I71N0, I71N1, I71N2], [I73N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
