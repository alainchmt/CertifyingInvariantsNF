
import IdealArithmetic.Examples.NF3_1_456435_2.RI3_1_456435_2
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [27, 11, 34, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [35, 28, 20], [5, 8, 17], [0, 1]]
 g := ![![[22, 2, 33], [24, 7], [11, 30, 4], [3, 1], []], ![[2, 30, 15, 29], [5, 10], [7, 24, 31, 19], [30, 27], [26, 30]], ![[19, 24, 20, 23], [18, 4], [10, 18, 34, 5], [33, 7], [29, 30]]]
 h' := ![![[35, 28, 20], [19, 16, 12], [36, 6, 28], [30, 14, 35], [0, 0, 1], [0, 1]], ![[5, 8, 17], [10, 12, 9], [16, 14, 11], [29, 33, 5], [5, 13, 8], [35, 28, 20]], ![[0, 1], [31, 9, 16], [6, 17, 35], [25, 27, 34], [19, 24, 28], [5, 8, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17, 4], []]
 b := ![[], [7, 20, 22], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [27, 11, 34, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5926623, -1406074, -528508]
  a := ![-3, -5, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-160179, -38002, -14284]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0]] 
 ![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [22, 11, 39, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [26, 38, 13], [17, 2, 28], [0, 1]]
 g := ![![[10, 3, 16], [37, 40], [30, 2], [34, 2, 1], []], ![[8, 40, 39, 22], [22, 21], [1, 20], [1, 3, 23, 11], [14, 5]], ![[5, 20, 5, 26], [36, 31], [25, 40], [23, 27, 31, 6], [40, 5]]]
 h' := ![![[26, 38, 13], [38, 19, 37], [14, 32, 32], [31, 33, 24], [0, 0, 1], [0, 1]], ![[17, 2, 28], [3, 24, 34], [35, 35, 29], [4, 30, 26], [40, 31, 2], [26, 38, 13]], ![[0, 1], [19, 39, 11], [14, 15, 21], [20, 19, 32], [24, 10, 38], [17, 2, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 35], []]
 b := ![[], [35, 24, 32], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [22, 11, 39, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1168377, 556411, 259038]
  a := ![2, 2, 9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![28497, 13571, 6318]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0]] 
 ![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [9, 42, 18, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 37, 5], [37, 5, 38], [0, 1]]
 g := ![![[30, 40, 13], [41, 9, 38], [3, 24], [24, 25, 1], []], ![[3, 27, 6, 33], [28, 15, 3, 5], [7, 35], [39, 31, 42, 39], [6, 25]], ![[18, 22, 6, 13], [9, 15, 16, 16], [2, 23], [22, 1, 8, 35], [16, 25]]]
 h' := ![![[31, 37, 5], [18, 34, 23], [17, 17, 9], [42, 14, 14], [0, 0, 1], [0, 1]], ![[37, 5, 38], [3, 6, 27], [21, 40, 1], [16, 27, 11], [4, 11, 5], [31, 37, 5]], ![[0, 1], [39, 3, 36], [18, 29, 33], [37, 2, 18], [21, 32, 37], [37, 5, 38]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26, 18], []]
 b := ![[], [23, 23, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [9, 42, 18, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-329763249540, -83800931883, -33645837792]
  a := ![-129, -193, -452]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-7668912780, -1948858881, -782461344]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-20, -9, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-20, -9, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![27, 38, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-20, -9, 1], ![137, -30, -75], ![-1507, -140, 26]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-27, -38, 47]], ![![-1, -1, 1], ![46, 60, -75], ![-47, -24, 26]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [16, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 46], [0, 1]]
 g := ![![[39, 3], [45, 36], [1, 14], [5, 28], [1]], ![[0, 44], [0, 11], [7, 33], [17, 19], [1]]]
 h' := ![![[34, 46], [32, 35], [31, 6], [14, 25], [31, 34], [0, 1]], ![[0, 1], [0, 12], [0, 41], [18, 22], [12, 13], [34, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [33, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [16, 13, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2790, 3985, 2936]
  a := ![-3, -4, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1746, -2289, 2936]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-19, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-19, 1, 0]] 
 ![![47, 0, 0], ![28, 1, 0], ![21, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-19, 1, 0], ![2, -16, 8], ![155, 17, -22]]]
  hmulB := by decide  
  f := ![![![2631, -26174, 13104], ![-1598, -76986, 0]], ![![1571, -15580, 7800], ![-939, -45825, 0]], ![![1180, -11695, 5855], ![-703, -34398, 0]]]
  g := ![![![1, 0, 0], ![-28, 47, 0], ![-21, 0, 47]], ![![-1, 1, 0], ![6, -16, 8], ![3, 17, -22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![-20, -9, 1]] ![![47, 0, 0], ![-19, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![-893, 47, 0]], ![![-940, -423, 47], ![517, 141, -94]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![-19, 1, 0]]], ![![![-20, -9, 1]], ![![11, 3, -2]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![5, 1, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![5, 1, 0]] 
 ![![53, 0, 0], ![5, 1, 0], ![35, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![5, 1, 0], ![2, 8, 8], ![155, 17, 2]]]
  hmulB := by decide  
  f := ![![![2201, 8952, 8960], ![424, -59360, 0]], ![![205, 839, 840], ![54, -5565, 0]], ![![1455, 5912, 5917], ![264, -39200, 0]]]
  g := ![![![1, 0, 0], ![-5, 53, 0], ![-35, 0, 53]], ![![0, 1, 0], ![-6, 8, 8], ![0, 17, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N0 : Nat.card (O ⧸ I53N0) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N0)

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := prime_ideal_of_norm_prime hp53.out _ NI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![21, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![21, 1, 0]] 
 ![![53, 0, 0], ![21, 1, 0], ![30, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![21, 1, 0], ![2, 24, 8], ![155, 17, 18]]]
  hmulB := by decide  
  f := ![![![2926, 44889, 14976], ![2067, -99216, 0]], ![![1146, 17768, 5928], ![849, -39273, 0]], ![![1659, 25409, 8477], ![1163, -56160, 0]]]
  g := ![![![1, 0, 0], ![-21, 53, 0], ![-30, 0, 53]], ![![0, 1, 0], ![-14, 24, 8], ![-14, 17, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1

def I53N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-26, 1, 0]] i)))

def SI53N2: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-26, 1, 0]] 
 ![![53, 0, 0], ![27, 1, 0], ![5, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-26, 1, 0], ![2, -23, 8], ![155, 17, -29]]]
  hmulB := by decide  
  f := ![![![19, 91, -32], ![53, 212, 0]], ![![23, 45, -16], ![54, 106, 0]], ![![17, 8, -3], ![36, 20, 0]]]
  g := ![![![1, 0, 0], ![-27, 53, 0], ![-5, 0, 53]], ![![-1, 1, 0], ![11, -23, 8], ![-3, 17, -29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N2 : Nat.card (O ⧸ I53N2) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N2)

lemma isPrimeI53N2 : Ideal.IsPrime I53N2 := prime_ideal_of_norm_prime hp53.out _ NI53N2
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![5, 1, 0]] ![![53, 0, 0], ![21, 1, 0]]
  ![![53, 0, 0], ![-33, -3, 1]] where
 M := ![![![2809, 0, 0], ![1113, 53, 0]], ![![265, 53, 0], ![107, 29, 8]]]
 hmul := by decide  
 g := ![![![![53, 0, 0], ![0, 0, 0]], ![![21, 1, 0], ![0, 0, 0]]], ![![![5, 1, 0], ![0, 0, 0]], ![![7, 1, 0], ![8, 0, 0]]]]
 hle2 := by decide  

def MulI53N1 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![-33, -3, 1]] ![![53, 0, 0], ![-26, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-1378, 53, 0]], ![![-1749, -159, 53], ![1007, 53, -53]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-26, 1, 0]]], ![![![-33, -3, 1]], ![![19, 1, -1]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1, I53N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
    exact isPrimeI53N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0 ⊙ MulI53N1)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-29, 1, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-29, 1, 0]] 
 ![![59, 0, 0], ![30, 1, 0], ![24, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-29, 1, 0], ![2, -26, 8], ![155, 17, -32]]]
  hmulB := by decide  
  f := ![![![22, 103, -32], ![59, 236, 0]], ![![26, 51, -16], ![60, 118, 0]], ![![6, 42, -13], ![18, 96, 0]]]
  g := ![![![1, 0, 0], ![-30, 59, 0], ![-24, 0, 59]], ![![-1, 1, 0], ![10, -26, 8], ![7, 17, -32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N0 : Nat.card (O ⧸ I59N0) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N0)

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := prime_ideal_of_norm_prime hp59.out _ NI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-26, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-26, 1, 0]] 
 ![![59, 0, 0], ![33, 1, 0], ![14, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-26, 1, 0], ![2, -23, 8], ![155, 17, -29]]]
  hmulB := by decide  
  f := ![![![1835, -27349, 9520], ![-1239, -70210, 0]], ![![1019, -15283, 5320], ![-707, -39235, 0]], ![![446, -6490, 2259], ![-270, -16660, 0]]]
  g := ![![![1, 0, 0], ![-33, 59, 0], ![-14, 0, 59]], ![![-1, 1, 0], ![11, -23, 8], ![0, 17, -29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-4, 1, 0]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-4, 1, 0]] 
 ![![59, 0, 0], ![55, 1, 0], ![44, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-4, 1, 0], ![2, -1, 8], ![155, 17, -7]]]
  hmulB := by decide  
  f := ![![![4993, -2502, 20064], ![-354, -147972, 0]], ![![4651, -2331, 18696], ![-353, -137883, 0]], ![![3724, -1866, 14963], ![-258, -110352, 0]]]
  g := ![![![1, 0, 0], ![-55, 59, 0], ![-44, 0, 59]], ![![-1, 1, 0], ![-5, -1, 8], ![-8, 17, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-29, 1, 0]] ![![59, 0, 0], ![-26, 1, 0]]
  ![![59, 0, 0], ![6, 23, 1]] where
 M := ![![![3481, 0, 0], ![-1534, 59, 0]], ![![-1711, 59, 0], ![756, -52, 8]]]
 hmul := by decide  
 g := ![![![![53, -23, -1], ![59, 0, 0]], ![![-26, 1, 0], ![0, 0, 0]]], ![![![-29, 1, 0], ![0, 0, 0]], ![![12, -4, 0], ![8, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![6, 23, 1]] ![![59, 0, 0], ![-4, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-236, 59, 0]], ![![354, 1357, 59], ![177, 0, 177]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-4, 1, 0]]], ![![![6, 23, 1]], ![![3, 0, 3]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![18, -17, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![18, -17, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![18, 44, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![18, -17, 1], ![121, -16, -139], ![-2747, -276, 88]]]
  hmulB := by decide  
  f := ![![![-17, 17, -1], ![61, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-18, -44, 61]], ![![0, -1, 1], ![43, 100, -139], ![-71, -68, 88]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [1, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [45, 60], [0, 1]]
 g := ![![[16, 1], [13], [34, 56], [2, 60], [45, 1]], ![[0, 60], [13], [53, 5], [18, 1], [29, 60]]]
 h' := ![![[45, 60], [45, 60], [27, 14], [59, 42], [16, 11], [0, 1]], ![[0, 1], [0, 1], [47, 47], [58, 19], [23, 50], [45, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [59, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [1, 16, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2484, 3937, 2456]
  a := ![-3, -5, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-684, -1707, 2456]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![17, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![17, 1, 0]] 
 ![![61, 0, 0], ![17, 1, 0], ![34, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![17, 1, 0], ![2, 20, 8], ![155, 17, 14]]]
  hmulB := by decide  
  f := ![![![-1341, -15110, -6048], ![-610, 46116, 0]], ![![-386, -4198, -1680], ![-121, 12810, 0]], ![![-748, -8422, -3371], ![-338, 25704, 0]]]
  g := ![![![1, 0, 0], ![-17, 61, 0], ![-34, 0, 61]], ![![0, 1, 0], ![-10, 20, 8], ![-10, 17, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![18, -17, 1]] ![![61, 0, 0], ![17, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![1037, 61, 0]], ![![1098, -1037, 61], ![427, -305, -122]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![17, 1, 0]]], ![![![18, -17, 1]], ![![7, -5, -2]]]]
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


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [65, 32, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [35, 19, 21], [27, 47, 46], [0, 1]]
 g := ![![[51, 14, 37], [11, 4, 15], [47, 25], [33, 49], [62, 1], []], ![[29, 48, 45, 39], [33, 21, 52, 29], [16, 65], [61, 14], [37, 65], [0, 39]], ![[43, 42, 7, 58], [64, 2, 16, 63], [54, 22], [52, 55], [33, 26], [42, 39]]]
 h' := ![![[35, 19, 21], [22, 30, 29], [46, 18, 45], [32, 23, 62], [57, 28, 60], [0, 0, 1], [0, 1]], ![[27, 47, 46], [15, 63, 50], [57, 52, 14], [5, 30, 47], [33, 56, 58], [19, 1, 47], [35, 19, 21]], ![[0, 1], [21, 41, 55], [66, 64, 8], [5, 14, 25], [13, 50, 16], [9, 66, 19], [27, 47, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 1], []]
 b := ![[], [2, 23, 51], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [65, 32, 5, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3064287478, 738939650, 297441475]
  a := ![23, 44, 91]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![45735634, 11028950, 4439425]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0]] 
 ![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [67, 12, 40, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 3, 57], [10, 67, 14], [0, 1]]
 g := ![![[23, 42, 37], [31, 26, 48], [70, 8, 60], [45, 37], [31, 1], []], ![[68, 70, 63, 37], [3, 0, 66, 54], [24, 29, 27, 54], [33, 49], [22, 16], [28, 54]], ![[46, 24, 27, 59], [21, 17, 58, 66], [27, 9, 59, 70], [11, 24], [30, 9], [0, 54]]]
 h' := ![![[21, 3, 57], [53, 32, 26], [67, 22, 41], [7, 5, 42], [53, 58, 26], [0, 0, 1], [0, 1]], ![[10, 67, 14], [51, 39, 16], [56, 28, 25], [50, 54, 46], [29, 46, 7], [56, 6, 67], [21, 3, 57]], ![[0, 1], [62, 0, 29], [56, 21, 5], [68, 12, 54], [38, 38, 38], [29, 65, 3], [10, 67, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23, 24], []]
 b := ![[], [45, 48, 22], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [67, 12, 40, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-34151, -8307, 852]
  a := ![-1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-481, -117, 12]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 357911 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def PBC71 : ContainsPrimesAboveP 71 ![I71N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![71, 0, 0]]) timesTableT_eq_Table B_one_repr 71 (by decide) 𝕀

instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![18, -34, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![18, -34, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![18, 39, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![18, -34, 1], ![87, -67, -275], ![-5382, -565, 139]]]
  hmulB := by decide  
  f := ![![![-17, 34, -1], ![73, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-18, -39, 73]], ![![0, -1, 1], ![69, 146, -275], ![-108, -82, 139]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [38, 69, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 72], [0, 1]]
 g := ![![[46, 25], [46], [25], [13, 3], [16], [1]], ![[0, 48], [46], [25], [25, 70], [16], [1]]]
 h' := ![![[4, 72], [20, 68], [69, 51], [17, 5], [33, 52], [35, 4], [0, 1]], ![[0, 1], [0, 5], [54, 22], [37, 68], [22, 21], [51, 69], [4, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58]]
 b := ![[], [15, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [38, 69, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5336, 11464, 8732]
  a := ![5, 8, 20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2080, -4508, 8732]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-17, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-17, 1, 0]] 
 ![![73, 0, 0], ![56, 1, 0], ![7, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-17, 1, 0], ![2, -14, 8], ![155, 17, -20]]]
  hmulB := by decide  
  f := ![![![4015, -30222, 17280], ![-1314, -157680, 0]], ![![3075, -23170, 13248], ![-1021, -120888, 0]], ![![385, -2898, 1657], ![-126, -15120, 0]]]
  g := ![![![1, 0, 0], ![-56, 73, 0], ![-7, 0, 73]], ![![-1, 1, 0], ![10, -14, 8], ![-9, 17, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![18, -34, 1]] ![![73, 0, 0], ![-17, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-1241, 73, 0]], ![![1314, -2482, 73], ![-219, 511, -292]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-17, 1, 0]]], ![![![18, -34, 1]], ![![-3, 7, -4]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-9, -6, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-9, -6, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![70, 73, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-9, -6, 1], ![143, -10, -51], ![-1042, -89, 28]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-70, -73, 79]], ![![-1, -1, 1], ![47, 47, -51], ![-38, -27, 28]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [33, 38, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [41, 78], [0, 1]]
 g := ![![[61, 45], [52, 20], [52, 51], [14, 11], [22], [1]], ![[10, 34], [3, 59], [10, 28], [70, 68], [22], [1]]]
 h' := ![![[41, 78], [22, 60], [22, 40], [12, 50], [47, 13], [46, 41], [0, 1]], ![[0, 1], [33, 19], [3, 39], [8, 29], [27, 66], [68, 38], [41, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46]]
 b := ![[], [42, 23]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [33, 38, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![25753, 34180, 21295]
  a := ![-10, -15, -35]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-18543, -19245, 21295]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-28, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-28, 1, 0]] 
 ![![79, 0, 0], ![51, 1, 0], ![51, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-28, 1, 0], ![2, -25, 8], ![155, 17, -31]]]
  hmulB := by decide  
  f := ![![![3607, -53451, 17112], ![-1896, -168981, 0]], ![![2341, -34485, 11040], ![-1184, -109020, 0]], ![![2319, -34506, 11047], ![-1251, -109089, 0]]]
  g := ![![![1, 0, 0], ![-51, 79, 0], ![-51, 0, 79]], ![![-1, 1, 0], ![11, -25, 8], ![11, 17, -31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-9, -6, 1]] ![![79, 0, 0], ![-28, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![-2212, 79, 0]], ![![-711, -474, 79], ![395, 158, -79]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![-28, 1, 0]]], ![![![-9, -6, 1]], ![![5, 2, -1]]]]
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


lemma PB192I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB192I1 : PrimesBelowBoundCertificateInterval O 31 79 192 where
  m := 11
  g := ![1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB192I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0]
    · exact ![I43N0]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1, I53N2]
    · exact ![I59N0, I59N1, I59N2]
    · exact ![I61N0, I61N1]
    · exact ![I67N0]
    · exact ![I71N0]
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
    · exact ![50653]
    · exact ![68921]
    · exact ![79507]
    · exact ![2209, 47]
    · exact ![53, 53, 53]
    · exact ![59, 59, 59]
    · exact ![3721, 61]
    · exact ![300763]
    · exact ![357911]
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
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
      exact NI53N2
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
      exact NI59N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I47N1, I53N0, I53N1, I53N2, I59N0, I59N1, I59N2, I61N1, I73N1, I79N1]
  Il := ![[], [], [], [I47N1], [I53N0, I53N1, I53N2], [I59N0, I59N1, I59N2], [I61N1], [], [], [I73N1], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
