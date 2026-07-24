
import IdealArithmetic.Examples.NF3_3_670761_3.RI3_3_670761_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-18, 1, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-18, 1, 0]] 
 ![![37, 0, 0], ![19, 1, 0], ![28, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-18, 1, 0], ![2, -17, 5], ![309, 54, -19]]]
  hmulB := by decide  
  f := ![![![-83, 1018, -300], ![74, 2220, 0]], ![![-41, 509, -150], ![38, 1110, 0]], ![![-56, 770, -227], ![70, 1680, 0]]]
  g := ![![![1, 0, 0], ![-19, 37, 0], ![-28, 0, 37]], ![![-1, 1, 0], ![5, -17, 5], ![-5, 54, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-11, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-11, 1, 0]] 
 ![![37, 0, 0], ![26, 1, 0], ![8, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-11, 1, 0], ![2, -10, 5], ![309, 54, -12]]]
  hmulB := by decide  
  f := ![![![-364, 2095, -1050], ![185, 7770, 0]], ![![-249, 1466, -735], ![149, 5439, 0]], ![![-79, 453, -227], ![39, 1680, 0]]]
  g := ![![![1, 0, 0], ![-26, 37, 0], ![-8, 0, 37]], ![![-1, 1, 0], ![6, -10, 5], ![-27, 54, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-8, 1, 0]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-8, 1, 0]] 
 ![![37, 0, 0], ![29, 1, 0], ![4, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-8, 1, 0], ![2, -7, 5], ![309, 54, -9]]]
  hmulB := by decide  
  f := ![![![1293, -4819, 3450], ![-407, -25530, 0]], ![![1017, -3772, 2700], ![-295, -19980, 0]], ![![140, -521, 373], ![-43, -2760, 0]]]
  g := ![![![1, 0, 0], ![-29, 37, 0], ![-4, 0, 37]], ![![-1, 1, 0], ![5, -7, 5], ![-33, 54, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![-18, 1, 0]] ![![37, 0, 0], ![-11, 1, 0]]
  ![![37, 0, 0], ![-34, -13, 1]] where
 M := ![![![1369, 0, 0], ![-407, 37, 0]], ![![-666, 37, 0], ![200, -28, 5]]]
 hmul := by decide  
 g := ![![![![37, 0, 0], ![0, 0, 0]], ![![23, 14, -1], ![37, 0, 0]]], ![![![16, 14, -1], ![37, 0, 0]], ![![10, 1, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![-34, -13, 1]] ![![37, 0, 0], ![-8, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-296, 37, 0]], ![![-1258, -481, 37], ![555, 111, -74]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-8, 1, 0]]], ![![![-34, -13, 1]], ![![15, 3, -2]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1, I37N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
    exact isPrimeI37N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0 ⊙ MulI37N1)
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


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [38, 38, 13, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [26, 40, 39], [2, 0, 2], [0, 1]]
 g := ![![[36, 25, 23], [26, 39], [33, 2], [8, 28, 1], []], ![[8, 4, 8, 20], [], [6, 39], [39, 20], [34, 4]], ![[38, 30, 0, 1], [24, 39], [1, 5], [39, 6, 17, 2], [30, 4]]]
 h' := ![![[26, 40, 39], [29, 31, 33], [19, 0, 11], [24, 26, 24], [0, 0, 1], [0, 1]], ![[2, 0, 2], [23, 6, 20], [8, 26], [20, 27, 30], [40, 21], [26, 40, 39]], ![[0, 1], [36, 4, 29], [28, 15, 30], [36, 29, 28], [12, 20, 40], [2, 0, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19, 14], []]
 b := ![[], [18, 32, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [38, 38, 13, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3774419, -1122457, -382325]
  a := ![-2, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-92059, -27377, -9325]
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


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [3, 6, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 5, 7], [15, 37, 36], [0, 1]]
 g := ![![[5, 39, 1], [37, 36, 41], [42, 9], [37, 0, 1], []], ![[5, 41, 20, 5], [23, 20, 41, 39], [1, 15], [10, 15, 36, 37], [27, 6]], ![[3, 19, 0, 10], [9, 36, 25, 21], [36, 38], [35, 31, 13, 40], [41, 6]]]
 h' := ![![[28, 5, 7], [18, 2, 42], [26, 28, 16], [18, 36, 40], [0, 0, 1], [0, 1]], ![[15, 37, 36], [16, 39, 20], [18, 20, 14], [35, 9, 12], [15, 14, 37], [28, 5, 7]], ![[0, 1], [32, 2, 24], [14, 38, 13], [37, 41, 34], [16, 29, 5], [15, 37, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 38], []]
 b := ![[], [21, 41, 13], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [3, 6, 0, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![22263035, 12230361, 6208254]
  a := ![5, 0, 13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![517745, 284427, 144378]
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


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [24, 36, 39, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [44, 36, 28], [11, 10, 19], [0, 1]]
 g := ![![[6, 37, 3], [46, 19, 18], [5, 35, 36], [28, 8, 1], []], ![[23, 11, 11, 18], [4, 1, 12, 8], [35, 42, 4, 1], [1, 42, 45, 27], [16, 32]], ![[5, 40, 6, 11], [10, 39, 29, 35], [24, 8, 28, 40], [24, 10, 1, 43], [25, 32]]]
 h' := ![![[44, 36, 28], [24, 21, 35], [21, 22, 26], [33, 22, 6], [0, 0, 1], [0, 1]], ![[11, 10, 19], [43, 18, 45], [28, 41, 30], [20, 33, 18], [1, 38, 10], [44, 36, 28]], ![[0, 1], [34, 8, 14], [29, 31, 38], [33, 39, 23], [38, 9, 36], [11, 10, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 40], []]
 b := ![[], [39, 35, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [24, 36, 39, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-81761754929, -23556023577, -7779371709]
  a := ![-66, -64, -133]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1739611807, -501191991, -165518547]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0]] 
 ![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [42, 18, 41, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [27, 6, 9], [38, 46, 44], [0, 1]]
 g := ![![[41, 22, 36], [30, 47], [15, 0, 29], [24, 38], [1]], ![[19, 17, 30, 13], [22, 10], [18, 52, 7, 9], [28, 43], [17, 18, 30, 40]], ![[46, 32, 42, 44], [6, 52], [31, 12, 36, 37], [24, 7], [22, 2, 45, 13]]]
 h' := ![![[27, 6, 9], [48, 43, 47], [6, 32, 43], [14, 14, 33], [11, 35, 12], [0, 1]], ![[38, 46, 44], [20, 4, 5], [19, 16, 40], [15, 50, 1], [48, 29, 19], [27, 6, 9]], ![[0, 1], [50, 6, 1], [39, 5, 23], [35, 42, 19], [47, 42, 22], [38, 46, 44]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47, 41], []]
 b := ![[], [29, 33, 19], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [42, 18, 41, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-31265071, -13305014, -5941936]
  a := ![-5, -1, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-589907, -251038, -112112]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0]] 
 ![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [55, 54, 15, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [28, 46, 58], [16, 12, 1], [0, 1]]
 g := ![![[7, 42, 35], [4, 27, 5], [12, 21], [38, 15, 48], [1]], ![[1, 18, 25, 37], [32, 5, 18, 31], [], [34, 50, 53, 54], [57, 50, 35, 58]], ![[18, 32, 16, 35], [2, 26, 37, 51], [54, 21], [4, 57, 58, 57], [26, 52, 21, 1]]]
 h' := ![![[28, 46, 58], [16, 55, 25], [24, 1, 51], [34, 30, 32], [4, 5, 44], [0, 1]], ![[16, 12, 1], [13, 24, 9], [36, 29, 21], [53, 32], [55, 58, 51], [28, 46, 58]], ![[0, 1], [54, 39, 25], [5, 29, 46], [5, 56, 27], [11, 55, 23], [16, 12, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 42], []]
 b := ![[], [28, 46, 42], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [55, 54, 15, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3767150, -1117755, -379665]
  a := ![-2, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-63850, -18945, -6435]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 205379 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def PBC59 : ContainsPrimesAboveP 59 ![I59N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![59, 0, 0]]) timesTableT_eq_Table B_one_repr 59 (by decide) 𝕀

instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![10, 1, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![10, 1, 0]] 
 ![![61, 0, 0], ![10, 1, 0], ![15, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![10, 1, 0], ![2, 11, 5], ![309, 54, 9]]]
  hmulB := by decide  
  f := ![![![841, 4836, 2200], ![244, -26840, 0]], ![![134, 791, 360], ![62, -4392, 0]], ![![205, 1189, 541], ![71, -6600, 0]]]
  g := ![![![1, 0, 0], ![-10, 61, 0], ![-15, 0, 61]], ![![0, 1, 0], ![-3, 11, 5], ![-6, 54, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N0 : Nat.card (O ⧸ I61N0) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N0)

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := prime_ideal_of_norm_prime hp61.out _ NI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![20, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![20, 1, 0]] 
 ![![61, 0, 0], ![20, 1, 0], ![14, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![20, 1, 0], ![2, 21, 5], ![309, 54, 19]]]
  hmulB := by decide  
  f := ![![![5133, 63291, 15080], ![2745, -183976, 0]], ![![1676, 20733, 4940], ![916, -60268, 0]], ![![1162, 14525, 3461], ![679, -42224, 0]]]
  g := ![![![1, 0, 0], ![-20, 61, 0], ![-14, 0, 61]], ![![0, 1, 0], ![-8, 21, 5], ![-17, 54, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-30, 1, 0]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-30, 1, 0]] 
 ![![61, 0, 0], ![31, 1, 0], ![46, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-30, 1, 0], ![2, -29, 5], ![309, 54, -31]]]
  hmulB := by decide  
  f := ![![![-87, 2144, -370], ![122, 4514, 0]], ![![-43, 1072, -185], ![62, 2257, 0]], ![![-72, 1617, -279], ![79, 3404, 0]]]
  g := ![![![1, 0, 0], ![-31, 61, 0], ![-46, 0, 61]], ![![-1, 1, 0], ![11, -29, 5], ![1, 54, -31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![10, 1, 0]] ![![61, 0, 0], ![20, 1, 0]]
  ![![61, 0, 0], ![-45, -6, 1]] where
 M := ![![![3721, 0, 0], ![1220, 61, 0]], ![![610, 61, 0], ![202, 31, 5]]]
 hmul := by decide  
 g := ![![![![61, 0, 0], ![0, 0, 0]], ![![20, 1, 0], ![0, 0, 0]]], ![![![10, 1, 0], ![0, 0, 0]], ![![7, 1, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-45, -6, 1]] ![![61, 0, 0], ![-30, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-1830, 61, 0]], ![![-2745, -366, 61], ![1647, 183, -61]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-30, 1, 0]]], ![![![-45, -6, 1]], ![![27, 3, -1]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1, I61N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
    exact isPrimeI61N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0 ⊙ MulI61N1)
instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![14, 1, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![14, 1, 0]] 
 ![![67, 0, 0], ![14, 1, 0], ![12, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![14, 1, 0], ![2, 15, 5], ![309, 54, 13]]]
  hmulB := by decide  
  f := ![![![-2923, -23386, -7800], ![-938, 104520, 0]], ![![-622, -4873, -1625], ![-133, 21775, 0]], ![![-530, -4189, -1397], ![-137, 18720, 0]]]
  g := ![![![1, 0, 0], ![-14, 67, 0], ![-12, 0, 67]], ![![0, 1, 0], ![-4, 15, 5], ![-9, 54, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N0 : Nat.card (O ⧸ I67N0) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N0)

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := prime_ideal_of_norm_prime hp67.out _ NI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![20, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![20, 1, 0]] 
 ![![67, 0, 0], ![20, 1, 0], ![37, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![20, 1, 0], ![2, 21, 5], ![309, 54, 19]]]
  hmulB := by decide  
  f := ![![![1793, 21533, 5130], ![871, -68742, 0]], ![![532, 6422, 1530], ![269, -20502, 0]], ![![983, 11891, 2833], ![505, -37962, 0]]]
  g := ![![![1, 0, 0], ![-20, 67, 0], ![-37, 0, 67]], ![![0, 1, 0], ![-9, 21, 5], ![-22, 54, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1

def I67N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![33, 1, 0]] i)))

def SI67N2: IdealEqSpanCertificate' Table ![![67, 0, 0], ![33, 1, 0]] 
 ![![67, 0, 0], ![33, 1, 0], ![44, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![33, 1, 0], ![2, 34, 5], ![309, 54, 32]]]
  hmulB := by decide  
  f := ![![![2746, 66265, 9750], ![2345, -130650, 0]], ![![1326, 32622, 4800], ![1207, -64320, 0]], ![![1793, 43517, 6403], ![1561, -85800, 0]]]
  g := ![![![1, 0, 0], ![-33, 67, 0], ![-44, 0, 67]], ![![0, 1, 0], ![-20, 34, 5], ![-43, 54, 32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N2 : Nat.card (O ⧸ I67N2) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N2)

lemma isPrimeI67N2 : Ideal.IsPrime I67N2 := prime_ideal_of_norm_prime hp67.out _ NI67N2
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![14, 1, 0]] ![![67, 0, 0], ![20, 1, 0]]
  ![![67, 0, 0], ![-24, 7, 1]] where
 M := ![![![4489, 0, 0], ![1340, 67, 0]], ![![938, 67, 0], ![282, 35, 5]]]
 hmul := by decide  
 g := ![![![![67, 0, 0], ![0, 0, 0]], ![![20, 1, 0], ![0, 0, 0]]], ![![![14, 1, 0], ![0, 0, 0]], ![![6, 0, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![-24, 7, 1]] ![![67, 0, 0], ![33, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![2211, 67, 0]], ![![-1608, 469, 67], ![-469, 268, 67]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![33, 1, 0]]], ![![![-24, 7, 1]], ![![-7, 4, 1]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0]] 
 ![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [38, 68, 16, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 31, 69], [28, 39, 2], [0, 1]]
 g := ![![[46, 15, 15], [53, 13, 18], [24, 66, 36], [51, 57], [55, 1], []], ![[52, 26, 28, 35], [31, 24, 8, 41], [50, 18, 47, 47], [25, 58], [49, 30], [25, 4]], ![[14, 39, 26, 37], [27, 39, 32, 37], [2, 13, 32, 20], [10, 8], [62, 38], [21, 4]]]
 h' := ![![[27, 31, 69], [45, 70, 50], [11, 54, 35], [17, 53, 65], [40, 56, 46], [0, 0, 1], [0, 1]], ![[28, 39, 2], [44, 15, 35], [53, 59, 50], [5, 13, 15], [48, 9, 49], [63, 35, 39], [27, 31, 69]], ![[0, 1], [27, 57, 57], [39, 29, 57], [23, 5, 62], [41, 6, 47], [57, 36, 31], [28, 39, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 23], []]
 b := ![[], [30, 3, 47], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [38, 68, 16, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![69974618, 16597812, 4193189]
  a := ![3, 21, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![985558, 233772, 59059]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0]] 
 ![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [61, 23, 35, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [29, 33, 1], [9, 39, 72], [0, 1]]
 g := ![![[45, 39, 61], [41, 32], [70, 6], [31, 58, 61], [38, 1], []], ![[63, 39, 64, 50], [10, 50], [72, 50], [0, 58, 32, 19], [61, 61], [31, 1]], ![[18, 3, 37, 38], [19, 16], [3, 1], [28, 18, 57, 50], [14, 67], [33, 1]]]
 h' := ![![[29, 33, 1], [4, 26, 39], [13, 59, 55], [7, 15, 58], [18, 14, 34], [0, 0, 1], [0, 1]], ![[9, 39, 72], [31, 58, 14], [38, 42, 14], [59, 39, 14], [56, 21, 26], [45, 45, 39], [29, 33, 1]], ![[0, 1], [7, 62, 20], [61, 45, 4], [68, 19, 1], [10, 38, 13], [39, 28, 33], [9, 39, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 28], []]
 b := ![[], [52, 52, 45], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [61, 23, 35, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1284581, -1429121, -853443]
  a := ![-3, 1, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-17597, -19577, -11691]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 389017 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def PBC73 : ContainsPrimesAboveP 73 ![I73N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![73, 0, 0]]) timesTableT_eq_Table B_one_repr 73 (by decide) 𝕀

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


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [78, 53, 14, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 65, 73], [34, 13, 6], [0, 1]]
 g := ![![[31, 0, 10], [72, 71, 31], [73, 20, 10], [54, 77, 67], [65, 1], []], ![[64, 71, 38, 21], [73, 63, 20, 44], [55, 44, 41, 49], [17, 48, 5, 11], [7, 11], [59, 36]], ![[52, 53, 7, 35], [19, 3, 78, 70], [0, 49, 46, 77], [7, 54, 59, 57], [6, 38], [47, 36]]]
 h' := ![![[31, 65, 73], [72, 4, 57], [73, 15, 30], [54, 18, 22], [65, 32, 64], [0, 0, 1], [0, 1]], ![[34, 13, 6], [34, 63, 6], [12, 73, 63], [63, 24, 20], [56, 3, 8], [72, 70, 13], [31, 65, 73]], ![[0, 1], [49, 12, 16], [17, 70, 65], [35, 37, 37], [14, 44, 7], [18, 9, 65], [34, 13, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 50], []]
 b := ![[], [18, 57, 61], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [78, 53, 14, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![25565585, 8395014, 3159210]
  a := ![4, 3, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![323615, 106266, 39990]
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



lemma PB183I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB183I1 : PrimesBelowBoundCertificateInterval O 31 79 183 where
  m := 11
  g := ![3, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB183I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0]
    · exact ![I43N0]
    · exact ![I47N0]
    · exact ![I53N0]
    · exact ![I59N0]
    · exact ![I61N0, I61N1, I61N2]
    · exact ![I67N0, I67N1, I67N2]
    · exact ![I71N0]
    · exact ![I73N0]
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
    · exact ![37, 37, 37]
    · exact ![68921]
    · exact ![79507]
    · exact ![103823]
    · exact ![148877]
    · exact ![205379]
    · exact ![61, 61, 61]
    · exact ![67, 67, 67]
    · exact ![357911]
    · exact ![389017]
    · exact ![493039]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
      exact NI37N2
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
      exact NI61N2
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
      exact NI67N2
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
  β := ![I37N0, I37N1, I37N2, I61N0, I61N1, I61N2, I67N0, I67N1, I67N2]
  Il := ![[I37N0, I37N1, I37N2], [], [], [], [], [], [I61N0, I61N1, I61N2], [I67N0, I67N1, I67N2], [], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
