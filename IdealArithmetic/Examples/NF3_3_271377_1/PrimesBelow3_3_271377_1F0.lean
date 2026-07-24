
import IdealArithmetic.Examples.NF3_3_271377_1.RI3_3_271377_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![30, 29, 6]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![30, 29, 6]] 
 ![![2, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![30, 29, 6], ![276, 263, 52], ![1058, 1022, 211]]]
  hmulB := by decide  
  f := ![![![-2349, -13, 70]], ![![1610, 9, -48]], ![![-1909, -11, 57]]]
  g := ![![![15, 29, 6], ![138, 263, 52], ![529, 1022, 211]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7628035, -42123, 227291]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![-7628035, -42123, 227291]] 
 ![![2, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![-7628035, -42123, 227291], ![10455386, 57736, -311537], ![-12393044, -68436, 369273]]]
  hmulB := by decide  
  f := ![![![204, 297, 125]], ![![2977, 2524, 297]], ![![3956, 5424, 2141]]]
  g := ![![![-3792956, -42123, 227291], ![5198825, 57736, -311537], ![-6162304, -68436, 369273]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 28, -9]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![53, 28, -9]] 
 ![![2, 0, 0], ![1, 1, 0], ![1, 0, 1]] where
  M :=![![![53, 28, -9], ![-414, -225, 65], ![1702, 898, -290]]]
  hmulB := by decide  
  f := ![![![-6880, -38, 205]], ![![1275, 7, -38]], ![![-9029, -50, 269]]]
  g := ![![![17, 28, -9], ![-127, -225, 65], ![547, 898, -290]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![30, 29, 6]] ![![-7628035, -42123, 227291]]
  ![![6880, 38, -205]] where
 M := ![![![6880, 38, -205]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![6880, 38, -205]] ![![53, 28, -9]]
  ![![2, 0, 0]] where
 M := ![![![-2, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 10, 2]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![11, 10, 2]] 
 ![![3, 0, 0], ![1, 1, 0], ![2, 0, 1]] where
  M :=![![![11, 10, 2], ![92, 89, 18], ![368, 352, 71]]]
  hmulB := by decide  
  f := ![![![17, 6, -2]], ![![-25, -13, 4]], ![![134, 68, -21]]]
  g := ![![![-1, 10, 2], ![-11, 89, 18], ![-42, 352, 71]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![11, 10, 2]] ![![11, 10, 2]]
  ![![1777, 1704, 344]] where
 M := ![![![1777, 1704, 344]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![1777, 1704, 344]] ![![11, 10, 2]]
  ![![3, 0, 0]] where
 M := ![![![302907, 290514, 58650]]]
 hmul := by decide  
 g := ![![![![100969, 96838, 19550]]]]
 hle2 := by decide  

def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N0, I3N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1)
instance hp5 : Fact (Nat.Prime 5) := {out := by norm_num}

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-166847941, -921356, 4971534]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![-166847941, -921356, 4971534]] 
 ![![5, 0, 0], ![0, 5, 0], ![1, 1, 1]] where
  M :=![![![-166847941, -921356, 4971534], ![228690564, 1262859, -6814246], ![-271072940, -1496900, 8077105]]]
  hmulB := by decide  
  f := ![![![-18841, -18044, -3626]], ![![-166796, -160169, -32462]], ![![-169773, -162693, -32759]]]
  g := ![![![-34363895, -1178578, 4971534], ![47100962, 1615421, -6814246], ![-55830009, -1914801, 8077105]]]
  hle1 := by decide   
  hle2 := by decide  


def P5P0 : CertificateIrreducibleZModOfList' 5 2 2 2 [3, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 4], [0, 1]]
 g := ![![[], [1]], ![[], [1]]]
 h' := ![![[0, 4], [2], [0, 1]], ![[0, 1], [2], [0, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [0, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where
  n := 2
  hpos := by decide
  P := [3, 0, 1]
  hirr := P5P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![141, 466, 311]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-34, 31, 311]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI5N0 B_one_repr
lemma NI5N0 : Nat.card (O ⧸ I5N0) = 25 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-18841, -18044, -3626]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![-18841, -18044, -3626]] 
 ![![5, 0, 0], ![4, 1, 0], ![0, 0, 1]] where
  M :=![![![-18841, -18044, -3626], ![-166796, -160169, -32462], ![-663228, -635252, -127707]]]
  hmulB := by decide  
  f := ![![![-166847941, -921356, 4971534]], ![![-87740240, -484513, 2614378]], ![![-54214588, -299380, 1615421]]]
  g := ![![![10667, -18044, -3626], ![94776, -160169, -32462], ![375556, -635252, -127707]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![-166847941, -921356, 4971534]] ![![-18841, -18044, -3626]]
  ![![5, 0, 0]] where
 M := ![![![5, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P7P0 : CertificateIrreducibleZModOfList' 7 3 2 2 [6, 1, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 0, 5], [6, 6, 2], [0, 1]]
 g := ![![[1], [1]], ![[6, 5, 0, 6], [6, 6, 0, 6]], ![[4, 6, 2, 1], [3, 0, 2, 1]]]
 h' := ![![[1, 0, 5], [1, 6], [0, 1]], ![[6, 6, 2], [0, 0, 2], [1, 0, 5]], ![[0, 1], [2, 1, 5], [6, 6, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2], []]
 b := ![[], [3, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 3
  hpos := by decide
  P := [6, 1, 0, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7448, 81214, 73150]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1064, 11602, 10450]
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

instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4815, -2586, 782]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![-4815, -2586, 782]] 
 ![![11, 0, 0], ![0, 11, 0], ![3, 10, 1]] where
  M :=![![![-4815, -2586, 782], ![35972, 19187, -5954], ![-154928, -83232, 25141]]]
  hmulB := by decide  
  f := ![![![1198451, 6618, -35710]], ![![-1642660, -9071, 48946]], ![![-989469, -5464, 29483]]]
  g := ![![![-651, -946, 782], ![4894, 7157, -5954], ![-20941, -30422, 25141]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [5, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 10], [0, 1]]
 g := ![![[3, 9], [9, 5], [1]], ![[0, 2], [0, 6], [1]]]
 h' := ![![[7, 10], [10, 8], [6, 7], [0, 1]], ![[0, 1], [0, 3], [0, 4], [7, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [1, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 2
  hpos := by decide
  P := [5, 4, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3799, 6, 159]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![302, -144, 159]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1198451, -6618, 35710]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![-1198451, -6618, 35710]] 
 ![![11, 0, 0], ![3, 1, 0], ![5, 0, 1]] where
  M :=![![![-1198451, -6618, 35710], ![1642660, 9071, -48946], ![-1947088, -10752, 58017]]]
  hmulB := by decide  
  f := ![![![4815, 2586, -782]], ![![-1957, -1039, 328]], ![![16273, 8742, -2641]]]
  g := ![![![-123377, -6618, 35710], ![169107, 9071, -48946], ![-200447, -10752, 58017]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![-4815, -2586, 782]] ![![-1198451, -6618, 35710]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11663, 11214, 2282]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![11663, 11214, 2282]] 
 ![![13, 0, 0], ![0, 13, 0], ![4, 3, 1]] where
  M :=![![![11663, 11214, 2282], ![104972, 100465, 20146], ![410872, 394968, 80319]]]
  hmulB := by decide  
  f := ![![![8632539, 47670, -257222]], ![![-11832212, -65339, 352562]], ![![1004504, 5547, -29931]]]
  g := ![![![195, 336, 2282], ![1876, 3079, 20146], ![6892, 11847, 80319]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [12, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 12], [0, 1]]
 g := ![![[2, 12], [12], [2, 1]], ![[0, 1], [12], [4, 12]]]
 h' := ![![[2, 12], [3, 5], [2, 5], [0, 1]], ![[0, 1], [0, 8], [12, 8], [2, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [10, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 2
  hpos := by decide
  P := [12, 11, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![150, 444, 278]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-74, -30, 278]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8632539, -47670, 257222]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![-8632539, -47670, 257222]] 
 ![![13, 0, 0], ![8, 1, 0], ![3, 0, 1]] where
  M :=![![![-8632539, -47670, 257222], ![11832212, 65339, -352562], ![-14025032, -77448, 417901]]]
  hmulB := by decide  
  f := ![![![-11663, -11214, -2282]], ![![-15252, -14629, -2954]], ![![-34297, -32970, -6705]]]
  g := ![![![-694065, -47670, 257222], ![951322, 65339, -352562], ![-1127627, -77448, 417901]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![11663, 11214, 2282]] ![![-8632539, -47670, 257222]]
  ![![13, 0, 0]] where
 M := ![![![-13, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-245083, -235056, -47454]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![-245083, -235056, -47454]] 
 ![![17, 0, 0], ![0, 17, 0], ![4, 2, 1]] where
  M :=![![![-245083, -235056, -47454], ![-2182884, -2093575, -422658], ![-8629692, -8276628, -1670917]]]
  hmulB := by decide  
  f := ![![![-413003, -2280, 12306]], ![![566076, 3121, -16866]], ![![-70048, -386, 2087]]]
  g := ![![![-3251, -8244, -47454], ![-28956, -73427, -422658], ![-114472, -290282, -1670917]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 2 2 4 [13, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 16], [0, 1]]
 g := ![![[9, 4], [15], [4], [1]], ![[0, 13], [15], [4], [1]]]
 h' := ![![[2, 16], [13, 2], [15, 7], [4, 2], [0, 1]], ![[0, 1], [0, 15], [12, 10], [8, 15], [2, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [12, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 2
  hpos := by decide
  P := [13, 15, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![18383, 31946, 15752]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2625, 26, 15752]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-413003, -2280, 12306]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![-413003, -2280, 12306]] 
 ![![17, 0, 0], ![14, 1, 0], ![14, 0, 1]] where
  M :=![![![-413003, -2280, 12306], ![566076, 3121, -16866], ![-670956, -3684, 19987]]]
  hmulB := by decide  
  f := ![![![-245083, -235056, -47454]], ![![-330238, -316727, -63942]], ![![-709462, -680436, -137369]]]
  g := ![![![-32551, -2280, 12306], ![44618, 3121, -16866], ![-52894, -3684, 19987]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![-245083, -235056, -47454]] ![![-413003, -2280, 12306]]
  ![![17, 0, 0]] where
 M := ![![![17, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-739, -4, 22]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![-739, -4, 22]] 
 ![![19, 0, 0], ![2, 1, 0], ![16, 0, 1]] where
  M :=![![![-739, -4, 22], ![1012, 5, -30], ![-1196, -4, 35]]]
  hmulB := by decide  
  f := ![![![55, 52, 10]], ![![30, 29, 6]], ![![148, 140, 27]]]
  g := ![![![-57, -4, 22], ![78, 5, -30], ![-92, -4, 35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N0 : Nat.card (O ⧸ I19N0) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N0)

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := prime_ideal_of_norm_prime hp19.out _ NI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2435, -2336, -472]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![-2435, -2336, -472]] 
 ![![19, 0, 0], ![15, 1, 0], ![13, 0, 1]] where
  M :=![![![-2435, -2336, -472], ![-21712, -20819, -4200], ![-85744, -82256, -16619]]]
  hmulB := by decide  
  f := ![![![-515761, -2848, 15368]], ![![-369973, -2043, 11024]], ![![-396991, -2192, 11829]]]
  g := ![![![2039, -2336, -472], ![18167, -20819, -4200], ![71797, -82256, -16619]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![-739, -4, 22]] ![![-739, -4, 22]]
  ![![515761, 2848, -15368]] where
 M := ![![![515761, 2848, -15368]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI19N1 : IdealMulLeCertificate' Table 
  ![![515761, 2848, -15368]] ![![-2435, -2336, -472]]
  ![![19, 0, 0]] where
 M := ![![![-19, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC19 : ContainsPrimesAboveP 19 ![I19N0, I19N0, I19N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N0
    exact isPrimeI19N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 19 (by decide) (𝕀 ⊙ MulI19N0 ⊙ MulI19N1)

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1784823, -9856, 53182]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![-1784823, -9856, 53182]] 
 ![![23, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![-1784823, -9856, 53182], ![2446372, 13509, -72894], ![-2899748, -16012, 86403]]]
  hmulB := by decide  
  f := ![![![39399, 37784, 7626]], ![![15252, 14629, 2954]], ![![60316, 57844, 11675]]]
  g := ![![![-77601, -9856, 53182], ![106364, 13509, -72894], ![-126076, -16012, 86403]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N0 : Nat.card (O ⧸ I23N0) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N0)

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := prime_ideal_of_norm_prime hp23.out _ NI23N0
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![-1784823, -9856, 53182]] ![![-1784823, -9856, 53182]]
  ![![3007267300761, 16606520600, -89606929176]] where
 M := ![![![3007267300761, 16606520600, -89606929176]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI23N1 : IdealMulLeCertificate' Table 
  ![![3007267300761, 16606520600, -89606929176]] ![![-1784823, -9856, 53182]]
  ![![23, 0, 0]] where
 M := ![![![-5066976604868639455, -27980502879548904, 150979666374861174]]]
 hmul := by decide  
 g := ![![![![-220303330646462585, -1216543603458648, 6564333320646138]]]]
 hle2 := by decide  

def PBC23 : ContainsPrimesAboveP 23 ![I23N0, I23N0, I23N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
    exact isPrimeI23N0
    exact isPrimeI23N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 23 (by decide) (𝕀 ⊙ MulI23N0 ⊙ MulI23N1)
instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107931, 596, -3216]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![107931, 596, -3216]] 
 ![![29, 0, 0], ![13, 1, 0], ![25, 0, 1]] where
  M :=![![![107931, 596, -3216], ![-147936, -817, 4408], ![175352, 968, -5225]]]
  hmulB := by decide  
  f := ![![![-1881, -1012, 304]], ![![-361, -197, 56]], ![![-3709, -1996, 599]]]
  g := ![![![6227, 596, -3216], ![-8535, -817, 4408], ![10117, 968, -5225]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N0 : Nat.card (O ⧸ I29N0) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N0)

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := prime_ideal_of_norm_prime hp29.out _ NI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15, 2, 0]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![15, 2, 0]] 
 ![![29, 0, 0], ![22, 1, 0], ![8, 0, 1]] where
  M :=![![![15, 2, 0], ![0, 17, 4], ![92, 68, 13]]]
  hmulB := by decide  
  f := ![![![51, 26, -8]], ![![26, 13, -4]], ![![68, 36, -11]]]
  g := ![![![-1, 2, 0], ![-14, 17, 4], ![-52, 68, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1

def I29N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![585703, 561740, 113406]] i)))

def SI29N2: IdealEqSpanCertificate' Table ![![585703, 561740, 113406]] 
 ![![29, 0, 0], ![23, 1, 0], ![14, 0, 1]] where
  M :=![![![585703, 561740, 113406], ![5216676, 5003247, 1010074], ![20623364, 19779596, 3993173]]]
  hmulB := by decide  
  f := ![![![-24817373, -137044, 739478]], ![![-18509779, -102213, 551532]], ![![-13371146, -73836, 398417]]]
  g := ![![![-480069, 561740, 113406], ![-4275829, 5003247, 1010074], ![-16903854, 19779596, 3993173]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N2 : Nat.card (O ⧸ I29N2) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N2)

lemma isPrimeI29N2 : Ideal.IsPrime I29N2 := prime_ideal_of_norm_prime hp29.out _ NI29N2
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![107931, 596, -3216]] ![![15, 2, 0]]
  ![![1323093, 7306, -39424]] where
 M := ![![![1323093, 7306, -39424]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI29N1 : IdealMulLeCertificate' Table 
  ![![1323093, 7306, -39424]] ![![585703, 561740, 113406]]
  ![![29, 0, 0]] where
 M := ![![![-2928101, -2808302, -566950]]]
 hmul := by decide  
 g := ![![![![-100969, -96838, -19550]]]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![387, 4, -12]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![387, 4, -12]] 
 ![![31, 0, 0], ![0, 31, 0], ![22, 10, 1]] where
  M :=![![![387, 4, -12], ![-552, -17, 20], ![736, 64, -37]]]
  hmulB := by decide  
  f := ![![![21, 20, 4]], ![![184, 177, 36]], ![![98, 94, 19]]]
  g := ![![![21, 4, -12], ![-32, -7, 20], ![50, 14, -37]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [4, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [13, 30], [0, 1]]
 g := ![![[20, 8], [21, 28], [12, 7], [13, 1]], ![[0, 23], [13, 3], [10, 24], [26, 30]]]
 h' := ![![[13, 30], [9, 16], [14, 11], [10, 10], [0, 1]], ![[0, 1], [0, 15], [2, 20], [16, 21], [13, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [9, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [4, 18, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![125, 178, 55]
  a := ![-1, 2, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-35, -12, 55]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-21, -20, -4]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![-21, -20, -4]] 
 ![![31, 0, 0], ![12, 1, 0], ![15, 0, 1]] where
  M :=![![![-21, -20, -4], ![-184, -177, -36], ![-736, -704, -141]]]
  hmulB := by decide  
  f := ![![![-387, -4, 12]], ![![-132, -1, 4]], ![![-211, -4, 7]]]
  g := ![![![9, -20, -4], ![80, -177, -36], ![317, -704, -141]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![387, 4, -12]] ![![-21, -20, -4]]
  ![![31, 0, 0]] where
 M := ![![![-31, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


lemma PB116I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB116I0 : PrimesBelowBoundCertificateInterval O 1 31 116 where
  m := 11
  g := ![3, 3, 2, 1, 2, 2, 2, 3, 3, 3, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB116I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N2]
    · exact ![I3N0, I3N0, I3N0]
    · exact ![I5N0, I5N1]
    · exact ![I7N0]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1]
    · exact ![I17N0, I17N1]
    · exact ![I19N0, I19N0, I19N1]
    · exact ![I23N0, I23N0, I23N0]
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
    · exact ![3, 3, 3]
    · exact ![25, 5]
    · exact ![343]
    · exact ![121, 11]
    · exact ![169, 13]
    · exact ![289, 17]
    · exact ![19, 19, 19]
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
      exact NI2N1
      exact NI2N2
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N0
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
      exact NI19N0
      exact NI19N1
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N0
      exact NI23N0
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
      exact NI29N2
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
  β := ![I2N0, I2N1, I2N2, I3N0, I5N0, I5N1, I11N1, I13N1, I17N1, I19N0, I19N1, I23N0, I29N0, I29N1, I29N2, I31N1]
  Il := ![[I2N0, I2N1, I2N2], [I3N0, I3N0, I3N0], [I5N0, I5N1], [], [I11N1], [I13N1], [I17N1], [I19N0, I19N0, I19N1], [I23N0, I23N0, I23N0], [I29N0, I29N1, I29N2], [I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
