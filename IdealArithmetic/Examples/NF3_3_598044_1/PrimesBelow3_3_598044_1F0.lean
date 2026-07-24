
import IdealArithmetic.Examples.NF3_3_598044_1.RI3_3_598044_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1135, -2, -27]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![1135, -2, -27]] 
 ![![2, 0, 0], ![0, 1, 0], ![1, 0, 1]] where
  M :=![![![1135, -2, -27], ![162, -1, -4], ![-69, -3, 1]]]
  hmulB := by decide  
  f := ![![![-13, 83, -19]], ![![57, -364, 83]], ![![-284, 1813, -415]]]
  g := ![![![581, -2, -27], ![83, -1, -4], ![-35, -3, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![104942, -807720, -168091]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![104942, -807720, -168091]] 
 ![![2, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![104942, -807720, -168091], ![1008546, -7762600, -1615440], ![4342047, -33419967, -6954880]]]
  hmulB := by decide  
  f := ![![![-2480, -603, 200]], ![![-1840, 2357, -503]], ![![2109, -12963, 2960]]]
  g := ![![![456331, -807720, -168091], ![4385573, -7762600, -1615440], ![18881007, -33419967, -6954880]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![1135, -2, -27]] ![![1135, -2, -27]]
  ![![1289764, -2187, -30664]] where
 M := ![![![1289764, -2187, -30664]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI2N1 : IdealMulLeCertificate' Table 
  ![![1289764, -2187, -30664]] ![![104942, -807720, -168091]]
  ![![2, 0, 0]] where
 M := ![![![194378, -1503792, -312924]]]
 hmul := by decide  
 g := ![![![![97189, -751896, -156462]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N0, I2N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N0
    exact isPrimeI2N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-28896, 49, 687]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![-28896, 49, 687]] 
 ![![3, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![-28896, 49, 687], ![-4122, 7, 98], ![1767, -3, -42]]]
  hmulB := by decide  
  f := ![![![0, 3, 7]], ![![-14, 99, 2]], ![![1, 35, 98]]]
  g := ![![![-9632, 49, 687], ![-1374, 7, 98], ![589, -3, -42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-938, 5, 23]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![-938, 5, 23]] 
 ![![3, 0, 0], ![2, 1, 0], ![0, 0, 1]] where
  M :=![![![-938, 5, 23], ![-138, 33, 10], ![39, 141, 28]]]
  hmulB := by decide  
  f := ![![![-486, 3103, -709]], ![![1094, -6985, 1596]], ![![-6915, 44151, -10088]]]
  g := ![![![-316, 5, 23], ![-68, 33, 10], ![-81, 141, 28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![-28896, 49, 687]] ![![-28896, 49, 687]]
  ![![835990767, -1417622, -19875604]] where
 M := ![![![835990767, -1417622, -19875604]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![835990767, -1417622, -19875604]] ![![-938, 5, 23]]
  ![![3, 0, 0]] where
 M := ![![![-784738856166, 1330712145, 18657094509]]]
 hmul := by decide  
 g := ![![![![-261579618722, 443570715, 6219031503]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N0, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1)
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


def P5P0 : CertificateIrreducibleZModOfList' 5 3 2 2 [4, 3, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 2, 1], [3, 2, 4], [0, 1]]
 g := ![![[3, 1, 1], []], ![[0, 3, 4, 4], [0, 1]], ![[2, 3, 1, 1], [2, 1]]]
 h' := ![![[3, 2, 1], [0, 0, 1], [0, 1]], ![[3, 2, 4], [4, 3, 2], [3, 2, 1]], ![[0, 1], [1, 2, 2], [3, 2, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 4], []]
 b := ![[], [0, 4, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where
  n := 3
  hpos := by decide
  P := [4, 3, 4, 1]
  hirr := P5P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9640, -88510, -48890]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1928, -17702, -9778]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![389, -2862, -596]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![389, -2862, -596]] 
 ![![7, 0, 0], ![0, 7, 0], ![3, 6, 1]] where
  M :=![![![389, -2862, -596], ![3576, -27505, -5724], ![15384, -118416, -24643]]]
  hmulB := by decide  
  f := ![![![1067, -6810, 1556]], ![![-9336, 59609, -13620]], ![![-1041, 6648, -1519]]]
  g := ![![![311, 102, -596], ![2964, 977, -5724], ![12759, 4206, -24643]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 2 2 2 [5, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 6], [0, 1]]
 g := ![![[5, 2], [3, 1]], ![[4, 5], [6, 6]]]
 h' := ![![[3, 6], [6, 4], [0, 1]], ![[0, 1], [4, 3], [3, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [1, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 2
  hpos := by decide
  P := [5, 4, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2, 291, 682]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-292, -543, 682]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1067, 6810, -1556]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![-1067, 6810, -1556]] 
 ![![7, 0, 0], ![2, 1, 0], ![4, 0, 1]] where
  M :=![![![-1067, 6810, -1556], ![9336, -59609, 13620], ![-45528, 290688, -66419]]]
  hmulB := by decide  
  f := ![![![-389, 2862, 596]], ![![-622, 4747, 988]], ![![-2420, 18552, 3861]]]
  g := ![![![-1209, 6810, -1556], ![10582, -59609, 13620], ![-51604, 290688, -66419]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![389, -2862, -596]] ![![-1067, 6810, -1556]]
  ![![7, 0, 0]] where
 M := ![![![-7, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![290, -1, -7]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![290, -1, -7]] 
 ![![11, 0, 0], ![0, 11, 0], ![1, 8, 1]] where
  M :=![![![290, -1, -7], ![42, -5, -2], ![-15, -21, -4]]]
  hmulB := by decide  
  f := ![![![-2, 13, -3]], ![![18, -115, 26]], ![![5, -32, 7]]]
  g := ![![![27, 5, -7], ![4, 1, -2], ![-1, 1, -4]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [8, 4, 1] where
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
 g := ![![[6, 4], [0, 5], [1]], ![[1, 7], [2, 6], [1]]]
 h' := ![![[7, 10], [0, 2], [3, 7], [0, 1]], ![[0, 1], [3, 9], [8, 4], [7, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [3, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 2
  hpos := by decide
  P := [8, 4, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3851, -3, 166]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![335, -121, 166]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2, 13, -3]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![-2, 13, -3]] 
 ![![11, 0, 0], ![6, 1, 0], ![1, 0, 1]] where
  M :=![![![-2, 13, -3], ![18, -115, 26], ![-87, 555, -128]]]
  hmulB := by decide  
  f := ![![![290, -1, -7]], ![![162, -1, -4]], ![![25, -2, -1]]]
  g := ![![![-7, 13, -3], ![62, -115, 26], ![-299, 555, -128]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![290, -1, -7]] ![![-2, 13, -3]]
  ![![11, 0, 0]] where
 M := ![![![11, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-359, -2, 8]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![-359, -2, 8]] 
 ![![13, 0, 0], ![0, 13, 0], ![12, 3, 1]] where
  M :=![![![-359, -2, 8], ![-48, -25, -4], ![36, -108, -23]]]
  hmulB := by decide  
  f := ![![![-11, 70, -16]], ![![96, -613, 140]], ![![-24, 153, -35]]]
  g := ![![![-35, -2, 8], ![0, -1, -4], ![24, -3, -23]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [3, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 12], [0, 1]]
 g := ![![[5, 9], [1], [11, 1]], ![[0, 4], [1], [9, 12]]]
 h' := ![![[11, 12], [7, 10], [6, 1], [0, 1]], ![[0, 1], [0, 3], [4, 12], [11, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [10, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 2
  hpos := by decide
  P := [3, 2, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-42, 477, 380]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-354, -51, 380]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11, 70, -16]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![-11, 70, -16]] 
 ![![13, 0, 0], ![7, 1, 0], ![11, 0, 1]] where
  M :=![![![-11, 70, -16], ![96, -613, 140], ![-468, 2988, -683]]]
  hmulB := by decide  
  f := ![![![-359, -2, 8]], ![![-197, -3, 4]], ![![-301, -10, 5]]]
  g := ![![![-25, 70, -16], ![219, -613, 140], ![-1067, 2988, -683]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![-359, -2, 8]] ![![-11, 70, -16]]
  ![![13, 0, 0]] where
 M := ![![![13, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0]] 
 ![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [15, 6, 15, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 10, 5], [6, 6, 12], [0, 1]]
 g := ![![[15, 0, 9], [14, 4], [2, 1], []], ![[5, 4, 2, 11], [10, 2], [13, 2], [14, 8]], ![[11, 0, 1, 7], [7, 16], [15, 15], [7, 8]]]
 h' := ![![[13, 10, 5], [10, 14, 3], [4, 7, 15], [0, 0, 1], [0, 1]], ![[6, 6, 12], [1, 2, 3], [7, 9, 6], [10, 5, 6], [13, 10, 5]], ![[0, 1], [6, 1, 11], [14, 1, 13], [16, 12, 10], [6, 6, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 3], []]
 b := ![[], [1, 14, 13], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [15, 6, 15, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5497205, 46548074, 18686842]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-323365, 2738122, 1099226]
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


def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4565, 35136, 7312]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![-4565, 35136, 7312]] 
 ![![19, 0, 0], ![3, 1, 0], ![13, 0, 1]] where
  M :=![![![-4565, 35136, 7312], ![-43872, 337675, 70272], ![-188880, 1453776, 302539]]]
  hmulB := by decide  
  f := ![![![109753, -192, -2608]], ![![18153, -29, -432]], ![![74743, -144, -1773]]]
  g := ![![![-10791, 35136, 7312], ![-103707, 337675, 70272], ![-446485, 1453776, 302539]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N0 : Nat.card (O ⧸ I19N0) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N0)

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := prime_ideal_of_norm_prime hp19.out _ NI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![331, 0, -8]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![331, 0, -8]] 
 ![![19, 0, 0], ![17, 1, 0], ![18, 0, 1]] where
  M :=![![![331, 0, -8], ![48, -5, 0], ![-24, 24, -5]]]
  hmulB := by decide  
  f := ![![![25, -192, -40]], ![![35, -269, -56]], ![![78, -600, -125]]]
  g := ![![![25, 0, -8], ![7, -5, 0], ![-18, 24, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![-4565, 35136, 7312]] ![![331, 0, -8]]
  ![![25, -192, -40]] where
 M := ![![![25, -192, -40]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI19N1 : IdealMulLeCertificate' Table 
  ![![25, -192, -40]] ![![331, 0, -8]]
  ![![19, 0, 0]] where
 M := ![![![19, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1853, -14262, -2968]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![1853, -14262, -2968]] 
 ![![23, 0, 0], ![0, 23, 0], ![10, 2, 1]] where
  M :=![![![1853, -14262, -2968], ![17808, -137065, -28524], ![76668, -590100, -122803]]]
  hmulB := by decide  
  f := ![![![835, -18, -16]], ![![96, 145, -36]], ![![374, -26, -3]]]
  g := ![![![1371, -362, -2968], ![13176, -3479, -28524], ![56726, -14978, -122803]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [15, 10, 1] where
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
 g := ![![[16, 4], [4, 4], [13, 8], [1]], ![[22, 19], [10, 19], [2, 15], [1]]]
 h' := ![![[13, 22], [9, 21], [12, 21], [8, 13], [0, 1]], ![[0, 1], [6, 2], [9, 2], [16, 10], [13, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [17, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 2
  hpos := by decide
  P := [15, 10, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-90, 1224, 1118]
  a := ![0, 3, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-490, -44, 1118]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-835, 18, 16]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![-835, 18, 16]] 
 ![![23, 0, 0], ![19, 1, 0], ![17, 0, 1]] where
  M :=![![![-835, 18, 16], ![-96, -145, 36], ![-60, 708, -163]]]
  hmulB := by decide  
  f := ![![![-1853, 14262, 2968]], ![![-2305, 17741, 3692]], ![![-4703, 36198, 7533]]]
  g := ![![![-63, 18, 16], ![89, -145, 36], ![-467, 708, -163]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![1853, -14262, -2968]] ![![-835, 18, 16]]
  ![![23, 0, 0]] where
 M := ![![![-23, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


def P29P0 : CertificateIrreducibleZModOfList' 29 3 2 4 [23, 23, 13, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 28, 26], [8, 0, 3], [0, 1]]
 g := ![![[11, 20, 25], [19, 24], [18, 25, 24], [1]], ![[9, 14, 19, 17], [10, 28], [5, 11, 2, 14], [10, 9, 5, 2]], ![[2, 23, 27, 27], [28, 16], [2, 24, 12, 12], [1, 11, 26, 27]]]
 h' := ![![[8, 28, 26], [4, 20, 5], [21, 4, 16], [6, 6, 16], [0, 1]], ![[8, 0, 3], [25, 1, 27], [20, 11, 17], [21, 9, 11], [8, 28, 26]], ![[0, 1], [19, 8, 26], [24, 14, 25], [25, 14, 2], [8, 0, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17, 14], []]
 b := ![[], [2, 2, 24], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 3
  hpos := by decide
  P := [23, 23, 13, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![184005, -1479580, -443642]
  a := ![2, -8, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![6345, -51020, -15298]
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

instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-16, 123, 25]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![-16, 123, 25]] 
 ![![31, 0, 0], ![0, 31, 0], ![13, 26, 1]] where
  M :=![![![-16, 123, 25], ![-150, 1157, 246], ![-663, 5091, 1034]]]
  hmulB := by decide  
  f := ![![![1808, -3, -43]], ![![258, -1, -6]], ![![971, -2, -23]]]
  g := ![![![-11, -17, 25], ![-108, -169, 246], ![-455, -703, 1034]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [30, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [24, 30], [0, 1]]
 g := ![![[24, 2], [17, 9], [28, 20], [24, 1]], ![[10, 29], [16, 22], [12, 11], [17, 30]]]
 h' := ![![[24, 30], [17, 23], [28, 28], [24, 19], [0, 1]], ![[0, 1], [11, 8], [18, 3], [15, 12], [24, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [18, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [30, 7, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![293, -3, 75]
  a := ![13, 0, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-22, -63, 75]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1808, 3, 43]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![-1808, 3, 43]] 
 ![![31, 0, 0], ![10, 1, 0], ![7, 0, 1]] where
  M :=![![![-1808, 3, 43], ![-258, 1, 6], ![111, -3, -2]]]
  hmulB := by decide  
  f := ![![![16, -123, -25]], ![![10, -77, -16]], ![![25, -192, -39]]]
  g := ![![![-69, 3, 43], ![-10, 1, 6], ![5, -3, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![-16, 123, 25]] ![![-1808, 3, 43]]
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


lemma PB172I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB172I0 : PrimesBelowBoundCertificateInterval O 1 31 172 where
  m := 11
  g := ![3, 3, 1, 2, 2, 2, 1, 3, 2, 1, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB172I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N0, I2N1]
    · exact ![I3N0, I3N0, I3N1]
    · exact ![I5N0]
    · exact ![I7N0, I7N1]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1]
    · exact ![I17N0]
    · exact ![I19N0, I19N1, I19N1]
    · exact ![I23N0, I23N1]
    · exact ![I29N0]
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
    · exact ![125]
    · exact ![49, 7]
    · exact ![121, 11]
    · exact ![169, 13]
    · exact ![4913]
    · exact ![19, 19, 19]
    · exact ![529, 23]
    · exact ![24389]
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
      exact NI2N1
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
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
  β := ![I2N0, I2N1, I3N0, I3N1, I5N0, I7N0, I7N1, I11N0, I11N1, I13N0, I13N1, I19N0, I19N1, I23N1, I31N1]
  Il := ![[I2N0, I2N0, I2N1], [I3N0, I3N0, I3N1], [I5N0], [I7N0, I7N1], [I11N0, I11N1], [I13N0, I13N1], [], [I19N0, I19N1, I19N1], [I23N1], [], [I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
