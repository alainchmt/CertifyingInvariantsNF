
import IdealArithmetic.Examples.NF3_3_109384_1.RI3_3_109384_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-172, 2, 7]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![-172, 2, 7]] 
 ![![2, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![-172, 2, 7], ![-271, 3, 11], ![-127, 1, 5]]]
  hmulB := by decide  
  f := ![![![-4, 3, -1]], ![![19, -13, 2]], ![![-55, 41, -13]]]
  g := ![![![-87, 2, 7], ![-137, 3, 11], ![-64, 1, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9, -2, 1]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![-9, -2, 1]] 
 ![![2, 0, 0], ![1, 1, 0], ![1, 0, 1]] where
  M :=![![![-9, -2, 1], ![-41, 16, -3], ![71, -57, 14]]]
  hmulB := by decide  
  f := ![![![53, -29, -10]], ![![207, -113, -39]], ![![627, -342, -118]]]
  g := ![![![-4, -2, 1], ![-27, 16, -3], ![57, -57, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![-172, 2, 7]] ![![-9, -2, 1]]
  ![![1963, -23, -80]] where
 M := ![![![1963, -23, -80]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![1963, -23, -80]] ![![-9, -2, 1]]
  ![![2, 0, 0]] where
 M := ![![![-22404, 266, 912]]]
 hmul := by decide  
 g := ![![![![-11202, 133, 456]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N1, I2N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
    exact isPrimeI2N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1)
instance hp3 : Fact (Nat.Prime 3) := {out := by norm_num}

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0]] 
 ![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P3P0 : CertificateIrreducibleZModOfList' 3 3 2 1 [2, 2, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 1, 1], [0, 1, 2], [0, 1]]
 g := ![![[1]], ![[2, 2, 1, 1]], ![[0, 1, 2, 2]]]
 h' := ![![[1, 1, 1], [0, 1]], ![[0, 1, 2], [1, 1, 1]], ![[0, 1], [0, 1, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 2], []]
 b := ![[], [1, 2, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : CertifiedPrimeIdeal' SI3N0 3 where
  n := 3
  hpos := by decide
  P := [2, 2, 2, 1]
  hirr := P3P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11346, -4656, -5436]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3782, -1552, -1812]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N0 B_one_repr
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 27 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N0

def PBC3 : ContainsPrimesAboveP 3 ![I3N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![3, 0, 0]]) timesTableT_eq_Table B_one_repr 3 (by decide) 𝕀

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


def P5P0 : CertificateIrreducibleZModOfList' 5 3 2 2 [1, 0, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 1, 3], [0, 3, 2], [0, 1]]
 g := ![![[1, 4, 1], []], ![[4, 1, 4, 2], [2, 4]], ![[0, 1, 0, 2], [3, 4]]]
 h' := ![![[4, 1, 3], [0, 0, 1], [0, 1]], ![[0, 3, 2], [4, 4, 3], [4, 1, 3]], ![[0, 1], [2, 1, 1], [0, 3, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 3], []]
 b := ![[], [2, 3, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where
  n := 3
  hpos := by decide
  P := [1, 0, 1, 1]
  hirr := P5P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![163610, -142455, 82140]
  a := ![2, -2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![32722, -28491, 16428]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, -6, -2]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![11, -6, -2]] 
 ![![7, 0, 0], ![3, 1, 0], ![3, 0, 1]] where
  M :=![![![11, -6, -2], ![72, -39, -14], ![248, -136, -45]]]
  hmulB := by decide  
  f := ![![![149, -2, -6]], ![![97, -1, -4]], ![![81, -2, -3]]]
  g := ![![![5, -6, -2], ![33, -39, -14], ![113, -136, -45]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N0)

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := prime_ideal_of_norm_prime hp7.out _ NI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-46, 1, 2]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![-46, 1, 2]] 
 ![![7, 0, 0], ![4, 1, 0], ![3, 0, 1]] where
  M :=![![![-46, 1, 2], ![-77, 4, 4], ![-53, 11, 5]]]
  hmulB := by decide  
  f := ![![![-24, 17, -4]], ![![11, -8, 2]], ![![-101, 72, -17]]]
  g := ![![![-8, 1, 2], ![-15, 4, 4], ![-16, 11, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1

def I7N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-16, 9, -2]] i)))

def SI7N2: IdealEqSpanCertificate' Table ![![-16, 9, -2]] 
 ![![7, 0, 0], ![6, 1, 0], ![0, 0, 1]] where
  M :=![![![-16, 9, -2], ![87, -66, 16], ![-337, 239, -57]]]
  hmulB := by decide  
  f := ![![![62, -35, -12]], ![![115, -64, -22]], ![![207, -113, -39]]]
  g := ![![![-10, 9, -2], ![69, -66, 16], ![-253, 239, -57]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N2 : Nat.card (O ⧸ I7N2) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N2)

lemma isPrimeI7N2 : Ideal.IsPrime I7N2 := prime_ideal_of_norm_prime hp7.out _ NI7N2
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![11, -6, -2]] ![![-46, 1, 2]]
  ![![62, -35, -12]] where
 M := ![![![62, -35, -12]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI7N1 : IdealMulLeCertificate' Table 
  ![![62, -35, -12]] ![![-16, 9, -2]]
  ![![7, 0, 0]] where
 M := ![![![7, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N1, I7N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N1
    exact isPrimeI7N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0 ⊙ MulI7N1)

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![52, -1, -2]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![52, -1, -2]] 
 ![![11, 0, 0], ![7, 1, 0], ![9, 0, 1]] where
  M :=![![![52, -1, -2], ![77, 2, -4], ![53, -11, 1]]]
  hmulB := by decide  
  f := ![![![-42, 23, 8]], ![![-53, 29, 10]], ![![-121, 66, 23]]]
  g := ![![![7, -1, -2], ![9, 2, -4], ![11, -11, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N0 : Nat.card (O ⧸ I11N0) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N0)

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := prime_ideal_of_norm_prime hp11.out _ NI11N0
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![52, -1, -2]] ![![52, -1, -2]]
  ![![2521, -32, -102]] where
 M := ![![![2521, -32, -102]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI11N1 : IdealMulLeCertificate' Table 
  ![![2521, -32, -102]] ![![52, -1, -2]]
  ![![11, 0, 0]] where
 M := ![![![123222, -1463, -5016]]]
 hmul := by decide  
 g := ![![![![11202, -133, -456]]]]
 hle2 := by decide  

def PBC11 : ContainsPrimesAboveP 11 ![I11N0, I11N0, I11N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
    exact isPrimeI11N0
    exact isPrimeI11N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 11 (by decide) (𝕀 ⊙ MulI11N0 ⊙ MulI11N1)
instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-957, 666, -158]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![-957, 666, -158]] 
 ![![13, 0, 0], ![0, 13, 0], ![4, 5, 1]] where
  M :=![![![-957, 666, -158], ![6828, -4907, 1174], ![-24868, 17756, -4241]]]
  hmulB := by decide  
  f := ![![![-2689, 1466, 506]], ![![-18268, 9961, 3438]], ![![-12524, 6829, 2357]]]
  g := ![![![-25, 112, -158], ![164, -829, 1174], ![-608, 2997, -4241]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [2, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 12], [0, 1]]
 g := ![![[], [4], [0, 1]], ![[], [4], [0, 12]]]
 h' := ![![[0, 12], [5], [0, 11], [0, 1]], ![[0, 1], [5], [0, 2], [0, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [0, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 2
  hpos := by decide
  P := [2, 0, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-21116, -33922, 117350]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-37732, -47744, 117350]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-378, 275, -66]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![-378, 275, -66]] 
 ![![13, 0, 0], ![2, 1, 0], ![5, 0, 1]] where
  M :=![![![-378, 275, -66], ![2849, -2028, 484], ![-10263, 7337, -1753]]]
  hmulB := by decide  
  f := ![![![3976, -2167, -748]], ![![2689, -1466, -506]], ![![8433, -4598, -1587]]]
  g := ![![![-46, 275, -66], ![345, -2028, 484], ![-1244, 7337, -1753]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![-957, 666, -158]] ![![-378, 275, -66]]
  ![![13, 0, 0]] where
 M := ![![![3880734, -2773069, 662480]]]
 hmul := by decide  
 g := ![![![![298518, -213313, 50960]]]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, -10, 2]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![23, -10, 2]] 
 ![![17, 0, 0], ![0, 17, 0], ![3, 12, 1]] where
  M :=![![![23, -10, 2], ![-88, 73, -18], ![376, -264, 63]]]
  hmulB := by decide  
  f := ![![![-9, 6, 2]], ![![-72, 41, 14]], ![![-67, 38, 13]]]
  g := ![![![1, -2, 2], ![-2, 17, -18], ![11, -60, 63]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 2 2 4 [14, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 16], [0, 1]]
 g := ![![[8, 8], [2], [15], [1]], ![[13, 9], [2], [15], [1]]]
 h' := ![![[7, 16], [15, 12], [3, 11], [3, 7], [0, 1]], ![[0, 1], [14, 5], [12, 6], [1, 10], [7, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [16, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 2
  hpos := by decide
  P := [14, 10, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![214, -419, 587]
  a := ![-2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-91, -439, 587]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9, 6, 2]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![-9, 6, 2]] 
 ![![17, 0, 0], ![9, 1, 0], ![11, 0, 1]] where
  M :=![![![-9, 6, 2], ![-72, 41, 14], ![-248, 136, 47]]]
  hmulB := by decide  
  f := ![![![23, -10, 2]], ![![7, -1, 0]], ![![37, -22, 5]]]
  g := ![![![-5, 6, 2], ![-35, 41, 14], ![-117, 136, 47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![23, -10, 2]] ![![-9, 6, 2]]
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
instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-115, 64, 22]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![-115, 64, 22]] 
 ![![19, 0, 0], ![6, 1, 0], ![11, 0, 1]] where
  M :=![![![-115, 64, 22], ![-794, 435, 150], ![-2650, 1446, 499]]]
  hmulB := by decide  
  f := ![![![-165, 124, -30]], ![![16, -9, 2]], ![![-339, 246, -59]]]
  g := ![![![-39, 64, 22], ![-266, 435, 150], ![-885, 1446, 499]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N0 : Nat.card (O ⧸ I19N0) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N0)

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := prime_ideal_of_norm_prime hp19.out _ NI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 13, -4]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![2, 13, -4]] 
 ![![19, 0, 0], ![14, 1, 0], ![7, 0, 1]] where
  M :=![![![2, 13, -4], ![169, -98, 22], ![-479, 353, -85]]]
  hmulB := by decide  
  f := ![![![564, -307, -106]], ![![617, -336, -116]], ![![877, -478, -165]]]
  g := ![![![-8, 13, -4], ![73, -98, 22], ![-254, 353, -85]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1

def I19N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, -1, 0]] i)))

def SI19N2: IdealEqSpanCertificate' Table ![![2, -1, 0]] 
 ![![19, 0, 0], ![17, 1, 0], ![8, 0, 1]] where
  M :=![![![2, -1, 0], ![-1, 2, -2], ![39, -25, 1]]]
  hmulB := by decide  
  f := ![![![48, -1, -2]], ![![47, -1, -2]], ![![23, -1, -1]]]
  g := ![![![1, -1, 0], ![-1, 2, -2], ![24, -25, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N2 : Nat.card (O ⧸ I19N2) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N2)

lemma isPrimeI19N2 : Ideal.IsPrime I19N2 := prime_ideal_of_norm_prime hp19.out _ NI19N2
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![-115, 64, 22]] ![![2, 13, -4]]
  ![![48, -1, -2]] where
 M := ![![![48, -1, -2]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI19N1 : IdealMulLeCertificate' Table 
  ![![48, -1, -2]] ![![2, -1, 0]]
  ![![19, 0, 0]] where
 M := ![![![19, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC19 : ContainsPrimesAboveP 19 ![I19N0, I19N1, I19N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N1
    exact isPrimeI19N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 19 (by decide) (𝕀 ⊙ MulI19N0 ⊙ MulI19N1)
instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-72, -17, -2]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![-72, -17, -2]] 
 ![![23, 0, 0], ![0, 23, 0], ![13, 20, 1]] where
  M :=![![![-72, -17, -2], ![61, -122, -36], ![677, -411, -139]]]
  hmulB := by decide  
  f := ![![![-94, 67, -16]], ![![691, -494, 118]], ![![439, -314, 75]]]
  g := ![![![-2, 1, -2], ![23, 26, -36], ![108, 103, -139]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [18, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 22], [0, 1]]
 g := ![![[20, 9], [14, 4], [17, 18], [1]], ![[0, 14], [0, 19], [0, 5], [1]]]
 h' := ![![[8, 22], [1, 20], [16, 21], [5, 8], [0, 1]], ![[0, 1], [0, 3], [0, 2], [0, 15], [8, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [22, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 2
  hpos := by decide
  P := [18, 15, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-179, 59, 80]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-53, -67, 80]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![94, -67, 16]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![94, -67, 16]] 
 ![![23, 0, 0], ![5, 1, 0], ![11, 0, 1]] where
  M :=![![![94, -67, 16], ![-691, 494, -118], ![2501, -1787, 427]]]
  hmulB := by decide  
  f := ![![![72, 17, 2]], ![![13, 9, 2]], ![![5, 26, 7]]]
  g := ![![![11, -67, 16], ![-81, 494, -118], ![293, -1787, 427]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![-72, -17, -2]] ![![94, -67, 16]]
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

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, -8, 2]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![11, -8, 2]] 
 ![![29, 0, 0], ![4, 1, 0], ![7, 0, 1]] where
  M :=![![![11, -8, 2], ![-86, 61, -14], ![298, -214, 53]]]
  hmulB := by decide  
  f := ![![![-237, 4, 10]], ![![-46, 1, 2]], ![![-65, 2, 3]]]
  g := ![![![1, -8, 2], ![-8, 61, -14], ![27, -214, 53]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N0 : Nat.card (O ⧸ I29N0) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N0)

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := prime_ideal_of_norm_prime hp29.out _ NI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, -142, 34]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![197, -142, 34]] 
 ![![29, 0, 0], ![11, 1, 0], ![27, 0, 1]] where
  M :=![![![197, -142, 34], ![-1468, 1047, -250], ![5300, -3788, 905]]]
  hmulB := by decide  
  f := ![![![-535, 282, 98]], ![![-325, 173, 60]], ![![-901, 482, 167]]]
  g := ![![![29, -142, 34], ![-215, 1047, -250], ![777, -3788, 905]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1

def I29N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, 2, 0]] i)))

def SI29N2: IdealEqSpanCertificate' Table ![![-3, 2, 0]] 
 ![![29, 0, 0], ![13, 1, 0], ![3, 0, 1]] where
  M :=![![![-3, 2, 0], ![2, -3, 4], ![-78, 50, -1]]]
  hmulB := by decide  
  f := ![![![197, -2, -8]], ![![99, -1, -4]], ![![25, 0, -1]]]
  g := ![![![-1, 2, 0], ![1, -3, 4], ![-25, 50, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N2 : Nat.card (O ⧸ I29N2) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N2)

lemma isPrimeI29N2 : Ideal.IsPrime I29N2 := prime_ideal_of_norm_prime hp29.out _ NI29N2
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![11, -8, 2]] ![![197, -142, 34]]
  ![![24511, -17514, 4184]] where
 M := ![![![24511, -17514, 4184]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI29N1 : IdealMulLeCertificate' Table 
  ![![24511, -17514, 4184]] ![![-3, 2, 0]]
  ![![29, 0, 0]] where
 M := ![![![-434913, 310764, -74240]]]
 hmul := by decide  
 g := ![![![![-14997, 10716, -2560]]]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0]] 
 ![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 3 2 4 [21, 30, 11, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [25, 5], [26, 25], [0, 1]]
 g := ![![[18, 4, 20], [22, 29, 2], [29, 11, 28], [1]], ![[1, 29, 4], [13, 25, 19], [10, 18, 18], [1]], ![[2, 29, 7], [20, 8, 10], [23, 2, 16], [1]]]
 h' := ![![[25, 5], [3, 30, 12], [11, 22, 23], [10, 1, 20], [0, 1]], ![[26, 25], [7, 19, 21], [25, 1, 17], [11, 14, 4], [25, 5]], ![[0, 1], [29, 13, 29], [11, 8, 22], [9, 16, 7], [26, 25]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25], []]
 b := ![[], [15, 11, 17], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 3
  hpos := by decide
  P := [21, 30, 11, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1151991, 660920, 219852]
  a := ![2, 19, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-37161, 21320, 7092]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 29791 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def PBC31 : ContainsPrimesAboveP 31 ![I31N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![31, 0, 0]]) timesTableT_eq_Table B_one_repr 31 (by decide) 𝕀



lemma PB74I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB74I0 : PrimesBelowBoundCertificateInterval O 1 31 74 where
  m := 11
  g := ![3, 1, 1, 3, 3, 2, 2, 3, 2, 3, 1]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB74I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1]
    · exact ![I3N0]
    · exact ![I5N0]
    · exact ![I7N0, I7N1, I7N2]
    · exact ![I11N0, I11N0, I11N0]
    · exact ![I13N0, I13N1]
    · exact ![I17N0, I17N1]
    · exact ![I19N0, I19N1, I19N2]
    · exact ![I23N0, I23N1]
    · exact ![I29N0, I29N1, I29N2]
    · exact ![I31N0]
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
    · exact ![27]
    · exact ![125]
    · exact ![7, 7, 7]
    · exact ![11, 11, 11]
    · exact ![169, 13]
    · exact ![289, 17]
    · exact ![19, 19, 19]
    · exact ![529, 23]
    · exact ![29, 29, 29]
    · exact ![29791]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N1
      exact NI2N1
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N1
      exact NI7N2
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N0
      exact NI11N0
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
      exact NI19N1
      exact NI19N2
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
      exact NI29N2
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
  β := ![I2N0, I2N1, I3N0, I7N0, I7N1, I7N2, I11N0, I13N1, I17N1, I19N0, I19N1, I19N2, I23N1, I29N0, I29N1, I29N2]
  Il := ![[I2N0, I2N1, I2N1], [I3N0], [], [I7N0, I7N1, I7N2], [I11N0, I11N0, I11N0], [I13N1], [I17N1], [I19N0, I19N1, I19N2], [I23N1], [I29N0, I29N1, I29N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
