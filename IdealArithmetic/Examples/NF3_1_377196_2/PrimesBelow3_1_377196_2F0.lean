
import IdealArithmetic.Examples.NF3_1_377196_2.RI3_1_377196_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![391205, 163113, -117488]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![391205, 163113, -117488]] 
 ![![2, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![391205, 163113, -117488], ![-13700471, -548699, 1024303], ![17132550, -809880, -385586]]]
  hmulB := by decide  
  f := ![![![1041133166254, 158045270658, 102611587127]], ![![6653672858949, 1010035566964, 655770034430]], ![![10248175252965, 1555685366775, 1010035566964]]]
  g := ![![![114046, 163113, -117488], ![-6575886, -548699, 1024303], ![8971215, -809880, -385586]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![391205, 163113, -117488]] ![![391205, 163113, -117488]]
  ![![-4094552608598, 69461862618, 166416970167]] where
 M := ![![![-4094552608598, 69461862618, 166416970167]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI2N1 : IdealMulLeCertificate' Table 
  ![![-4094552608598, 69461862618, 166416970167]] ![![391205, 163113, -117488]]
  ![![2, 0, 0]] where
 M := ![![![297677374584162182, -840766190001729516, 488042737285354216]]]
 hmul := by decide  
 g := ![![![![148838687292081091, -420383095000864758, 244021368642677108]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![0, 1, 0]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0], ![0, 1, 0]] 
 ![![3, 0, 0], ![0, 1, 0], ![1, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![0, 1, 0], ![1, 0, 7], ![118, 8, 1]]]
  hmulB := by decide  
  f := ![![![0, 0, -7], ![0, 3, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, -2], ![0, 1, 0]]]
  g := ![![![1, 0, 0], ![0, 3, 0], ![-1, 0, 3]], ![![0, 1, 0], ![-2, 0, 7], ![39, 8, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-1, 1, 0]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![3, 0, 0], ![-1, 1, 0]] 
 ![![3, 0, 0], ![2, 1, 0], ![0, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![-1, 1, 0], ![1, -1, 7], ![118, 8, 0]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]], ![![1, -1, 5], ![1, -2, 0]]]
  g := ![![![1, 0, 0], ![-2, 3, 0], ![0, 0, 3]], ![![-1, 1, 0], ![1, -1, 7], ![34, 8, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![0, 1, 0]] ![![3, 0, 0], ![0, 1, 0]]
  ![![3, 0, 0], ![-5, 0, 1]] where
 M := ![![![9, 0, 0], ![0, 3, 0]], ![![0, 3, 0], ![1, 0, 7]]]
 hmul := by decide  
 g := ![![![![3, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]]], ![![![0, 1, 0], ![0, 0, 0]], ![![2, 0, 2], ![1, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![-5, 0, 1]] ![![3, 0, 0], ![-1, 1, 0]]
  ![![3, 0, 0]] where
 M := ![![![9, 0, 0], ![-3, 3, 0]], ![![-15, 0, 3], ![123, 3, 0]]]
 hmul := by decide  
 g := ![![![![3, 0, 0]], ![![-1, 1, 0]]], ![![![-5, 0, 1]], ![![41, 1, 0]]]]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![0, 1, 0]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![5, 0, 0], ![0, 1, 0]] 
 ![![5, 0, 0], ![0, 1, 0], ![3, 0, 1]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![0, 1, 0], ![1, 0, 7], ![118, 8, 1]]]
  hmulB := by decide  
  f := ![![![0, 0, -7], ![0, 5, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, -4], ![0, 3, 0]]]
  g := ![![![1, 0, 0], ![0, 5, 0], ![-3, 0, 5]], ![![0, 1, 0], ![-4, 0, 7], ![23, 8, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![1, 1, 0]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![5, 0, 0], ![1, 1, 0]] 
 ![![5, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![1, 1, 0], ![1, 1, 7], ![118, 8, 2]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![5, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, 3], ![2, -2, 0]]]
  g := ![![![1, 0, 0], ![-1, 5, 0], ![0, 0, 5]], ![![0, 1, 0], ![0, 1, 7], ![22, 8, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1

def I5N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-2, 1, 0]] i)))

def SI5N2: IdealEqSpanCertificate' Table ![![5, 0, 0], ![-2, 1, 0]] 
 ![![5, 0, 0], ![3, 1, 0], ![1, 0, 1]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![-2, 1, 0], ![1, -2, 7], ![118, 8, -1]]]
  hmulB := by decide  
  f := ![![![-5, 15, -56], ![5, 40, 0]], ![![-1, 7, -28], ![6, 20, 0]], ![![-1, 3, -11], ![1, 8, 0]]]
  g := ![![![1, 0, 0], ![-3, 5, 0], ![-1, 0, 5]], ![![-1, 1, 0], ![0, -2, 7], ![19, 8, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N2 : Nat.card (O ⧸ I5N2) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N2)

lemma isPrimeI5N2 : Ideal.IsPrime I5N2 := prime_ideal_of_norm_prime hp5.out _ NI5N2
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![5, 0, 0], ![0, 1, 0]] ![![5, 0, 0], ![1, 1, 0]]
  ![![5, 0, 0], ![-7, -2, 1]] where
 M := ![![![25, 0, 0], ![5, 5, 0]], ![![0, 5, 0], ![1, 1, 7]]]
 hmul := by decide  
 g := ![![![![5, 0, 0], ![0, 0, 0]], ![![1, 1, 0], ![0, 0, 0]]], ![![![0, 1, 0], ![0, 0, 0]], ![![3, 1, 1], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI5N1 : IdealMulLeCertificate' Table 
  ![![5, 0, 0], ![-7, -2, 1]] ![![5, 0, 0], ![-2, 1, 0]]
  ![![5, 0, 0]] where
 M := ![![![25, 0, 0], ![-10, 5, 0]], ![![-35, -10, 5], ![130, 5, -15]]]
 hmul := by decide  
 g := ![![![![5, 0, 0]], ![![-2, 1, 0]]], ![![![-7, -2, 1]], ![![26, 1, -3]]]]
 hle2 := by decide  


def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N1, I5N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N1
    exact isPrimeI5N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0 ⊙ MulI5N1)

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![1, 1, 0]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0], ![1, 1, 0]] 
 ![![7, 0, 0], ![1, 1, 0], ![6, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![1, 1, 0], ![1, 1, 7], ![118, 8, 2]]]
  hmulB := by decide  
  f := ![![![463, 22, 8], ![70, 0, -28]], ![![0, 0, 0], ![1, 0, 0]], ![![396, 18, 7], ![66, 0, -24]]]
  g := ![![![1, 0, 0], ![-1, 7, 0], ![-6, 0, 7]], ![![0, 1, 0], ![-6, 1, 7], ![14, 8, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N0)

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := prime_ideal_of_norm_prime hp7.out _ NI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![-1, 1, 0]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![7, 0, 0], ![-1, 1, 0]] 
 ![![7, 0, 0], ![6, 1, 0], ![0, 0, 7]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![-1, 1, 0], ![1, -1, 7], ![118, 8, 0]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]], ![![0, 0, 1], ![0, 0, 0]]]
  g := ![![![1, 0, 0], ![-6, 7, 0], ![0, 0, 1]], ![![-1, 1, 0], ![1, -1, 1], ![10, 8, 0]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P1 : CertificateIrreducibleZModOfList' 7 2 2 2 [6, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 6], [0, 1]]
 g := ![![[1, 4], [1, 1]], ![[5, 3], [2, 6]]]
 h' := ![![[1, 6], [1, 2], [0, 1]], ![[0, 1], [3, 5], [1, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [3, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N1 : CertifiedPrimeIdeal' SI7N1 7 where
  n := 2
  hpos := by decide
  P := [6, 6, 1]
  hirr := P7P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3004, 3550, 1918]
  a := ![2, -2, 15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3472, 3550, 274]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N1 B_one_repr
lemma NI7N1 : Nat.card (O ⧸ I7N1) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![7, 0, 0], ![1, 1, 0]] ![![7, 0, 0], ![-1, 1, 0]]
  ![![7, 0, 0]] where
 M := ![![![49, 0, 0], ![-7, 7, 0]], ![![7, 7, 0], ![0, 0, 7]]]
 hmul := by decide  
 g := ![![![![7, 0, 0]], ![![-1, 1, 0]]], ![![![1, 1, 0]], ![![0, 0, 1]]]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-293331, -44528, -28910]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![-293331, -44528, -28910]] 
 ![![11, 0, 0], ![0, 1, 0], ![8, 0, 1]] where
  M :=![![![-293331, -44528, -28910], ![-3455908, -524611, -340606], ![-5774684, -876604, -569139]]]
  hmulB := by decide  
  f := ![![![2095, -248, 42]], ![![428, 221, -154]], ![![-1068, -292, 229]]]
  g := ![![![-5641, -44528, -28910], ![-66460, -524611, -340606], ![-111052, -876604, -569139]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N0 : Nat.card (O ⧸ I11N0) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N0)

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := prime_ideal_of_norm_prime hp11.out _ NI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13241, -2010, -1305]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![-13241, -2010, -1305]] 
 ![![11, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![-13241, -2010, -1305], ![-156000, -23681, -15375], ![-260670, -39570, -25691]]]
  hmulB := by decide  
  f := ![![![179, 60, -45]], ![![-461, -11, 30]], ![![570, -30, -11]]]
  g := ![![![-1021, -2010, -1305], ![-12029, -23681, -15375], ![-20100, -39570, -25691]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1

def I11N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![176395, 14248, -17487]] i)))

def SI11N2: IdealEqSpanCertificate' Table ![![176395, 14248, -17487]] 
 ![![11, 0, 0], ![9, 1, 0], ![9, 0, 1]] where
  M :=![![![176395, 14248, -17487], ![-2049218, 36499, 82249], ![1366498, -200782, 50747]]]
  hmulB := by decide  
  f := ![![![18366333471, 2788031578, 1810141765]], ![![34698341917, 5267250163, 3419785336]], ![![47897025383, 7270826236, 4720615914]]]
  g := ![![![18686, 14248, -17487], ![-283450, 36499, 82249], ![246983, -200782, 50747]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N2 : Nat.card (O ⧸ I11N2) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N2)

lemma isPrimeI11N2 : Ideal.IsPrime I11N2 := prime_ideal_of_norm_prime hp11.out _ NI11N2
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![-293331, -44528, -28910]] ![![-13241, -2010, -1305]]
  ![![18366333471, 2788031578, 1810141765]] where
 M := ![![![18366333471, 2788031578, 1810141765]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI11N1 : IdealMulLeCertificate' Table 
  ![![18366333471, 2788031578, 1810141765]] ![![176395, 14248, -17487]]
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


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [5, 8, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 8, 11], [10, 4, 2], [0, 1]]
 g := ![![[5, 4, 3], [11, 4], [1]], ![[3, 11, 3, 6], [7, 12], [0, 1, 8, 5]], ![[11, 9, 3, 8], [8, 10], [7, 10, 6, 8]]]
 h' := ![![[1, 8, 11], [9, 11, 4], [8, 5, 11], [0, 1]], ![[10, 4, 2], [5, 0, 7], [1, 6, 8], [1, 8, 11]], ![[0, 1], [8, 2, 2], [3, 2, 7], [10, 4, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 4], []]
 b := ![[], [11, 10, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [5, 8, 2, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-135645534843, -17708051426, -6157011874]
  a := ![-65, 1, -391]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10434271911, -1362157802, -473616298]
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


def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![-8, 1, 0]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0], ![-8, 1, 0]] 
 ![![17, 0, 0], ![9, 1, 0], ![8, 0, 1]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]], ![![-8, 1, 0], ![1, -8, 7], ![118, 8, -7]]]
  hmulB := by decide  
  f := ![![![-7, 190, -168], ![34, 408, 0]], ![![-3, 95, -84], ![18, 204, 0]], ![![0, 89, -79], ![23, 192, 0]]]
  g := ![![![1, 0, 0], ![-9, 17, 0], ![-8, 0, 17]], ![![-1, 1, 0], ![1, -8, 7], ![6, 8, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N0 : Nat.card (O ⧸ I17N0) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N0)

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := prime_ideal_of_norm_prime hp17.out _ NI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![-2, 1, 0]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![17, 0, 0], ![-2, 1, 0]] 
 ![![17, 0, 0], ![15, 1, 0], ![2, 0, 1]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]], ![![-2, 1, 0], ![1, -2, 7], ![118, 8, -1]]]
  hmulB := by decide  
  f := ![![![-91, 190, -672], ![34, 1632, 0]], ![![-79, 166, -588], ![35, 1428, 0]], ![![-10, 22, -79], ![10, 192, 0]]]
  g := ![![![1, 0, 0], ![-15, 17, 0], ![-2, 0, 17]], ![![-1, 1, 0], ![1, -2, 7], ![0, 8, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![17, 0, 0], ![-8, 1, 0]] ![![17, 0, 0], ![-8, 1, 0]]
  ![![17, 0, 0], ![2, 5, 1]] where
 M := ![![![289, 0, 0], ![-136, 17, 0]], ![![-136, 17, 0], ![65, -16, 7]]]
 hmul := by decide  
 g := ![![![![15, -5, -1], ![17, 0, 0]], ![![-8, 1, 0], ![0, 0, 0]]], ![![![-8, 1, 0], ![0, 0, 0]], ![![3, -3, 0], ![7, 0, 0]]]]
 hle2 := by decide  
def MulI17N1 : IdealMulLeCertificate' Table 
  ![![17, 0, 0], ![2, 5, 1]] ![![17, 0, 0], ![-2, 1, 0]]
  ![![17, 0, 0]] where
 M := ![![![289, 0, 0], ![-34, 17, 0]], ![![34, 85, 17], ![119, 0, 34]]]
 hmul := by decide  
 g := ![![![![17, 0, 0]], ![![-2, 1, 0]]], ![![![2, 5, 1]], ![![7, 0, 2]]]]
 hle2 := by decide  


def PBC17 : ContainsPrimesAboveP 17 ![I17N0, I17N0, I17N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N0
    exact isPrimeI17N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 17 (by decide) (𝕀 ⊙ MulI17N0 ⊙ MulI17N1)
instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0]] 
 ![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 3 2 4 [13, 6, 17, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 16, 5], [5, 2, 14], [0, 1]]
 g := ![![[9, 7, 5], [9, 13, 4], [2, 1], []], ![[12, 13, 1, 11], [7, 3, 13, 4], [10, 4], [1, 6]], ![[15, 6, 8, 15], [2, 2, 14, 18], [2, 9], [11, 6]]]
 h' := ![![[16, 16, 5], [16, 16, 10], [12, 13, 17], [0, 0, 1], [0, 1]], ![[5, 2, 14], [4, 14, 5], [0, 17, 4], [15, 10, 2], [16, 16, 5]], ![[0, 1], [18, 8, 4], [9, 8, 17], [15, 9, 16], [5, 2, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 17], []]
 b := ![[], [7, 0, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 3
  hpos := by decide
  P := [13, 6, 17, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7004312, -880403, -229311]
  a := ![-2, 1, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-368648, -46337, -12069]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 6859 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def PBC19 : ContainsPrimesAboveP 19 ![I19N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![19, 0, 0]]) timesTableT_eq_Table B_one_repr 19 (by decide) 𝕀

instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![3, 1, 0]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0], ![3, 1, 0]] 
 ![![23, 0, 0], ![3, 1, 0], ![12, 0, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![3, 1, 0], ![1, 3, 7], ![118, 8, 4]]]
  hmulB := by decide  
  f := ![![![-108, -335, -784], ![-23, 2576, 0]], ![![-14, -42, -98], ![1, 322, 0]], ![![-57, -175, -409], ![-7, 1344, 0]]]
  g := ![![![1, 0, 0], ![-3, 23, 0], ![-12, 0, 23]], ![![0, 1, 0], ![-4, 3, 7], ![2, 8, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N0 : Nat.card (O ⧸ I23N0) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N0)

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := prime_ideal_of_norm_prime hp23.out _ NI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![5, 1, 0]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![23, 0, 0], ![5, 1, 0]] 
 ![![23, 0, 0], ![5, 1, 0], ![13, 0, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![5, 1, 0], ![1, 5, 7], ![118, 8, 6]]]
  hmulB := by decide  
  f := ![![![-231, -1256, -1764], ![-92, 5796, 0]], ![![-49, -269, -378], ![-22, 1242, 0]], ![![-131, -710, -997], ![-50, 3276, 0]]]
  g := ![![![1, 0, 0], ![-5, 23, 0], ![-13, 0, 23]], ![![0, 1, 0], ![-5, 5, 7], ![0, 8, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1

def I23N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![-9, 1, 0]] i)))

def SI23N2: IdealEqSpanCertificate' Table ![![23, 0, 0], ![-9, 1, 0]] 
 ![![23, 0, 0], ![14, 1, 0], ![5, 0, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![-9, 1, 0], ![1, -9, 7], ![118, 8, -8]]]
  hmulB := by decide  
  f := ![![![-15, 224, -175], ![23, 575, 0]], ![![-5, 134, -105], ![24, 345, 0]], ![![3, 48, -38], ![21, 125, 0]]]
  g := ![![![1, 0, 0], ![-14, 23, 0], ![-5, 0, 23]], ![![-1, 1, 0], ![4, -9, 7], ![2, 8, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N2 : Nat.card (O ⧸ I23N2) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N2)

lemma isPrimeI23N2 : Ideal.IsPrime I23N2 := prime_ideal_of_norm_prime hp23.out _ NI23N2
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![23, 0, 0], ![3, 1, 0]] ![![23, 0, 0], ![5, 1, 0]]
  ![![23, 0, 0], ![-1, 11, 1]] where
 M := ![![![529, 0, 0], ![115, 23, 0]], ![![69, 23, 0], ![16, 8, 7]]]
 hmul := by decide  
 g := ![![![![23, 0, 0], ![0, 0, 0]], ![![6, -10, -1], ![23, 0, 0]]], ![![![4, -10, -1], ![23, 0, 0]], ![![1, -3, 0], ![7, 0, 0]]]]
 hle2 := by decide  

def MulI23N1 : IdealMulLeCertificate' Table 
  ![![23, 0, 0], ![-1, 11, 1]] ![![23, 0, 0], ![-9, 1, 0]]
  ![![23, 0, 0]] where
 M := ![![![529, 0, 0], ![-207, 23, 0]], ![![-23, 253, 23], ![138, -92, 69]]]
 hmul := by decide  
 g := ![![![![23, 0, 0]], ![![-9, 1, 0]]], ![![![-1, 11, 1]], ![![6, -4, 3]]]]
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

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0]] 
 ![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 3 2 4 [5, 25, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 12, 26], [21, 16, 3], [0, 1]]
 g := ![![[10, 1, 22], [14, 5], [16], [1]], ![[4, 10, 25, 12], [1, 6], [24, 4, 22, 3], [10, 1, 5, 2]], ![[18, 5, 22, 11], [17, 13], [5, 5, 10, 26], [21, 21, 26, 27]]]
 h' := ![![[8, 12, 26], [8, 1, 15], [7, 2, 18], [24, 4], [0, 1]], ![[21, 16, 3], [25, 14, 5], [28, 9, 21], [27, 19, 17], [8, 12, 26]], ![[0, 1], [24, 14, 9], [14, 18, 19], [21, 6, 12], [21, 16, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 27], []]
 b := ![[], [6, 26, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 3
  hpos := by decide
  P := [5, 25, 0, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-930436, -116551, -56637]
  a := ![-1, -1, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-32084, -4019, -1953]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![-2, -8, 1]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0], ![-2, -8, 1]] 
 ![![31, 0, 0], ![0, 31, 0], ![29, 23, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![-2, -8, 1], ![110, 6, -55], ![-926, -46, -2]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-29, -23, 31]], ![![-1, -1, 1], ![55, 41, -55], ![-28, 0, -2]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [7, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 30], [0, 1]]
 g := ![![[0, 9], [0, 4], [0, 18], [0, 1]], ![[0, 22], [0, 27], [0, 13], [0, 30]]]
 h' := ![![[0, 30], [0, 3], [0, 29], [0, 24], [0, 1]], ![[0, 1], [0, 28], [0, 2], [0, 7], [0, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [0, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [7, 0, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![61706, 7070, 4425]
  a := ![2, 19, 13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2149, -3055, 4425]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![-7, 1, 0]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![31, 0, 0], ![-7, 1, 0]] 
 ![![31, 0, 0], ![24, 1, 0], ![2, 0, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![-7, 1, 0], ![1, -7, 7], ![118, 8, -6]]]
  hmulB := by decide  
  f := ![![![-294, 2305, -2310], ![155, 10230, 0]], ![![-226, 1781, -1785], ![125, 7905, 0]], ![![-14, 148, -149], ![32, 660, 0]]]
  g := ![![![1, 0, 0], ![-24, 31, 0], ![-2, 0, 31]], ![![-1, 1, 0], ![5, -7, 7], ![-2, 8, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![31, 0, 0], ![-2, -8, 1]] ![![31, 0, 0], ![-7, 1, 0]]
  ![![31, 0, 0]] where
 M := ![![![961, 0, 0], ![-217, 31, 0]], ![![-62, -248, 31], ![124, 62, -62]]]
 hmul := by decide  
 g := ![![![![31, 0, 0]], ![![-7, 1, 0]]], ![![![-2, -8, 1]], ![![4, 2, -2]]]]
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


lemma PB174I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB174I0 : PrimesBelowBoundCertificateInterval O 1 31 174 where
  m := 11
  g := ![3, 3, 3, 2, 3, 1, 3, 1, 3, 1, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB174I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N0, I2N0]
    · exact ![I3N0, I3N0, I3N1]
    · exact ![I5N0, I5N1, I5N2]
    · exact ![I7N0, I7N1]
    · exact ![I11N0, I11N1, I11N2]
    · exact ![I13N0]
    · exact ![I17N0, I17N0, I17N1]
    · exact ![I19N0]
    · exact ![I23N0, I23N1, I23N2]
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
    · exact ![5, 5, 5]
    · exact ![7, 49]
    · exact ![11, 11, 11]
    · exact ![2197]
    · exact ![17, 17, 17]
    · exact ![6859]
    · exact ![23, 23, 23]
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
      exact NI2N0
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N0
      exact NI3N1
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N1
      exact NI5N2
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
      exact NI17N0
      exact NI17N1
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
      exact NI23N2
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
  β := ![I2N0, I3N0, I3N1, I5N0, I5N1, I5N2, I7N0, I7N1, I11N0, I11N1, I11N2, I17N0, I17N1, I23N0, I23N1, I23N2, I31N1]
  Il := ![[I2N0, I2N0, I2N0], [I3N0, I3N0, I3N1], [I5N0, I5N1, I5N2], [I7N0, I7N1], [I11N0, I11N1, I11N2], [], [I17N0, I17N0, I17N1], [], [I23N0, I23N1, I23N2], [], [I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
