
import IdealArithmetic.Examples.NF3_1_508248_2.RI3_1_508248_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5059, -174, 553]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![-5059, -174, 553]] 
 ![![2, 0, 0], ![0, 1, 0], ![1, 0, 1]] where
  M :=![![![-5059, -174, 553], ![76662, -3195, -2846], ![-54980, 6493, -1946]]]
  hmulB := by decide  
  f := ![![![-24696548, -3252025, -2262039]], ![![-152828666, -20124377, -13998086]], ![![-173400907, -22833316, -15882366]]]
  g := ![![![-2806, -174, 553], ![39754, -3195, -2846], ![-26517, 6493, -1946]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-192404, 14706, 797]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![-192404, 14706, 797]] 
 ![![2, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![-192404, 14706, 797], ![80574, -159804, 145466], ![1984796, 69185, -217831]]]
  hmulB := by decide  
  f := ![![![24746199914, 3258563131, 2266586784]], ![![153135924965, 20164836656, 14026228871]], ![![161376426087, 21249940358, 14781003786]]]
  g := ![![![-96202, 14706, 797], ![40287, -159804, 145466], ![992398, 69185, -217831]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![-5059, -174, 553]] ![![-192404, 14706, 797]]
  ![![2056944148, -8332453, -149803650]] where
 M := ![![![2056944148, -8332453, -149803650]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![2056944148, -8332453, -149803650]] ![![-192404, 14706, 797]]
  ![![2, 0, 0]] where
 M := ![![![-693765346225214, 21216814434450, 33059174761008]]]
 hmul := by decide  
 g := ![![![![-346882673112607, 10608407217225, 16529587380504]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![1, 1, 0]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0], ![1, 1, 0]] 
 ![![3, 0, 0], ![1, 1, 0], ![1, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![1, 1, 0], ![-2, 3, 10], ![138, 4, -1]]]
  hmulB := by decide  
  f := ![![![3, -3, -10], ![0, 3, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![1, -1, -3], ![0, 1, 0]]]
  g := ![![![1, 0, 0], ![-1, 3, 0], ![-1, 0, 3]], ![![0, 1, 0], ![-5, 3, 10], ![45, 4, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![1, 1, 0]] ![![3, 0, 0], ![1, 1, 0]]
  ![![3, 0, 0], ![-4, 1, 1]] where
 M := ![![![9, 0, 0], ![3, 3, 0]], ![![3, 3, 0], ![-1, 4, 10]]]
 hmul := by decide  
 g := ![![![![3, 0, 0], ![0, 0, 0]], ![![1, 1, 0], ![0, 0, 0]]], ![![![1, 1, 0], ![0, 0, 0]], ![![1, 1, 3], ![1, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![-4, 1, 1]] ![![3, 0, 0], ![1, 1, 0]]
  ![![3, 0, 0]] where
 M := ![![![9, 0, 0], ![3, 3, 0]], ![![-12, 3, 3], ![132, 3, 9]]]
 hmul := by decide  
 g := ![![![![3, 0, 0]], ![![1, 1, 0]]], ![![![-4, 1, 1]], ![![44, 1, 3]]]]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![1, 1, 0]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![5, 0, 0], ![1, 1, 0]] 
 ![![5, 0, 0], ![1, 1, 0], ![1, 0, 1]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![1, 1, 0], ![-2, 3, 10], ![138, 4, -1]]]
  hmulB := by decide  
  f := ![![![133, -2, -1], ![30, 0, -5]], ![![0, 0, 0], ![1, 0, 0]], ![![26, -1, 0], ![9, 0, -1]]]
  g := ![![![1, 0, 0], ![-1, 5, 0], ![-1, 0, 5]], ![![0, 1, 0], ![-3, 3, 10], ![27, 4, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![2, 1, 0]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![5, 0, 0], ![2, 1, 0]] 
 ![![5, 0, 0], ![2, 1, 0], ![0, 0, 5]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![2, 1, 0], ![-2, 4, 10], ![138, 4, 0]]]
  hmulB := by decide  
  f := ![![![-1, -1, 0], ![5, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, 1], ![0, 0, 0]]]
  g := ![![![1, 0, 0], ![-2, 5, 0], ![0, 0, 1]], ![![0, 1, 0], ![-2, 4, 2], ![26, 4, 0]]]
  hle1 := by decide   
  hle2 := by decide  


def P5P1 : CertificateIrreducibleZModOfList' 5 2 2 2 [1, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 4], [0, 1]]
 g := ![![[1, 1], [1]], ![[0, 4], [1]]]
 h' := ![![[4, 4], [4, 4], [0, 1]], ![[0, 1], [0, 1], [4, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [2, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N1 : CertifiedPrimeIdeal' SI5N1 5 where
  n := 2
  hpos := by decide
  P := [1, 1, 1]
  hirr := P5P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10969, 2548, 910]
  a := ![-3, 0, 14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3213, 2548, 182]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI5N1 B_one_repr
lemma NI5N1 : Nat.card (O ⧸ I5N1) = 25 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI5N1
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![5, 0, 0], ![1, 1, 0]] ![![5, 0, 0], ![2, 1, 0]]
  ![![5, 0, 0]] where
 M := ![![![25, 0, 0], ![10, 5, 0]], ![![5, 5, 0], ![0, 5, 10]]]
 hmul := by decide  
 g := ![![![![5, 0, 0]], ![![2, 1, 0]]], ![![![1, 1, 0]], ![![0, 1, 2]]]]
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


def P7P0 : CertificateIrreducibleZModOfList' 7 3 2 2 [4, 1, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 4, 3], [5, 2, 4], [0, 1]]
 g := ![![[0, 3, 4], [1]], ![[4, 6], [3, 2, 5, 6]], ![[5, 1, 0, 2], [1, 1, 3, 1]]]
 h' := ![![[0, 4, 3], [3, 6, 5], [0, 1]], ![[5, 2, 4], [2, 3], [0, 4, 3]], ![[0, 1], [2, 5, 2], [5, 2, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2], []]
 b := ![[], [4, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 3
  hpos := by decide
  P := [4, 1, 2, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1219527442, -156784264, -128039842]
  a := ![1, -64, -69]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-174218206, -22397752, -18291406]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![-4, -4, 1]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0], ![-4, -4, 1]] 
 ![![11, 0, 0], ![0, 11, 0], ![7, 7, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![-4, -4, 1], ![146, -8, -42], ![-608, -3, 9]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-7, -7, 11]], ![![-1, -1, 1], ![40, 26, -42], ![-61, -6, 9]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [3, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 10], [0, 1]]
 g := ![![[1, 4], [2, 9], [1]], ![[0, 7], [8, 2], [1]]]
 h' := ![![[8, 10], [5, 9], [8, 8], [0, 1]], ![[0, 1], [0, 2], [6, 3], [8, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [1, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 2
  hpos := by decide
  P := [3, 3, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7093, 2653, 808]
  a := ![3, -1, -14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1159, -273, 808]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![-2, 1, 0]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![11, 0, 0], ![-2, 1, 0]] 
 ![![11, 0, 0], ![9, 1, 0], ![2, 0, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![-2, 1, 0], ![-2, 0, 10], ![138, 4, -4]]]
  hmulB := by decide  
  f := ![![![-95, -2, 500], ![22, -550, 0]], ![![-75, -2, 400], ![23, -440, 0]], ![![-16, -1, 91], ![11, -100, 0]]]
  g := ![![![1, 0, 0], ![-9, 11, 0], ![-2, 0, 11]], ![![-1, 1, 0], ![-2, 0, 10], ![10, 4, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![11, 0, 0], ![-4, -4, 1]] ![![11, 0, 0], ![-2, 1, 0]]
  ![![11, 0, 0]] where
 M := ![![![121, 0, 0], ![-22, 11, 0]], ![![-44, -44, 11], ![154, 0, -44]]]
 hmul := by decide  
 g := ![![![![11, 0, 0]], ![![-2, 1, 0]]], ![![![-4, -4, 1]], ![![14, 0, -4]]]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![2, 1, 0]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0], ![2, 1, 0]] 
 ![![13, 0, 0], ![2, 1, 0], ![12, 0, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![2, 1, 0], ![-2, 4, 10], ![138, 4, 0]]]
  hmulB := by decide  
  f := ![![![69, -141, -350], ![13, 455, 0]], ![![10, -20, -50], ![1, 65, 0]], ![![64, -130, -323], ![10, 420, 0]]]
  g := ![![![1, 0, 0], ![-2, 13, 0], ![-12, 0, 13]], ![![0, 1, 0], ![-10, 4, 10], ![10, 4, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N0 : Nat.card (O ⧸ I13N0) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N0)

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := prime_ideal_of_norm_prime hp13.out _ NI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![-1, 1, 0]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![13, 0, 0], ![-1, 1, 0]] 
 ![![13, 0, 0], ![12, 1, 0], ![9, 0, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![-1, 1, 0], ![-2, 1, 10], ![138, 4, -3]]]
  hmulB := by decide  
  f := ![![![25, -12, -120], ![0, 156, 0]], ![![23, -11, -110], ![1, 143, 0]], ![![18, -9, -83], ![9, 108, 0]]]
  g := ![![![1, 0, 0], ![-12, 13, 0], ![-9, 0, 13]], ![![-1, 1, 0], ![-8, 1, 10], ![9, 4, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![13, 0, 0], ![2, 1, 0]] ![![13, 0, 0], ![-1, 1, 0]]
  ![![13, 0, 0], ![-3, -1, 1]] where
 M := ![![![169, 0, 0], ![-13, 13, 0]], ![![26, 13, 0], ![-4, 3, 10]]]
 hmul := by decide  
 g := ![![![![13, 0, 0], ![0, 0, 0]], ![![2, 2, -1], ![13, 0, 0]]], ![![![2, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![10, 0, 0]]]]
 hle2 := by decide  

def MulI13N1 : IdealMulLeCertificate' Table 
  ![![13, 0, 0], ![-3, -1, 1]] ![![13, 0, 0], ![-1, 1, 0]]
  ![![13, 0, 0]] where
 M := ![![![169, 0, 0], ![-13, 13, 0]], ![![-39, -13, 13], ![143, 0, -13]]]
 hmul := by decide  
 g := ![![![![13, 0, 0]], ![![-1, 1, 0]]], ![![![-3, -1, 1]], ![![11, 0, -1]]]]
 hle2 := by decide  


def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N1, I13N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N1
    exact isPrimeI13N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 13 (by decide) (𝕀 ⊙ MulI13N0 ⊙ MulI13N1)
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


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [16, 1, 8, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 5, 6], [9, 11, 11], [0, 1]]
 g := ![![[0, 14, 13], [16, 8], [9, 1], []], ![[9, 13, 5, 10], [9, 1], [12, 2], [10, 2]], ![[13, 12], [12, 2], [16, 8], [5, 2]]]
 h' := ![![[0, 5, 6], [12, 1, 8], [9, 9, 12], [0, 0, 1], [0, 1]], ![[9, 11, 11], [7, 9, 9], [10, 0, 16], [10, 9, 11], [0, 5, 6]], ![[0, 1], [12, 7], [0, 8, 6], [1, 8, 5], [9, 11, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 11], []]
 b := ![[], [3, 16, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [16, 1, 8, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-267920, -17238, -12240]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-15760, -1014, -720]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![26443, 3482, 2422]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![26443, 3482, 2422]] 
 ![![19, 0, 0], ![0, 19, 0], ![10, 9, 1]] where
  M :=![![![26443, 3482, 2422], ![327272, 43095, 29976], ![344884, 45414, 31589]]]
  hmulB := by decide  
  f := ![![![-111, -10, 18]], ![![2504, -59, -136]], ![![1002, -23, -55]]]
  g := ![![![117, -964, 2422], ![1448, -11931, 29976], ![1526, -12573, 31589]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [13, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 18], [0, 1]]
 g := ![![[14, 16], [], [7], [1]], ![[9, 3], [], [7], [1]]]
 h' := ![![[8, 18], [0, 4], [2], [6, 8], [0, 1]], ![[0, 1], [13, 15], [2], [13, 11], [8, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [7, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [13, 11, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![31881, 2547, 4140]
  a := ![-1, 21, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-501, -1827, 4140]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-111, -10, 18]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![-111, -10, 18]] 
 ![![19, 0, 0], ![7, 1, 0], ![3, 0, 1]] where
  M :=![![![-111, -10, 18], ![2504, -59, -136], ![-2388, 194, -1]]]
  hmulB := by decide  
  f := ![![![26443, 3482, 2422]], ![![26967, 3551, 2470]], ![![22327, 2940, 2045]]]
  g := ![![![-5, -10, 18], ![175, -59, -136], ![-197, 194, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![26443, 3482, 2422]] ![![-111, -10, 18]]
  ![![19, 0, 0]] where
 M := ![![![19, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0]] 
 ![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [12, 13, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 13, 2], [5, 9, 21], [0, 1]]
 g := ![![[20, 1, 18], [17, 18, 3], [12, 18, 1], []], ![[6, 9], [0, 3, 19, 8], [12, 13, 8, 1], [9, 4]], ![[14, 9, 12, 10], [14, 9, 18, 22], [19, 15, 17, 7], [13, 4]]]
 h' := ![![[13, 13, 2], [3, 13, 15], [17, 19, 16], [0, 0, 1], [0, 1]], ![[5, 9, 21], [6, 4], [21, 2, 21], [15, 12, 9], [13, 13, 2]], ![[0, 1], [12, 6, 8], [17, 2, 9], [7, 11, 13], [5, 9, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12, 11], []]
 b := ![[], [12, 11, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [12, 13, 5, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-278185, -25392, 26036]
  a := ![1, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-12095, -1104, 1132]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 12167 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def PBC23 : ContainsPrimesAboveP 23 ![I23N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![23, 0, 0]]) timesTableT_eq_Table B_one_repr 23 (by decide) 𝕀

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


def P29P0 : CertificateIrreducibleZModOfList' 29 3 2 4 [16, 1, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [15, 1, 6], [11, 27, 23], [0, 1]]
 g := ![![[19, 22, 6], [24, 20], [6, 8, 9], [1]], ![[22, 25, 1, 6], [21, 20], [19, 16], [12, 26, 11, 13]], ![[17, 1, 4, 25], [], [5, 25, 10, 4], [17, 7, 26, 16]]]
 h' := ![![[15, 1, 6], [16, 12, 21], [20, 6, 7], [13, 28, 26], [0, 1]], ![[11, 27, 23], [28, 16, 1], [25, 17, 22], [22, 15], [15, 1, 6]], ![[0, 1], [28, 1, 7], [17, 6], [15, 15, 3], [11, 27, 23]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 5], []]
 b := ![[], [4, 25, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 3
  hpos := by decide
  P := [16, 1, 3, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2064104, 141723, 61480]
  a := ![-2, 3, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![71176, 4887, 2120]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0]] 
 ![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 3 2 4 [22, 1, 14, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [24, 0, 28], [24, 30, 3], [0, 1]]
 g := ![![[13, 24, 5], [2, 4, 7], [5, 12, 10], [1]], ![[21, 30, 30, 1], [23, 8, 5, 7], [30, 20, 28, 1], [2, 2, 6, 4]], ![[28, 5, 0, 6], [13, 2, 27, 15], [15, 17, 7, 27], [24, 7, 29, 27]]]
 h' := ![![[24, 0, 28], [18, 13, 6], [14, 29, 21], [9, 30, 17], [0, 1]], ![[24, 30, 3], [20, 2, 17], [28, 7, 16], [16, 16, 17], [24, 0, 28]], ![[0, 1], [6, 16, 8], [10, 26, 25], [28, 16, 28], [24, 30, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19, 15], []]
 b := ![[], [2, 23, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 3
  hpos := by decide
  P := [22, 1, 14, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-427428, -59830, -50530]
  a := ![0, -5, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-13788, -1930, -1630]
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



lemma PB202I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB202I0 : PrimesBelowBoundCertificateInterval O 1 31 202 where
  m := 11
  g := ![3, 3, 2, 1, 2, 3, 1, 2, 1, 1, 1]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB202I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1]
    · exact ![I3N0, I3N0, I3N0]
    · exact ![I5N0, I5N1]
    · exact ![I7N0]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1, I13N1]
    · exact ![I17N0]
    · exact ![I19N0, I19N1]
    · exact ![I23N0]
    · exact ![I29N0]
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
    · exact ![3, 3, 3]
    · exact ![5, 25]
    · exact ![343]
    · exact ![121, 11]
    · exact ![13, 13, 13]
    · exact ![4913]
    · exact ![361, 19]
    · exact ![12167]
    · exact ![24389]
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
      exact NI13N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
  β := ![I2N0, I2N1, I3N0, I5N0, I5N1, I11N0, I11N1, I13N0, I13N1, I19N1]
  Il := ![[I2N0, I2N1, I2N1], [I3N0, I3N0, I3N0], [I5N0, I5N1], [], [I11N0, I11N1], [I13N0, I13N1, I13N1], [], [I19N1], [], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
