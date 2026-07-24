
import IdealArithmetic.Examples.NF3_1_391287_1.RI3_1_391287_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp2 : Fact (Nat.Prime 2) := {out := by norm_num}

def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0]] 
 ![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P2P0 : CertificateIrreducibleZModOfList' 2 3 2 1 [1, 1, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 0, 1], [0, 1, 1], [0, 1]]
 g := ![![[]], ![[0, 1]], ![[0, 1]]]
 h' := ![![[0, 0, 1], [0, 1]], ![[0, 1, 1], [0, 0, 1]], ![[0, 1], [0, 1, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1], []]
 b := ![[], [1, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI2N0 : CertifiedPrimeIdeal' SI2N0 2 where
  n := 3
  hpos := by decide
  P := [1, 1, 0, 1]
  hirr := P2P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-119796, 6318, -3414]
  a := ![1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-59898, 3159, -1707]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI2N0 B_one_repr
lemma NI2N0 : Nat.card (O ⧸ I2N0) = 8 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI2N0

def PBC2 : ContainsPrimesAboveP 2 ![I2N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![2, 0, 0]]) timesTableT_eq_Table B_one_repr 2 (by decide) 𝕀


def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137476687, 14816485, 7798750]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![137476687, 14816485, 7798750]] 
 ![![3, 0, 0], ![2, 1, 0], ![2, 0, 1]] where
  M :=![![![137476687, 14816485, 7798750], ![921033515, 99263952, 52248205], ![2409676950, 259701795, 136695672]]]
  hmulB := by decide  
  f := ![![![-12231, 3330, -575]], ![![-32264, -2392, 2755]], ![![109521, -8585, -2967]]]
  g := ![![![30748739, 14816485, 7798750], ![206003067, 99263952, 52248205], ![538960672, 259701795, 136695672]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-49, -11, 7]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![-49, -11, 7]] 
 ![![3, 0, 0], ![2, 1, 0], ![0, 0, 1]] where
  M :=![![![-49, -11, 7], ![851, -59, -26], ![-753, 306, -74]]]
  hmulB := by decide  
  f := ![![![12322, 1328, 699]], ![![35732, 3851, 2027]], ![![71993, 7759, 4084]]]
  g := ![![![-9, -11, 7], ![323, -59, -26], ![-455, 306, -74]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![137476687, 14816485, 7798750]] ![![-49, -11, 7]]
  ![![12322, 1328, 699]] where
 M := ![![![12322, 1328, 699]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI3N1 : IdealMulLeCertificate' Table 
  ![![12322, 1328, 699]] ![![-49, -11, 7]]
  ![![3, 0, 0]] where
 M := ![![![3, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N1, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N1
    exact isPrimeI3N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1)
instance hp5 : Fact (Nat.Prime 5) := {out := by norm_num}

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![205067, 22101, 11633]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![205067, 22101, 11633]] 
 ![![5, 0, 0], ![0, 5, 0], ![4, 2, 1]] where
  M :=![![![205067, 22101, 11633], ![1373859, 148067, 77936], ![3594393, 387384, 203902]]]
  hmulB := by decide  
  f := ![![![-398, -6, 25]], ![![3006, -467, 7]], ![![1145, 7, -68]]]
  g := ![![![31707, -233, 11633], ![212423, -1561, 77936], ![555757, -4084, 203902]]]
  hle1 := by decide   
  hle2 := by decide  


def P5P0 : CertificateIrreducibleZModOfList' 5 2 2 2 [3, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 4], [0, 1]]
 g := ![![[1, 4], [1]], ![[4, 1], [1]]]
 h' := ![![[2, 4], [2, 2], [0, 1]], ![[0, 1], [1, 3], [2, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [1, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where
  n := 2
  hpos := by decide
  P := [3, 3, 1]
  hirr := P5P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4438, 2726, -157]
  a := ![-3, -5, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-762, 608, -157]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI5N0 B_one_repr
lemma NI5N0 : Nat.card (O ⧸ I5N0) = 25 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-398, -6, 25]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![-398, -6, 25]] 
 ![![5, 0, 0], ![3, 1, 0], ![1, 0, 1]] where
  M :=![![![-398, -6, 25], ![3006, -467, 7], ![1305, 993, -454]]]
  hmulB := by decide  
  f := ![![![205067, 22101, 11633]], ![![397812, 42874, 22567]], ![![759892, 81897, 43107]]]
  g := ![![![-81, -6, 25], ![880, -467, 7], ![-244, 993, -454]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![205067, 22101, 11633]] ![![-398, -6, 25]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19668822, 2119798, 1115769]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![19668822, 2119798, 1115769]] 
 ![![7, 0, 0], ![0, 7, 0], ![3, 4, 1]] where
  M :=![![![19668822, 2119798, 1115769], ![131772482, 14201717, 7475163], ![344753049, 37155597, 19557082]]]
  hmulB := by decide  
  f := ![![![-3931, -49, 243]], ![![29209, -4611, 96]], ![![16978, -1281, -479]]]
  g := ![![![2331645, -334754, 1115769], ![15620999, -2242705, 7475163], ![40868829, -5867533, 19557082]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 2 2 2 [3, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 6], [0, 1]]
 g := ![![[4, 1], [2, 1]], ![[6, 6], [4, 6]]]
 h' := ![![[2, 6], [1, 1], [0, 1]], ![[0, 1], [3, 6], [2, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [5, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 2
  hpos := by decide
  P := [3, 5, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![331454, 175885, -9703]
  a := ![1, 2, -67]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![51509, 30671, -9703]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3931, -49, 243]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![-3931, -49, 243]] 
 ![![7, 0, 0], ![1, 1, 0], ![2, 0, 1]] where
  M :=![![![-3931, -49, 243], ![29209, -4611, 96], ![13803, 9624, -4466]]]
  hmulB := by decide  
  f := ![![![19668822, 2119798, 1115769]], ![![21634472, 2331645, 1227276]], ![![54870099, 5913599, 3112660]]]
  g := ![![![-624, -49, 243], ![4804, -4611, 96], ![1873, 9624, -4466]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![19668822, 2119798, 1115769]] ![![-3931, -49, 243]]
  ![![7, 0, 0]] where
 M := ![![![7, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0]] 
 ![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [8, 9, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 7, 5], [1, 3, 6], [0, 1]]
 g := ![![[5, 1, 3], [5, 5, 1], []], ![[1, 8, 4, 1], [3, 6, 1, 1], [8, 3]], ![[2, 5, 0, 2], [6, 7, 5, 8], [7, 3]]]
 h' := ![![[4, 7, 5], [4, 3, 5], [0, 0, 1], [0, 1]], ![[1, 3, 6], [7, 8, 8], [7, 4, 3], [4, 7, 5]], ![[0, 1], [7, 0, 9], [0, 7, 7], [1, 3, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 9], []]
 b := ![[], [3, 5, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [8, 9, 6, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2589180, 130416, 25168]
  a := ![3, 4, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-235380, 11856, 2288]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 1331 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def PBC11 : ContainsPrimesAboveP 11 ![I11N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![11, 0, 0]]) timesTableT_eq_Table B_one_repr 11 (by decide) 𝕀


def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1965650, 211847, 111507]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![1965650, 211847, 111507]] 
 ![![13, 0, 0], ![7, 1, 0], ![3, 0, 1]] where
  M :=![![![1965650, 211847, 111507], ![13168993, 1419282, 747048], ![34453707, 3713232, 1954483]]]
  hmulB := by decide  
  f := ![![![2070, 523, -318]], ![![-1861, 474, -75]], ![![3324, -954, 175]]]
  g := ![![![11400, 211847, 111507], ![76375, 1419282, 747048], ![199818, 3713232, 1954483]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N0 : Nat.card (O ⧸ I13N0) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N0)

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := prime_ideal_of_norm_prime hp13.out _ NI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2131765, 525647, -79293]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![-2131765, 525647, -79293]] 
 ![![13, 0, 0], ![12, 1, 0], ![12, 0, 1]] where
  M :=![![![-2131765, 525647, -79293], ![-10040807, -2419533, 1497648], ![56654907, -4669368, -1447532]]]
  hmulB := by decide  
  f := ![![![10495421089020, 1131139050028, 595382148087]], ![![15096905522204, 1627061861159, 856414236555]], ![![23839053312819, 2569242709665, 1352337047686]]]
  g := ![![![-576001, 525647, -79293], ![78601, -2419533, 1497648], ![10004439, -4669368, -1447532]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![1965650, 211847, 111507]] ![![1965650, 211847, 111507]]
  ![![10495421089020, 1131139050028, 595382148087]] where
 M := ![![![10495421089020, 1131139050028, 595382148087]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI13N1 : IdealMulLeCertificate' Table 
  ![![10495421089020, 1131139050028, 595382148087]] ![![-2131765, 525647, -79293]]
  ![![13, 0, 0]] where
 M := ![![![13, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N0, I13N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N0
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


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [5, 10, 16, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 0, 2], [5, 16, 15], [0, 1]]
 g := ![![[11, 5, 13], [11, 13], [1, 1], []], ![[16, 9, 0, 9], [14, 16], [2, 1], [4, 4]], ![[1, 10, 13, 15], [0, 16], [], [8, 4]]]
 h' := ![![[13, 0, 2], [4, 9, 9], [12, 2, 8], [0, 0, 1], [0, 1]], ![[5, 16, 15], [0, 4, 9], [6, 13, 13], [13, 8, 16], [13, 0, 2]], ![[0, 1], [16, 4, 16], [4, 2, 13], [2, 9], [5, 16, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 10], []]
 b := ![[], [1, 2, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [5, 10, 16, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-108103, 11934, -3825]
  a := ![1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-6359, 702, -225]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4038112271, -397627605, 382364386]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![-4038112271, -397627605, 382364386]] 
 ![![19, 0, 0], ![0, 1, 0], ![6, 0, 1]] where
  M :=![![![-4038112271, -397627605, 382364386], ![46281353925, -4787577824, -810518429], ![-16743797334, 16105093869, -5200468648]]]
  hmulB := by decide  
  f := ![![![-37951123755171473753, -4090164435310721394, -2152883756832608609]], ![![-13381888757084332194, -1442226739440154028, -759125108566566989]], ![![-46995266266934563533, -5064892622231784207, -2665938064095401557]]]
  g := ![![![-333278873, -397627605, 382364386], ![2691813921, -4787577824, -810518429], ![761000766, 16105093869, -5200468648]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N0 : Nat.card (O ⧸ I19N0) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N0)

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := prime_ideal_of_norm_prime hp19.out _ NI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6779876005, -2627465189, 617472233]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![6779876005, -2627465189, 617472233]] 
 ![![19, 0, 0], ![0, 19, 0], ![9, 6, 1]] where
  M :=![![![6779876005, -2627465189, 617472233], ![76724133149, 7554924495, -7264923334], ![-265280571807, 31963812654, 2917466350]]]
  hmulB := by decide  
  f := ![![![13381888757084332194, 1442226739440154028, 759125108566566989]], ![![89652786288547884652, 9662286691944477199, 5085805326887029073]], ![![46995266266934563533, 5064892622231784207, 2665938064095401557]]]
  g := ![![![64348732, -333278873, 617472233], ![7479391745, 2691813921, -7264923334], ![-15344093103, 761000766, 2917466350]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P1 : CertificateIrreducibleZModOfList' 19 2 2 4 [2, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 18], [0, 1]]
 g := ![![[18, 9], [], [4], [1]], ![[17, 10], [], [4], [1]]]
 h' := ![![[2, 18], [0, 16], [15], [17, 2], [0, 1]], ![[0, 1], [13, 3], [15], [2, 17], [2, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [9, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N1 : CertifiedPrimeIdeal' SI19N1 19 where
  n := 2
  hpos := by decide
  P := [2, 17, 1]
  hirr := P19P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![18238, 138, 1144]
  a := ![-1, 18, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![418, -354, 1144]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N1 B_one_repr
lemma NI19N1 : Nat.card (O ⧸ I19N1) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![-4038112271, -397627605, 382364386]] ![![6779876005, -2627465189, 617472233]]
  ![![19, 0, 0]] where
 M := ![![![-159319376758099401002, 19827776488089290188, 1510847094321375027]]]
 hmul := by decide  
 g := ![![![![-8385230355689442158, 1043567183583646852, 79518268122177633]]]]
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


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [5, 18, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 7, 5], [9, 15, 18], [0, 1]]
 g := ![![[11, 12, 9], [11, 3, 2], [5, 0, 1], []], ![[15, 8, 14, 14], [13, 5, 8, 11], [1, 17, 3, 21], [1, 2]], ![[19, 4, 20, 16], [9, 4, 9, 18], [16, 5, 6, 8], [11, 2]]]
 h' := ![![[14, 7, 5], [14, 21, 20], [21, 2, 18], [0, 0, 1], [0, 1]], ![[9, 15, 18], [11, 11, 14], [14, 2, 4], [7, 7, 15], [14, 7, 5]], ![[0, 1], [10, 14, 12], [1, 19, 1], [3, 16, 7], [9, 15, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 12], []]
 b := ![[], [14, 7, 16], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [5, 18, 0, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-350888, 276, 15548]
  a := ![1, 4, -4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-15256, 12, 676]
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

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![132369, 14266, 7509]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![132369, 14266, 7509]] 
 ![![29, 0, 0], ![0, 29, 0], ![8, 1, 1]] where
  M :=![![![132369, 14266, 7509], ![886814, 95576, 50307], ![2320149, 250053, 131617]]]
  hmulB := by decide  
  f := ![![![349, -5, -18]], ![![-2155, 408, -33]], ![![-49, -11, 7]]]
  g := ![![![2493, 233, 7509], ![16702, 1561, 50307], ![43697, 4084, 131617]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [5, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [15, 28], [0, 1]]
 g := ![![[26, 6], [28], [16, 28], [15, 1]], ![[0, 23], [28], [1, 1], [1, 28]]]
 h' := ![![[15, 28], [25, 8], [7, 12], [12, 17], [0, 1]], ![[0, 1], [0, 21], [13, 17], [6, 12], [15, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [22, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [5, 14, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1456, 1429, -21]
  a := ![-2, -1, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![56, 50, -21]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![349, -5, -18]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![349, -5, -18]] 
 ![![29, 0, 0], ![25, 1, 0], ![22, 0, 1]] where
  M :=![![![349, -5, -18], ![-2155, 408, -33], ![-2058, -687, 380]]]
  hmulB := by decide  
  f := ![![![132369, 14266, 7509]], ![![144691, 15594, 8208]], ![![180423, 19445, 10235]]]
  g := ![![![30, -5, -18], ![-401, 408, -33], ![233, -687, 380]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![132369, 14266, 7509]] ![![349, -5, -18]]
  ![![29, 0, 0]] where
 M := ![![![29, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC29 : ContainsPrimesAboveP 29 ![I29N0, I29N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 29 (by decide) (𝕀 ⊙ MulI29N0)
instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![133, -12, -3]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![133, -12, -3]] 
 ![![31, 0, 0], ![0, 31, 0], ![28, 4, 1]] where
  M :=![![![133, -12, -3], ![-348, 154, -39], ![-1683, -81, 127]]]
  hmulB := by decide  
  f := ![![![529, 57, 30]], ![![3543, 382, 201]], ![![1234, 133, 70]]]
  g := ![![![7, 0, -3], ![24, 10, -39], ![-169, -19, 127]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [26, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [20, 30], [0, 1]]
 g := ![![[4, 19], [9, 9], [15, 4], [20, 1]], ![[12, 12], [3, 22], [2, 27], [9, 30]]]
 h' := ![![[20, 30], [14, 22], [13, 28], [7, 2], [0, 1]], ![[0, 1], [20, 9], [15, 3], [16, 29], [20, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [3, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [26, 11, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2051, 975, -105]
  a := ![0, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![161, 45, -105]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![529, 57, 30]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![529, 57, 30]] 
 ![![31, 0, 0], ![18, 1, 0], ![1, 0, 1]] where
  M :=![![![529, 57, 30], ![3543, 382, 201], ![9270, 999, 526]]]
  hmulB := by decide  
  f := ![![![133, -12, -3]], ![![66, -2, -3]], ![![-50, -3, 4]]]
  g := ![![![-17, 57, 30], ![-114, 382, 201], ![-298, 999, 526]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![133, -12, -3]] ![![529, 57, 30]]
  ![![31, 0, 0]] where
 M := ![![![31, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


lemma PB177I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB177I0 : PrimesBelowBoundCertificateInterval O 1 31 177 where
  m := 11
  g := ![1, 3, 2, 2, 1, 3, 1, 2, 1, 2, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB177I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0]
    · exact ![I3N0, I3N1, I3N1]
    · exact ![I5N0, I5N1]
    · exact ![I7N0, I7N1]
    · exact ![I11N0]
    · exact ![I13N0, I13N0, I13N1]
    · exact ![I17N0]
    · exact ![I19N0, I19N1]
    · exact ![I23N0]
    · exact ![I29N0, I29N1]
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
    · exact ![8]
    · exact ![3, 3, 3]
    · exact ![25, 5]
    · exact ![49, 7]
    · exact ![1331]
    · exact ![13, 13, 13]
    · exact ![4913]
    · exact ![19, 361]
    · exact ![12167]
    · exact ![841, 29]
    · exact ![961, 31]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N1
      exact NI3N1
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N1
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N1
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N0
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
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
  β := ![I2N0, I3N0, I3N1, I5N0, I5N1, I7N0, I7N1, I13N0, I13N1, I19N0, I29N1, I31N1]
  Il := ![[I2N0], [I3N0, I3N1, I3N1], [I5N0, I5N1], [I7N0, I7N1], [], [I13N0, I13N0, I13N1], [], [I19N0], [], [I29N1], [I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
