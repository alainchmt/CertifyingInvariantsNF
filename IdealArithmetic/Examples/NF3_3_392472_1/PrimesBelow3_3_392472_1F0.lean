
import IdealArithmetic.Examples.NF3_3_392472_1.RI3_3_392472_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-601, -535, 149]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![-601, -535, 149]] 
 ![![2, 0, 0], ![0, 1, 0], ![1, 0, 1]] where
  M :=![![![-601, -535, 149], ![4917, 4377, -1219], ![-22572, -20093, 5596]]]
  hmulB := by decide  
  f := ![![![325, 3, -8]], ![![-132, 16, 7]], ![![344, 65, 5]]]
  g := ![![![-375, -535, 149], ![3068, 4377, -1219], ![-14084, -20093, 5596]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2158, 1921, -535]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![2158, 1921, -535]] 
 ![![2, 0, 0], ![1, 1, 0], ![1, 0, 1]] where
  M :=![![![2158, 1921, -535], ![-17655, -15716, 4377], ![81048, 72147, -20093]]]
  hmulB := by decide  
  f := ![![![5831, -8, -157]], ![![325, 3, -8]], ![![5374, 5, -142]]]
  g := ![![![386, 1921, -535], ![-3158, -15716, 4377], ![14497, 72147, -20093]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![-601, -535, 149]] ![![2158, 1921, -535]]
  ![![20224619, 18003442, -5014017]] where
 M := ![![![20224619, 18003442, -5014017]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![20224619, 18003442, -5014017]] ![![2158, 1921, -535]]
  ![![2, 0, 0]] where
 M := ![![![-680582090524, -605836885872, 168727538050]]]
 hmul := by decide  
 g := ![![![![-340291045262, -302918442936, 84363769025]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5163, 4596, -1280]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![5163, 4596, -1280]] 
 ![![3, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![5163, 4596, -1280], ![-42240, -37601, 10472], ![193908, 172612, -48073]]]
  hmulB := by decide  
  f := ![![![9, 148, 32]], ![![352, 447, 88]], ![![1276, 1804, 359]]]
  g := ![![![1721, 4596, -1280], ![-14080, -37601, 10472], ![64636, 172612, -48073]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![5163, 4596, -1280]] ![![5163, 4596, -1280]]
  ![![-415680711, -370028408, 103054112]] where
 M := ![![![-415680711, -370028408, 103054112]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![-415680711, -370028408, 103054112]] ![![5163, 4596, -1280]]
  ![![3, 0, 0]] where
 M := ![![![33466857192723, 29791346001996, -8296986504672]]]
 hmul := by decide  
 g := ![![![![11155619064241, 9930448667332, -2765662168224]]]]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-226423, -201556, 56134]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![-226423, -201556, 56134]] 
 ![![5, 0, 0], ![0, 5, 0], ![3, 1, 1]] where
  M :=![![![-226423, -201556, 56134], ![1852422, 1648979, -459246], ![-8503770, -7569840, 2108225]]]
  hmulB := by decide  
  f := ![![![-2327, 92, 82]], ![![2706, 799, 102]], ![![-789, 863, 209]]]
  g := ![![![-78965, -51538, 56134], ![646032, 421645, -459246], ![-2965689, -1935613, 2108225]]]
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
  c := ![102, 424, 329]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-177, 19, 329]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI5N0 B_one_repr
lemma NI5N0 : Nat.card (O ⧸ I5N0) = 25 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2327, 92, 82]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![-2327, 92, 82]] 
 ![![5, 0, 0], ![4, 1, 0], ![0, 0, 1]] where
  M :=![![![-2327, 92, 82], ![2706, 799, 102], ![330, 3240, 697]]]
  hmulB := by decide  
  f := ![![![-226423, -201556, 56134]], ![![189346, 168551, -46942]], ![![-1700754, -1513968, 421645]]]
  g := ![![![-539, 92, 82], ![-98, 799, 102], ![-2526, 3240, 697]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![-226423, -201556, 56134]] ![![-2327, 92, 82]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2599, 2288, -638]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![2599, 2288, -638]] 
 ![![7, 0, 0], ![0, 7, 0], ![5, 1, 1]] where
  M :=![![![2599, 2288, -638], ![-21054, -18719, 5214], ![96558, 85932, -23933]]]
  hmulB := by decide  
  f := ![![![-6803, -9416, -1870]], ![![-61710, -85409, -16962]], ![![-49249, -68163, -13537]]]
  g := ![![![827, 418, -638], ![-6732, -3419, 5214], ![30889, 15695, -23933]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 2 2 2 [6, 4, 1] where
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
 g := ![![[3, 2], [3, 1]], ![[2, 5], [6, 6]]]
 h' := ![![[3, 6], [3, 3], [0, 1]], ![[0, 1], [5, 4], [3, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [4, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 2
  hpos := by decide
  P := [6, 4, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-261, 267, 610]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-473, -49, 610]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6803, -9416, -1870]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![-6803, -9416, -1870]] 
 ![![7, 0, 0], ![6, 1, 0], ![0, 0, 1]] where
  M :=![![![-6803, -9416, -1870], ![-61710, -85409, -16962], ![-249018, -344652, -68447]]]
  hmulB := by decide  
  f := ![![![2599, 2288, -638]], ![![-780, -713, 198]], ![![13794, 12276, -3419]]]
  g := ![![![7099, -9416, -1870], ![64392, -85409, -16962], ![259842, -344652, -68447]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![2599, 2288, -638]] ![![-6803, -9416, -1870]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![120956, 107672, -29987]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![120956, 107672, -29987]] 
 ![![11, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![120956, 107672, -29987], ![-989571, -880891, 245331], ![4542747, 4043838, -1126222]]]
  hmulB := by decide  
  f := ![![![3424, 5078, 1015]], ![![3045, 4187, 831]], ![![12189, 16896, 3356]]]
  g := ![![![10996, 107672, -29987], ![-89961, -880891, 245331], ![412977, 4043838, -1126222]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N0 : Nat.card (O ⧸ I11N0) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N0)

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := prime_ideal_of_norm_prime hp11.out _ NI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 10, 2]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![7, 10, 2]] 
 ![![11, 0, 0], ![3, 1, 0], ![5, 0, 1]] where
  M :=![![![7, 10, 2], ![66, 91, 18], ![264, 366, 73]]]
  hmulB := by decide  
  f := ![![![-55, -2, 2]], ![![-9, 1, 0]], ![![-37, -8, 3]]]
  g := ![![![-3, 10, 2], ![-27, 91, 18], ![-109, 366, 73]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1

def I11N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1168, -28, 25]] i)))

def SI11N2: IdealEqSpanCertificate' Table ![![-1168, -28, 25]] 
 ![![11, 0, 0], ![8, 1, 0], ![8, 0, 1]] where
  M :=![![![-1168, -28, 25], ![825, -271, -81], ![-1749, -1086, -190]]]
  hmulB := by decide  
  f := ![![![-36476, -32470, 9043]], ![![601, 535, -149]], ![![-151067, -134476, 37452]]]
  g := ![![![-104, -28, 25], ![331, -271, -81], ![769, -1086, -190]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N2 : Nat.card (O ⧸ I11N2) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N2)

lemma isPrimeI11N2 : Ideal.IsPrime I11N2 := prime_ideal_of_norm_prime hp11.out _ NI11N2
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![120956, 107672, -29987]] ![![7, 10, 2]]
  ![![36476, 32470, -9043]] where
 M := ![![![36476, 32470, -9043]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI11N1 : IdealMulLeCertificate' Table 
  ![![36476, 32470, -9043]] ![![-1168, -28, 25]]
  ![![11, 0, 0]] where
 M := ![![![-11, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-100, -106, 29]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![-100, -106, 29]] 
 ![![13, 0, 0], ![0, 13, 0], ![10, 8, 1]] where
  M :=![![![-100, -106, 29], ![957, 867, -241], ![-4455, -3980, 1108]]]
  hmulB := by decide  
  f := ![![![-112, -156, -31]], ![![-1023, -1415, -281]], ![![-1033, -1430, -284]]]
  g := ![![![-30, -26, 29], ![259, 215, -241], ![-1195, -988, 1108]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [3, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 12], [0, 1]]
 g := ![![[11, 9], [10], [6, 1]], ![[0, 4], [10], [12, 12]]]
 h' := ![![[6, 12], [8, 3], [8, 7], [0, 1]], ![[0, 1], [0, 10], [11, 6], [6, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [10, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 2
  hpos := by decide
  P := [3, 7, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3618, -2, 159]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![156, -98, 159]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![112, 156, 31]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![112, 156, 31]] 
 ![![13, 0, 0], ![11, 1, 0], ![12, 0, 1]] where
  M :=![![![112, 156, 31], ![1023, 1415, 281], ![4125, 5710, 1134]]]
  hmulB := by decide  
  f := ![![![100, 106, -29]], ![![11, 23, -6]], ![![435, 404, -112]]]
  g := ![![![-152, 156, 31], ![-1378, 1415, 281], ![-5561, 5710, 1134]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![-100, -106, 29]] ![![112, 156, 31]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![80, -4, -3]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![80, -4, -3]] 
 ![![17, 0, 0], ![0, 17, 0], ![13, 7, 1]] where
  M :=![![![80, -4, -3], ![-99, -35, -5], ![-33, -142, -30]]]
  hmulB := by decide  
  f := ![![![-20, -18, 5]], ![![165, 147, -41]], ![![8, 7, -2]]]
  g := ![![![7, 1, -3], ![-2, 0, -5], ![21, 4, -30]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 2 2 4 [4, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 16], [0, 1]]
 g := ![![[2, 13], [2], [13], [1]], ![[0, 4], [2], [13], [1]]]
 h' := ![![[9, 16], [13, 8], [15, 11], [13, 9], [0, 1]], ![[0, 1], [0, 9], [12, 6], [9, 8], [9, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [14, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 2
  hpos := by decide
  P := [4, 8, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-152, 674, 888]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-688, -326, 888]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-20, -18, 5]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![-20, -18, 5]] 
 ![![17, 0, 0], ![4, 1, 0], ![7, 0, 1]] where
  M :=![![![-20, -18, 5], ![165, 147, -41], ![-759, -676, 188]]]
  hmulB := by decide  
  f := ![![![80, -4, -3]], ![![13, -3, -1]], ![![31, -10, -3]]]
  g := ![![![1, -18, 5], ![-8, 147, -41], ![37, -676, 188]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![80, -4, -3]] ![![-20, -18, 5]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-146963, -203498, -40416]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![-146963, -203498, -40416]] 
 ![![19, 0, 0], ![0, 19, 0], ![12, 9, 1]] where
  M :=![![![-146963, -203498, -40416], ![-1333728, -1845853, -366580], ![-5381706, -7448594, -1479273]]]
  hmulB := by decide  
  f := ![![![785071, 698850, -194632]], ![![-6422856, -5717463, 1592332]], ![![-994734, -885487, 246611]]]
  g := ![![![17791, 8434, -40416], ![161328, 76493, -366580], ![651030, 308677, -1479273]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [8, 11, 1] where
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
 g := ![![[18, 5], [2, 16], [7], [1]], ![[1, 14], [16, 3], [7], [1]]]
 h' := ![![[8, 18], [3, 9], [8, 4], [11, 8], [0, 1]], ![[0, 1], [18, 10], [2, 15], [18, 11], [8, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [5, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [8, 11, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![107, 408, 305]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-187, -123, 305]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![785071, 698850, -194632]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![785071, 698850, -194632]] 
 ![![19, 0, 0], ![2, 1, 0], ![16, 0, 1]] where
  M :=![![![785071, 698850, -194632], ![-6422856, -5717463, 1592332], ![29484906, 26246714, -7309795]]]
  hmulB := by decide  
  f := ![![![-146963, -203498, -40416]], ![![-85666, -118571, -23548]], ![![-407006, -563398, -111891]]]
  g := ![![![131657, 698850, -194632], ![-1077118, -5717463, 1592332], ![4944642, 26246714, -7309795]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![-146963, -203498, -40416]] ![![785071, 698850, -194632]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![38, 0, -1]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![38, 0, -1]] 
 ![![23, 0, 0], ![5, 1, 0], ![8, 0, 1]] where
  M :=![![![38, 0, -1], ![-33, 1, 1], ![33, 2, 0]]]
  hmulB := by decide  
  f := ![![![-2, -2, 1]], ![![1, 1, 0]], ![![-5, -4, 2]]]
  g := ![![![2, 0, -1], ![-2, 1, 1], ![1, 2, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N0 : Nat.card (O ⧸ I23N0) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N0)

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := prime_ideal_of_norm_prime hp23.out _ NI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 6, -2]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![7, 6, -2]] 
 ![![23, 0, 0], ![13, 1, 0], ![1, 0, 1]] where
  M :=![![![7, 6, -2], ![-66, -61, 14], ![264, 226, -75]]]
  hmulB := by decide  
  f := ![![![-1411, 2, 38]], ![![-743, 1, 20]], ![![-113, 0, 3]]]
  g := ![![![-3, 6, -2], ![31, -61, 14], ![-113, 226, -75]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![38, 0, -1]] ![![38, 0, -1]]
  ![![1411, -2, -38]] where
 M := ![![![1411, -2, -38]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI23N1 : IdealMulLeCertificate' Table 
  ![![1411, -2, -38]] ![![7, 6, -2]]
  ![![23, 0, 0]] where
 M := ![![![-23, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC23 : ContainsPrimesAboveP 23 ![I23N0, I23N0, I23N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
    exact isPrimeI23N0
    exact isPrimeI23N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 23 (by decide) (𝕀 ⊙ MulI23N0 ⊙ MulI23N1)
instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1535, -4, 40]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![-1535, -4, 40]] 
 ![![29, 0, 0], ![0, 29, 0], ![16, 26, 1]] where
  M :=![![![-1535, -4, 40], ![1320, -59, -48], ![-1452, -228, -11]]]
  hmulB := by decide  
  f := ![![![-355, -316, 88]], ![![2904, 2585, -720]], ![![1948, 1734, -483]]]
  g := ![![![-75, -36, 40], ![72, 41, -48], ![-44, 2, -11]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [27, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [27, 28], [0, 1]]
 g := ![![[28, 24], [23], [25, 7], [27, 1]], ![[9, 5], [23], [11, 22], [25, 28]]]
 h' := ![![[27, 28], [23, 13], [21, 9], [25, 6], [0, 1]], ![[0, 1], [26, 16], [3, 20], [13, 23], [27, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [24, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [27, 2, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![13197, 30678, 16802]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-8815, -14006, 16802]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![355, 316, -88]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![355, 316, -88]] 
 ![![29, 0, 0], ![7, 1, 0], ![1, 0, 1]] where
  M :=![![![355, 316, -88], ![-2904, -2585, 720], ![13332, 11868, -3305]]]
  hmulB := by decide  
  f := ![![![1535, 4, -40]], ![![325, 3, -8]], ![![103, 8, -1]]]
  g := ![![![-61, 316, -88], ![499, -2585, 720], ![-2291, 11868, -3305]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![-1535, -4, 40]] ![![355, 316, -88]]
  ![![29, 0, 0]] where
 M := ![![![-29, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 8, 2]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![5, 8, 2]] 
 ![![31, 0, 0], ![0, 31, 0], ![18, 4, 1]] where
  M :=![![![5, 8, 2], ![66, 87, 14], ![198, 292, 73]]]
  hmulB := by decide  
  f := ![![![-73, 0, 2]], ![![66, 1, -2]], ![![-36, 0, 1]]]
  g := ![![![-1, 0, 2], ![-6, 1, 14], ![-36, 0, 73]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [22, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [7, 30], [0, 1]]
 g := ![![[18, 8], [18, 25], [11, 16], [7, 1]], ![[12, 23], [7, 6], [30, 15], [14, 30]]]
 h' := ![![[7, 30], [7, 15], [6, 5], [1, 27], [0, 1]], ![[0, 1], [19, 16], [10, 26], [4, 4], [7, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [3, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [22, 24, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![98, 194, 64]
  a := ![-1, 2, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-34, -2, 64]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-73, 0, 2]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![-73, 0, 2]] 
 ![![31, 0, 0], ![24, 1, 0], ![10, 0, 1]] where
  M :=![![![-73, 0, 2], ![66, 1, -2], ![-66, -4, 3]]]
  hmulB := by decide  
  f := ![![![5, 8, 2]], ![![6, 9, 2]], ![![8, 12, 3]]]
  g := ![![![-3, 0, 2], ![2, 1, -2], ![0, -4, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![5, 8, 2]] ![![-73, 0, 2]]
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


lemma PB140I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB140I0 : PrimesBelowBoundCertificateInterval O 1 31 140 where
  m := 11
  g := ![3, 3, 2, 2, 3, 2, 2, 2, 3, 2, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB140I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1]
    · exact ![I3N0, I3N0, I3N0]
    · exact ![I5N0, I5N1]
    · exact ![I7N0, I7N1]
    · exact ![I11N0, I11N1, I11N2]
    · exact ![I13N0, I13N1]
    · exact ![I17N0, I17N1]
    · exact ![I19N0, I19N1]
    · exact ![I23N0, I23N0, I23N1]
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
    · exact ![2, 2, 2]
    · exact ![3, 3, 3]
    · exact ![25, 5]
    · exact ![49, 7]
    · exact ![11, 11, 11]
    · exact ![169, 13]
    · exact ![289, 17]
    · exact ![361, 19]
    · exact ![23, 23, 23]
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
      exact NI7N1
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
      exact NI11N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N0
      exact NI23N1
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
  β := ![I2N0, I2N1, I3N0, I5N0, I5N1, I7N0, I7N1, I11N0, I11N1, I11N2, I13N1, I17N1, I19N1, I23N0, I23N1, I29N1, I31N1]
  Il := ![[I2N0, I2N1, I2N1], [I3N0, I3N0, I3N0], [I5N0, I5N1], [I7N0, I7N1], [I11N0, I11N1, I11N2], [I13N1], [I17N1], [I19N1], [I23N0, I23N0, I23N1], [I29N1], [I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
