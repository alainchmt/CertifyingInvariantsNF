
import IdealArithmetic.Examples.NF3_1_80359_1.RI3_1_80359_1
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
  c := ![-112060, 13034, -14728]
  a := ![1, 0, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-56030, 6517, -7364]
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

instance hp3 : Fact (Nat.Prime 3) := {out := by norm_num}

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1302, 97, -261]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![1302, 97, -261]] 
 ![![3, 0, 0], ![0, 1, 0], ![2, 0, 1]] where
  M :=![![![1302, 97, -261], ![-14452, 1988, 157], ![-929, -2118, 2018]]]
  hmulB := by decide  
  f := ![![![4344310, 357052, 534097]], ![![9672761, 794989, 1189186]], ![![13714936, 1127209, 1686138]]]
  g := ![![![608, 97, -261], ![-4922, 1988, 157], ![-1655, -2118, 2018]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4344310, -357052, -534097]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![-4344310, -357052, -534097]] 
 ![![3, 0, 0], ![0, 3, 0], ![1, 1, 1]] where
  M :=![![![-4344310, -357052, -534097], ![-29018283, -2384967, -3567558], ![-32456188, -2667523, -3990220]]]
  hmulB := by decide  
  f := ![![![-1302, -97, 261]], ![![14452, -1988, -157]], ![![4693, 11, -638]]]
  g := ![![![-1270071, 59015, -534097], ![-8483575, 394197, -3567558], ![-9488656, 440899, -3990220]]]
  hle1 := by decide   
  hle2 := by decide  


def P3P1 : CertificateIrreducibleZModOfList' 3 2 2 1 [2, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 2], [0, 1]]
 g := ![![[1, 1]], ![[2, 2]]]
 h' := ![![[1, 2], [0, 1]], ![[0, 1], [1, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [2, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N1 : CertifiedPrimeIdeal' SI3N1 3 where
  n := 2
  hpos := by decide
  P := [2, 2, 1]
  hirr := P3P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1420, 3395, -1105]
  a := ![-3, -5, 20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-105, 1500, -1105]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N1 B_one_repr
lemma NI3N1 : Nat.card (O ⧸ I3N1) = 9 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![1302, 97, -261]] ![![-4344310, -357052, -534097]]
  ![![3, 0, 0]] where
 M := ![![![-3, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0)
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


def P5P0 : CertificateIrreducibleZModOfList' 5 3 2 2 [2, 4, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 1, 3], [2, 3, 2], [0, 1]]
 g := ![![[1, 0, 1], []], ![[0, 2, 1, 2], [1, 4]], ![[0, 2, 2, 2], [2, 4]]]
 h' := ![![[3, 1, 3], [0, 0, 1], [0, 1]], ![[2, 3, 2], [2, 4, 3], [3, 1, 3]], ![[0, 1], [0, 1, 1], [2, 3, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 4], []]
 b := ![[], [1, 2, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where
  n := 3
  hpos := by decide
  P := [2, 4, 0, 1]
  hirr := P5P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-123931890, 13286490, -13689015]
  a := ![1, 2, -71]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-24786378, 2657298, -2737803]
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


def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 6, 9]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![73, 6, 9]] 
 ![![7, 0, 0], ![3, 1, 0], ![3, 0, 1]] where
  M :=![![![73, 6, 9], ![489, 40, 60], ![546, 45, 67]]]
  hmulB := by decide  
  f := ![![![-20, 3, 0]], ![![-9, -2, 3]], ![![15, 0, -2]]]
  g := ![![![4, 6, 9], ![27, 40, 60], ![30, 45, 67]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N0)

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := prime_ideal_of_norm_prime hp7.out _ NI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![90, -9, -4]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![90, -9, -4]] 
 ![![7, 0, 0], ![5, 1, 0], ![3, 0, 1]] where
  M :=![![![90, -9, -4], ![-211, 111, -71], ![-591, -1, 80]]]
  hmulB := by decide  
  f := ![![![-8809, -724, -1083]], ![![-14698, -1208, -1807]], ![![-13177, -1083, -1620]]]
  g := ![![![21, -9, -4], ![-79, 111, -71], ![-118, -1, 80]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1

def I7N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-49, -4, -6]] i)))

def SI7N2: IdealEqSpanCertificate' Table ![![-49, -4, -6]] 
 ![![7, 0, 0], ![5, 1, 0], ![6, 0, 1]] where
  M :=![![![-49, -4, -6], ![-326, -27, -40], ![-364, -30, -45]]]
  hmulB := by decide  
  f := ![![![-15, 0, 2]], ![![5, -3, 2]], ![![-6, 2, -1]]]
  g := ![![![1, -4, -6], ![7, -27, -40], ![8, -30, -45]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N2 : Nat.card (O ⧸ I7N2) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N2)

lemma isPrimeI7N2 : Ideal.IsPrime I7N2 := prime_ideal_of_norm_prime hp7.out _ NI7N2
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![73, 6, 9]] ![![90, -9, -4]]
  ![![-15, 0, 2]] where
 M := ![![![-15, 0, 2]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI7N1 : IdealMulLeCertificate' Table 
  ![![-15, 0, 2]] ![![-49, -4, -6]]
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
instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1646, -233, -12]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![1646, -233, -12]] 
 ![![11, 0, 0], ![0, 11, 0], ![4, 2, 1]] where
  M :=![![![1646, -233, -12], ![-427, 1915, -1655], ![-13103, 615, 1204]]]
  hmulB := by decide  
  f := ![![![302135, 24832, 37145]], ![![2018143, 165868, 248114]], ![![682006, 56053, 83847]]]
  g := ![![![154, -19, -12], ![563, 475, -1655], ![-1629, -163, 1204]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [6, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 10], [0, 1]]
 g := ![![[7, 4], [6, 4], [1]], ![[4, 7], [3, 7], [1]]]
 h' := ![![[2, 10], [8, 2], [5, 2], [0, 1]], ![[0, 1], [1, 9], [9, 9], [2, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [1, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 2
  hpos := by decide
  P := [6, 9, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1192, 343, -175]
  a := ![1, 0, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![172, 63, -175]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-302135, -24832, -37145]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![-302135, -24832, -37145]] 
 ![![11, 0, 0], ![6, 1, 0], ![5, 0, 1]] where
  M :=![![![-302135, -24832, -37145], ![-2018143, -165868, -248114], ![-2257240, -185519, -277509]]]
  hmulB := by decide  
  f := ![![![-1646, 233, 12]], ![![-859, -47, 157]], ![![443, 50, -104]]]
  g := ![![![2962, -24832, -37145], ![19785, -165868, -248114], ![22129, -185519, -277509]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![1646, -233, -12]] ![![-302135, -24832, -37145]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4, 5, -5]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![4, 5, -5]] 
 ![![13, 0, 0], ![0, 13, 0], ![7, 12, 1]] where
  M :=![![![4, 5, -5], ![-280, 14, 25], ![155, -50, 24]]]
  hmulB := by decide  
  f := ![![![122, 10, 15]], ![![815, 67, 100]], ![![888, 73, 109]]]
  g := ![![![3, 5, -5], ![-35, -22, 25], ![-1, -26, 24]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [3, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 12], [0, 1]]
 g := ![![[9, 9], [4], [12, 1]], ![[0, 4], [4], [11, 12]]]
 h' := ![![[12, 12], [10, 10], [3, 11], [0, 1]], ![[0, 1], [0, 3], [5, 2], [12, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [6, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 2
  hpos := by decide
  P := [3, 1, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1995, 636, -168]
  a := ![1, 4, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-63, 204, -168]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![122, 10, 15]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![122, 10, 15]] 
 ![![13, 0, 0], ![5, 1, 0], ![10, 0, 1]] where
  M :=![![![122, 10, 15], ![815, 67, 100], ![910, 75, 112]]]
  hmulB := by decide  
  f := ![![![4, 5, -5]], ![![-20, 3, 0]], ![![15, 0, -2]]]
  g := ![![![-6, 10, 15], ![-40, 67, 100], ![-45, 75, 112]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![4, 5, -5]] ![![122, 10, 15]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-24, -2, 5]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![-24, -2, 5]] 
 ![![17, 0, 0], ![9, 1, 0], ![9, 0, 1]] where
  M :=![![![-24, -2, 5], ![277, -37, -4], ![10, 41, -38]]]
  hmulB := by decide  
  f := ![![![-1570, -129, -193]], ![![-1448, -119, -178]], ![![-1521, -125, -187]]]
  g := ![![![-3, -2, 5], ![38, -37, -4], ![-1, 41, -38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N0 : Nat.card (O ⧸ I17N0) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N0)

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := prime_ideal_of_norm_prime hp17.out _ NI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-787, 280, -145]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![-787, 280, -145]] 
 ![![17, 0, 0], ![12, 1, 0], ![15, 0, 1]] where
  M :=![![![-787, 280, -145], ![-8255, -632, 1670], ![11920, -1855, 63]]]
  hmulB := by decide  
  f := ![![![3058034, 251335, 375960]], ![![3360169, 276167, 413105]], ![![4042175, 332220, 496952]]]
  g := ![![![-116, 280, -145], ![-1513, -632, 1670], ![1955, -1855, 63]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![-24, -2, 5]] ![![-787, 280, -145]]
  ![![94998, -14731, 455]] where
 M := ![![![94998, -14731, 455]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI17N1 : IdealMulLeCertificate' Table 
  ![![94998, -14731, 455]] ![![-787, 280, -145]]
  ![![17, 0, 0]] where
 M := ![![![52264579, 35065407, -38346815]]]
 hmul := by decide  
 g := ![![![![3074387, 2062671, -2255695]]]]
 hle2 := by decide  


def PBC17 : ContainsPrimesAboveP 17 ![I17N0, I17N1, I17N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N1
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


def P19P0 : CertificateIrreducibleZModOfList' 19 3 2 4 [15, 4, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 0, 6], [17, 18, 13], [0, 1]]
 g := ![![[5, 0, 16], [14, 0, 9], [18, 1], []], ![[4, 12, 8, 4], [10, 8, 14, 7], [12, 1], [2, 17]], ![[12, 11, 15, 10], [5, 14, 12, 8], [], [14, 17]]]
 h' := ![![[1, 0, 6], [18, 17, 15], [15, 8, 16], [0, 0, 1], [0, 1]], ![[17, 18, 13], [18, 7, 11], [15, 10, 13], [9, 3, 18], [1, 0, 6]], ![[0, 1], [10, 14, 12], [9, 1, 9], [3, 16], [17, 18, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 3], []]
 b := ![[], [17, 13, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 3
  hpos := by decide
  P := [15, 4, 1, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![982072, -114646, 90440]
  a := ![-2, -1, 14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![51688, -6034, 4760]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-77736, -6389, -9557]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![-77736, -6389, -9557]] 
 ![![23, 0, 0], ![3, 1, 0], ![22, 0, 1]] where
  M :=![![![-77736, -6389, -9557], ![-519246, -42676, -63837], ![-580763, -47732, -71400]]]
  hmulB := by decide  
  f := ![![![1284, -124, -61]], ![![27, 53, -51]], ![![868, -121, -8]]]
  g := ![![![6595, -6389, -9557], ![44052, -42676, -63837], ![49271, -47732, -71400]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N0 : Nat.card (O ⧸ I23N0) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N0)

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := prime_ideal_of_norm_prime hp23.out _ NI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-25, -2, -3]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![-25, -2, -3]] 
 ![![23, 0, 0], ![6, 1, 0], ![12, 0, 1]] where
  M :=![![![-25, -2, -3], ![-163, -14, -20], ![-182, -15, -23]]]
  hmulB := by decide  
  f := ![![![-22, 1, 2]], ![![-1, -1, 1]], ![![-7, 1, 0]]]
  g := ![![![1, -2, -3], ![7, -14, -20], ![8, -15, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1

def I23N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2089, -183, -116]] i)))

def SI23N2: IdealEqSpanCertificate' Table ![![2089, -183, -116]] 
 ![![23, 0, 0], ![13, 1, 0], ![17, 0, 1]] where
  M :=![![![2089, -183, -116], ![-6197, 2620, -1513], ![-12849, -263, 1955]]]
  hmulB := by decide  
  f := ![![![-4724181, -388273, -580799]], ![![-4042175, -332220, -496952]], ![![-5026316, -413105, -617944]]]
  g := ![![![280, -183, -116], ![-632, 2620, -1513], ![-1855, -263, 1955]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N2 : Nat.card (O ⧸ I23N2) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N2)

lemma isPrimeI23N2 : Ideal.IsPrime I23N2 := prime_ideal_of_norm_prime hp23.out _ NI23N2
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![-77736, -6389, -9557]] ![![-25, -2, -3]]
  ![![4724181, 388273, 580799]] where
 M := ![![![4724181, 388273, 580799]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI23N1 : IdealMulLeCertificate' Table 
  ![![4724181, 388273, 580799]] ![![2089, -183, -116]]
  ![![23, 0, 0]] where
 M := ![![![-23, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1521, -125, -187]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![-1521, -125, -187]] 
 ![![29, 0, 0], ![11, 1, 0], ![9, 0, 1]] where
  M :=![![![-1521, -125, -187], ![-10160, -835, -1249], ![-11363, -934, -1397]]]
  hmulB := by decide  
  f := ![![![71, -33, 20]], ![![66, -11, 1]], ![![-24, -2, 5]]]
  g := ![![![53, -125, -187], ![354, -835, -1249], ![396, -934, -1397]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N0 : Nat.card (O ⧸ I29N0) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N0)

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := prime_ideal_of_norm_prime hp29.out _ NI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![984141, 80885, 120992]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![984141, 80885, 120992]] 
 ![![29, 0, 0], ![23, 1, 0], ![27, 0, 1]] where
  M :=![![![984141, 80885, 120992], ![6573675, 540280, 808179], ![7352483, 604289, 903927]]]
  hmulB := by decide  
  f := ![![![-171, -707, 655]], ![![1131, -610, 394]], ![![-958, -427, 510]]]
  g := ![![![-142862, 80885, 120992], ![-954262, 540280, 808179], ![-1067317, 604289, 903927]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![-1521, -125, -187]] ![![984141, 80885, 120992]]
  ![![-3693502157, -303563128, -454085556]] where
 M := ![![![-3693502157, -303563128, -454085556]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI29N1 : IdealMulLeCertificate' Table 
  ![![-3693502157, -303563128, -454085556]] ![![984141, 80885, 120992]]
  ![![29, 0, 0]] where
 M := ![![![-8969108582783085, -737156915314469, -1102677752582068]]]
 hmul := by decide  
 g := ![![![![-309279606302865, -25419203976361, -38023370778692]]]]
 hle2 := by decide  


def PBC29 : ContainsPrimesAboveP 29 ![I29N0, I29N1, I29N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N1
    exact isPrimeI29N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 29 (by decide) (𝕀 ⊙ MulI29N0 ⊙ MulI29N1)
instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3834, 36, 481]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![-3834, 36, 481]] 
 ![![31, 0, 0], ![0, 31, 0], ![20, 10, 1]] where
  M :=![![![-3834, 36, 481], ![26419, -5313, 1214], ![13524, 3259, -4724]]]
  hmulB := by decide  
  f := ![![![682006, 56053, 83847]], ![![4555532, 374412, 560065]], ![![2073893, 170450, 254968]]]
  g := ![![![-434, -154, 481], ![69, -563, 1214], ![3484, 1629, -4724]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [29, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [29, 30], [0, 1]]
 g := ![![[30, 5], [12, 14], [4, 5], [29, 1]], ![[20, 26], [15, 17], [25, 26], [27, 30]]]
 h' := ![![[29, 30], [24, 6], [8, 18], [27, 6], [0, 1]], ![[0, 1], [12, 25], [3, 13], [15, 25], [29, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [5, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [29, 2, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![629, 175, -60]
  a := ![0, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![59, 25, -60]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![682006, 56053, 83847]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![682006, 56053, 83847]] 
 ![![31, 0, 0], ![21, 1, 0], ![24, 0, 1]] where
  M :=![![![682006, 56053, 83847], ![4555532, 374412, 560065], ![5095243, 418770, 626418]]]
  hmulB := by decide  
  f := ![![![-3834, 36, 481]], ![![-1745, -147, 365]], ![![-2532, 133, 220]]]
  g := ![![![-80885, 56053, 83847], ![-540280, 374412, 560065], ![-604289, 418770, 626418]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![-3834, 36, 481]] ![![682006, 56053, 83847]]
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


lemma PB81I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB81I0 : PrimesBelowBoundCertificateInterval O 1 31 81 where
  m := 11
  g := ![1, 2, 1, 3, 2, 2, 3, 1, 3, 3, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB81I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0]
    · exact ![I3N0, I3N1]
    · exact ![I5N0]
    · exact ![I7N0, I7N1, I7N2]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1]
    · exact ![I17N0, I17N1, I17N1]
    · exact ![I19N0]
    · exact ![I23N0, I23N1, I23N2]
    · exact ![I29N0, I29N1, I29N1]
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
    · exact ![3, 9]
    · exact ![125]
    · exact ![7, 7, 7]
    · exact ![121, 11]
    · exact ![169, 13]
    · exact ![17, 17, 17]
    · exact ![6859]
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
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N1
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
      exact NI11N1
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
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
      exact NI29N1
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
  β := ![I2N0, I3N0, I3N1, I7N0, I7N1, I7N2, I11N1, I13N1, I17N0, I17N1, I23N0, I23N1, I23N2, I29N0, I29N1, I31N1]
  Il := ![[I2N0], [I3N0, I3N1], [], [I7N0, I7N1, I7N2], [I11N1], [I13N1], [I17N0, I17N1, I17N1], [], [I23N0, I23N1, I23N2], [I29N0, I29N1, I29N1], [I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
