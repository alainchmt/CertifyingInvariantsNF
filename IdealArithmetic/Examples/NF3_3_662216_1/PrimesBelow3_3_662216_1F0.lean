
import IdealArithmetic.Examples.NF3_3_662216_1.RI3_3_662216_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-16, -6, -1]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![-16, -6, -1]] 
 ![![2, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![-16, -6, -1], ![-167, -73, -13], ![-1075, -451, -79]]]
  hmulB := by decide  
  f := ![![![-96, -23, 5]], ![![343, 83, -18]], ![![-1579, -383, 83]]]
  g := ![![![-5, -6, -1], ![-47, -73, -13], ![-312, -451, -79]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-63639, -2616, 1261]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![-63639, -2616, 1261]] 
 ![![2, 0, 0], ![1, 1, 0], ![1, 0, 1]] where
  M :=![![![-63639, -2616, 1261], ![200405, 8238, -3971], ![-283727, -11663, 5622]]]
  hmulB := by decide  
  f := ![![![263, 109, 18]], ![![1635, 699, 127]], ![![9887, 4142, 708]]]
  g := ![![![-31142, -2616, 1261], ![98069, 8238, -3971], ![-138843, -11663, 5622]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![-16, -6, -1]] ![![-63639, -2616, 1261]]
  ![![99521, 4091, -1972]] where
 M := ![![![99521, 4091, -1972]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![99521, 4091, -1972]] ![![-63639, -2616, 1261]]
  ![![2, 0, 0]] where
 M := ![![![-4954050420, -203645842, 98164036]]]
 hmul := by decide  
 g := ![![![![-2477025210, -101822921, 49082018]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4744, 195, -94]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![4744, 195, -94]] 
 ![![3, 0, 0], ![0, 1, 0], ![2, 0, 1]] where
  M :=![![![4744, 195, -94], ![-14939, -614, 296], ![21149, 869, -419]]]
  hmulB := by decide  
  f := ![![![42, 19, 4]], ![![221, 90, 14]], ![![1193, 519, 99]]]
  g := ![![![1644, 195, -94], ![-5177, -614, 296], ![7329, 869, -419]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![42, 19, 4]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![42, 19, 4]] 
 ![![3, 0, 0], ![0, 3, 0], ![0, 1, 1]] where
  M :=![![![42, 19, 4], ![663, 270, 42], ![3495, 1519, 289]]]
  hmulB := by decide  
  f := ![![![4744, 195, -94]], ![![-14939, -614, 296]], ![![2070, 85, -41]]]
  g := ![![![14, 5, 4], ![221, 76, 42], ![1165, 410, 289]]]
  hle1 := by decide   
  hle2 := by decide  


def P3P1 : CertificateIrreducibleZModOfList' 3 2 2 1 [2, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 2], [0, 1]]
 g := ![![[2, 1]], ![[1, 2]]]
 h' := ![![[2, 2], [0, 1]], ![[0, 1], [2, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [1, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N1 : CertifiedPrimeIdeal' SI3N1 3 where
  n := 2
  hpos := by decide
  P := [2, 1, 1]
  hirr := P3P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1083, 665, 236]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![361, 143, 236]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N1 B_one_repr
lemma NI3N1 : Nat.card (O ⧸ I3N1) = 9 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![4744, 195, -94]] ![![42, 19, 4]]
  ![![3, 0, 0]] where
 M := ![![![3, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P5P0 : CertificateIrreducibleZModOfList' 5 3 2 2 [3, 4, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 0, 4], [0, 4, 1], [0, 1]]
 g := ![![[2, 4, 1], []], ![[3, 2, 3, 4], [4, 1]], ![[0, 1], [2, 1]]]
 h' := ![![[4, 0, 4], [0, 0, 1], [0, 1]], ![[0, 4, 1], [4, 1, 4], [4, 0, 4]], ![[0, 1], [4, 4], [0, 4, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 3], []]
 b := ![[], [4, 0, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where
  n := 3
  hpos := by decide
  P := [3, 4, 1, 1]
  hirr := P5P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1584440, 1072765, 409000]
  a := ![2, -2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![316888, 214553, 81800]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0]] 
 ![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 3 2 2 [6, 4, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 3, 2], [1, 3, 5], [0, 1]]
 g := ![![[2, 3, 2], [1]], ![[1, 0, 2, 2], [6, 2, 4, 1]], ![[0, 1, 2, 3], [6, 5, 5, 6]]]
 h' := ![![[2, 3, 2], [1, 3, 3], [0, 1]], ![[1, 3, 5], [0, 0, 1], [2, 3, 2]], ![[0, 1], [0, 4, 3], [1, 3, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5], []]
 b := ![[], [3, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 3
  hpos := by decide
  P := [6, 4, 4, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6797059948, -3617824322, -1041379136]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-971008564, -516832046, -148768448]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0]] 
 ![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [4, 7, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 3, 9], [2, 7, 2], [0, 1]]
 g := ![![[4], [2, 8, 1], []], ![[0, 1, 9, 1], [5, 1, 6, 1], [9, 4]], ![[6, 5, 9, 10], [10, 10, 8, 7], [5, 4]]]
 h' := ![![[6, 3, 9], [3, 9], [0, 0, 1], [0, 1]], ![[2, 7, 2], [2, 5, 4], [0, 1, 7], [6, 3, 9]], ![[0, 1], [10, 8, 7], [6, 10, 3], [2, 7, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 4], []]
 b := ![[], [3, 10, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [4, 7, 3, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2280102, -1311013, -418759]
  a := ![-2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-207282, -119183, -38069]
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

instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2725, 112, -54]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![2725, 112, -54]] 
 ![![13, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![2725, 112, -54], ![-8582, -353, 170], ![12146, 498, -241]]]
  hmulB := by decide  
  f := ![![![413, 100, -22]], ![![-233, -57, 12]], ![![1054, 254, -57]]]
  g := ![![![201, 112, -54], ![-633, -353, 170], ![896, 498, -241]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N0 : Nat.card (O ⧸ I13N0) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N0)

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := prime_ideal_of_norm_prime hp13.out _ NI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-37656, -1547, 746]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![-37656, -1547, 746]] 
 ![![13, 0, 0], ![5, 1, 0], ![1, 0, 1]] where
  M :=![![![-37656, -1547, 746], ![118559, 4866, -2348], ![-167753, -6865, 3319]]]
  hmulB := by decide  
  f := ![![![31234, 13203, 2320]], ![![41761, 17653, 3102]], ![![185369, 78358, 13769]]]
  g := ![![![-2359, -1547, 746], ![7429, 4866, -2348], ![-10519, -6865, 3319]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1

def I13N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5409, 252, -112]] i)))

def SI13N2: IdealEqSpanCertificate' Table ![![5409, 252, -112]] 
 ![![13, 0, 0], ![6, 1, 0], ![2, 0, 1]] where
  M :=![![![5409, 252, -112], ![-17780, -975, 392], ![28364, 2156, -723]]]
  hmulB := by decide  
  f := ![![![-140227, -59276, -10416]], ![![-198278, -83815, -14728]], ![![-843018, -356356, -62619]]]
  g := ![![![317, 252, -112], ![-978, -975, 392], ![1298, 2156, -723]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N2 : Nat.card (O ⧸ I13N2) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N2)

lemma isPrimeI13N2 : Ideal.IsPrime I13N2 := prime_ideal_of_norm_prime hp13.out _ NI13N2
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![2725, 112, -54]] ![![-37656, -1547, 746]]
  ![![-80275330, -3299873, 1590648]] where
 M := ![![![-80275330, -3299873, 1590648]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI13N1 : IdealMulLeCertificate' Table 
  ![![-80275330, -3299873, 1590648]] ![![5409, 252, -112]]
  ![![13, 0, 0]] where
 M := ![![![-330420378158, -13582569897, 6547248240]]]
 hmul := by decide  
 g := ![![![![-25416952166, -1044813069, 503634480]]]]
 hle2 := by decide  


def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N1, I13N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N1
    exact isPrimeI13N2
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


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [9, 0, 11, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 14, 4], [12, 2, 13], [0, 1]]
 g := ![![[12, 14, 9], [5, 4], [6, 1], []], ![[7, 10, 14, 16], [16, 4], [0, 4], [4, 16]], ![[10, 16, 5, 2], [8, 16], [1, 9], [12, 16]]]
 h' := ![![[11, 14, 4], [15, 1, 14], [14, 8, 2], [0, 0, 1], [0, 1]], ![[12, 2, 13], [9, 15, 15], [0, 15, 2], [0, 11, 2], [11, 14, 4]], ![[0, 1], [4, 1, 5], [12, 11, 13], [2, 6, 14], [12, 2, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 6], []]
 b := ![[], [4, 12, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [9, 0, 11, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-294491, -135796, -29818]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-17323, -7988, -1754]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0]] 
 ![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 3 2 4 [1, 7, 13, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 3, 12], [3, 15, 7], [0, 1]]
 g := ![![[16], [1, 6, 5], [6, 1], []], ![[18, 7, 6, 3], [8, 8, 16, 15], [16, 16], [5, 11]], ![[2, 3, 17, 16], [3, 11, 14, 4], [13, 9], [10, 11]]]
 h' := ![![[3, 3, 12], [18, 4], [13, 14, 10], [0, 0, 1], [0, 1]], ![[3, 15, 7], [11, 12, 10], [0, 9, 14], [4, 10, 15], [3, 3, 12]], ![[0, 1], [11, 3, 9], [7, 15, 14], [18, 9, 3], [3, 15, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 2], []]
 b := ![[], [18, 16, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 3
  hpos := by decide
  P := [1, 7, 13, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8696471, 3698673, 647881]
  a := ![2, 19, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![457709, 194667, 34099]
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


def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![122534, 5037, -2428]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![122534, 5037, -2428]] 
 ![![23, 0, 0], ![7, 1, 0], ![22, 0, 1]] where
  M :=![![![122534, 5037, -2428], ![-385871, -15862, 7646], ![546305, 22457, -10825]]]
  hmulB := by decide  
  f := ![![![-72, -71, -34]], ![![-263, -109, -18]], ![![-727, -405, -123]]]
  g := ![![![6117, 5037, -2428], ![-19263, -15862, 7646], ![27272, 22457, -10825]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N0 : Nat.card (O ⧸ I23N0) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N0)

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := prime_ideal_of_norm_prime hp23.out _ NI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8, -1, 0]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![-8, -1, 0]] 
 ![![23, 0, 0], ![8, 1, 0], ![3, 0, 1]] where
  M :=![![![-8, -1, 0], ![-1, -8, -2], ![-161, -57, -9]]]
  hmulB := by decide  
  f := ![![![-42, -9, 2]], ![![-1, 0, 0]], ![![-59, -14, 3]]]
  g := ![![![0, -1, 0], ![3, -8, -2], ![14, -57, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![122534, 5037, -2428]] ![![122534, 5037, -2428]]
  ![![11744520389, 482781268, -232716550]] where
 M := ![![![11744520389, 482781268, -232716550]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI23N1 : IdealMulLeCertificate' Table 
  ![![11744520389, 482781268, -232716550]] ![![-8, -1, 0]]
  ![![23, 0, 0]] where
 M := ![![![-56971579830, -2341927183, 1128886414]]]
 hmul := by decide  
 g := ![![![![-2477025210, -101822921, 49082018]]]]
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

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0]] 
 ![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 3 2 4 [17, 21, 26, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 22, 10], [1, 6, 19], [0, 1]]
 g := ![![[5, 5, 23], [3, 25], [27, 17, 9], [1]], ![[23, 1, 7, 19], [5, 24], [25, 15, 8, 21], [9, 10, 1, 14]], ![[17, 13, 16, 27], [13, 6], [25, 1, 23, 12], [15, 3, 18, 15]]]
 h' := ![![[2, 22, 10], [3, 19, 9], [5, 13, 24], [12, 8, 3], [0, 1]], ![[1, 6, 19], [15, 11, 12], [10, 3, 13], [0, 21, 11], [2, 22, 10]], ![[0, 1], [12, 28, 8], [1, 13, 21], [7, 0, 15], [1, 6, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 18], []]
 b := ![[], [24, 7, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 3
  hpos := by decide
  P := [17, 21, 26, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![63539, -79170, -70122]
  a := ![-2, 3, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2191, -2730, -2418]
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


def P31P0 : CertificateIrreducibleZModOfList' 31 3 2 4 [29, 11, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [28, 8, 28], [1, 22, 3], [0, 1]]
 g := ![![[14, 9, 16], [6, 4, 2], [28, 5, 4], [1]], ![[27, 24, 7, 28], [22, 17, 13, 14], [14, 12, 21, 9], [30, 30, 22, 4]], ![[22, 30, 6, 27], [12, 25, 28, 29], [20, 6, 24, 11], [14, 30, 13, 27]]]
 h' := ![![[28, 8, 28], [12, 9, 4], [25, 16, 8], [2, 20, 29], [0, 1]], ![[1, 22, 3], [20, 4, 30], [16, 23, 4], [2, 8, 20], [28, 8, 28]], ![[0, 1], [7, 18, 28], [13, 23, 19], [29, 3, 13], [1, 22, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 7], []]
 b := ![[], [30, 7, 23], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 3
  hpos := by decide
  P := [29, 11, 2, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1993765, 976810, 243970]
  a := ![2, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![64315, 31510, 7870]
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



lemma PB181I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB181I0 : PrimesBelowBoundCertificateInterval O 1 31 181 where
  m := 11
  g := ![3, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB181I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1]
    · exact ![I3N0, I3N1]
    · exact ![I5N0]
    · exact ![I7N0]
    · exact ![I11N0]
    · exact ![I13N0, I13N1, I13N2]
    · exact ![I17N0]
    · exact ![I19N0]
    · exact ![I23N0, I23N0, I23N1]
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
    · exact ![3, 9]
    · exact ![125]
    · exact ![343]
    · exact ![1331]
    · exact ![13, 13, 13]
    · exact ![4913]
    · exact ![6859]
    · exact ![23, 23, 23]
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
      exact NI3N1
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
      exact NI13N2
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N0
      exact NI23N1
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
  β := ![I2N0, I2N1, I3N0, I3N1, I5N0, I13N0, I13N1, I13N2, I23N0, I23N1]
  Il := ![[I2N0, I2N1, I2N1], [I3N0, I3N1], [I5N0], [], [], [I13N0, I13N1, I13N2], [], [], [I23N0, I23N0, I23N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
