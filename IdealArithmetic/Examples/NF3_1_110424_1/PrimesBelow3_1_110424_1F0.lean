
import IdealArithmetic.Examples.NF3_1_110424_1.RI3_1_110424_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![6, 2, 1]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0], ![6, 2, 1]] 
 ![![2, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![6, 2, 1], ![62, 0, 10], ![74, -7, -7]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![-10, 13, 8], ![-9, 0, 1]], ![![-3, -1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![3, 2, 1], ![31, 0, 10], ![37, -7, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43523, 3729, 3363]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![43523, 3729, 3363]] 
 ![![2, 0, 0], ![0, 1, 0], ![1, 0, 1]] where
  M :=![![![43523, 3729, 3363], ![202512, 17351, 15648], ![75036, 6429, 5798]]]
  hmulB := by decide  
  f := ![![![106, -15, -21]], ![![-624, 143, -24]], ![![59, -69, 152]]]
  g := ![![![20080, 3729, 3363], ![93432, 17351, 15648], ![34619, 6429, 5798]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![2, 0, 0], ![6, 2, 1]] ![![2, 0, 0], ![6, 2, 1]]
  ![![106, -15, -21]] where
 M := ![![![4, 0, 0], ![12, 4, 2]], ![![12, 4, 2], ![234, 5, 19]]]
 hmul := by decide  
 g := ![![![![87046, 7458, 6726]], ![![741198, 63505, 57272]]], ![![![741198, 63505, 57272]], ![![6311313, 540746, 487672]]]]
 hle2 := by decide  
def MulI2N1 : IdealMulLeCertificate' Table 
  ![![106, -15, -21]] ![![43523, 3729, 3363]]
  ![![2, 0, 0]] where
 M := ![![![2, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![6, 1, 1]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0], ![6, 1, 1]] 
 ![![3, 0, 0], ![2, 1, 0], ![1, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![6, 1, 1], ![60, -2, 4], ![16, 3, -5]]]
  hmulB := by decide  
  f := ![![![9, 2, -14], ![12, 0, -6]], ![![8, 2, -9], ![7, 0, -4]], ![![-1, 0, -5], ![6, 0, -2]]]
  g := ![![![1, 0, 0], ![-2, 3, 0], ![-1, 0, 3]], ![![1, 1, 1], ![20, -2, 4], ![5, 3, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![791206297159, 67789645138, 61136113972]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![791206297159, 67789645138, 61136113972]] 
 ![![3, 0, 0], ![2, 1, 0], ![2, 0, 1]] where
  M :=![![![791206297159, 67789645138, 61136113972], ![3681473900652, 315424447715, 284465642884], ![1364082631180, 116873030256, 105401981135]]]
  hmulB := by decide  
  f := ![![![758221, -134798, -75988]], ![![-1053486, 326303, -269596]], ![![-1036782, 30180, 519911]]]
  g := ![![![177784926313, 67789645138, 61136113972], ![827231239818, 315424447715, 284465642884], ![306510869466, 116873030256, 105401981135]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![6, 1, 1]] ![![3, 0, 0], ![6, 1, 1]]
  ![![758221, -134798, -75988]] where
 M := ![![![9, 0, 0], ![18, 3, 3]], ![![18, 3, 3], ![112, 7, 5]]]
 hmul := by decide  
 g := ![![![![2373618891477, 203368935414, 183408341916]], ![![9792794314786, 839035348799, 756684307851]]], ![![![9792794314786, 839035348799, 756684307851]], ![![40401945247424, 3461592180247, 3121838056909]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![758221, -134798, -75988]] ![![791206297159, 67789645138, 61136113972]]
  ![![3, 0, 0]] where
 M := ![![![3, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P5P0 : CertificateIrreducibleZModOfList' 5 3 2 2 [2, 0, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 2, 2], [1, 2, 3], [0, 1]]
 g := ![![[1, 4, 1], []], ![[1, 2, 2, 3], [4, 4]], ![[0, 2, 3, 2], [3, 4]]]
 h' := ![![[3, 2, 2], [0, 0, 1], [0, 1]], ![[1, 2, 3], [1, 4, 2], [3, 2, 2]], ![[0, 1], [0, 1, 2], [1, 2, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 3], []]
 b := ![[], [1, 1, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where
  n := 3
  hpos := by decide
  P := [2, 0, 1, 1]
  hirr := P5P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2350, 1005, -3360]
  a := ![-1, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-470, 201, -672]
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


def P7P0 : CertificateIrreducibleZModOfList' 7 3 2 2 [3, 0, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 5, 2], [5, 1, 5], [0, 1]]
 g := ![![[0, 6, 4], [1]], ![[3, 6, 1, 1], [5, 6, 2, 1]], ![[4, 4, 2, 3], [4, 5, 0, 6]]]
 h' := ![![[0, 5, 2], [4, 0, 5], [0, 1]], ![[5, 1, 5], [6, 3, 5], [0, 5, 2]], ![[0, 1], [1, 4, 4], [5, 1, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5], []]
 b := ![[], [0, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 3
  hpos := by decide
  P := [3, 0, 2, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-834355494, 219176216, -225480395]
  a := ![-65, -64, -131]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-119193642, 31310888, -32211485]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![0, 1, 0]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0], ![0, 1, 0]] 
 ![![11, 0, 0], ![0, 1, 0], ![4, 0, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![0, 1, 0], ![2, 2, 6], ![58, -10, -2]]]
  hmulB := by decide  
  f := ![![![-11, -12, -36], ![0, 66, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-4, -5, -13], ![7, 24, 0]]]
  g := ![![![1, 0, 0], ![0, 11, 0], ![-4, 0, 11]], ![![0, 1, 0], ![-2, 2, 6], ![6, -10, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N0 : Nat.card (O ⧸ I11N0) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N0)

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := prime_ideal_of_norm_prime hp11.out _ NI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1825, 307, 230]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![-1825, 307, 230]] 
 ![![11, 0, 0], ![1, 1, 0], ![9, 0, 1]] where
  M :=![![![-1825, 307, 230], ![13954, -3511, 1382], ![8146, -80, -4509]]]
  hmulB := by decide  
  f := ![![![15941659, 1365863, 1231804]], ![![8192547, 701928, 633034]], ![![15541747, 1331599, 1200903]]]
  g := ![![![-382, 307, 230], ![457, -3511, 1382], ![4437, -80, -4509]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1

def I11N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![-1, 1, 0]] i)))

def SI11N2: IdealEqSpanCertificate' Table ![![11, 0, 0], ![-1, 1, 0]] 
 ![![11, 0, 0], ![10, 1, 0], ![6, 0, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![-1, 1, 0], ![2, 1, 6], ![58, -10, -3]]]
  hmulB := by decide  
  f := ![![![81, 40, 240], ![0, -440, 0]], ![![73, 36, 216], ![1, -396, 0]], ![![44, 22, 131], ![-2, -240, 0]]]
  g := ![![![1, 0, 0], ![-10, 11, 0], ![-6, 0, 11]], ![![-1, 1, 0], ![-4, 1, 6], ![16, -10, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N2 : Nat.card (O ⧸ I11N2) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N2)

lemma isPrimeI11N2 : Ideal.IsPrime I11N2 := prime_ideal_of_norm_prime hp11.out _ NI11N2
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![11, 0, 0], ![0, 1, 0]] ![![-1825, 307, 230]]
  ![![11, 0, 0], ![4, 6, 1]] where
 M := ![![![-20075, 3377, 2530]], ![![13954, -3511, 1382]]]
 hmul := by decide  
 g := ![![![![-1705, 487, 260], ![-330, 0, 0]]], ![![![1190, -437, 106], ![216, 0, 0]]]]
 hle2 := by decide  

def MulI11N1 : IdealMulLeCertificate' Table 
  ![![11, 0, 0], ![4, 6, 1]] ![![11, 0, 0], ![-1, 1, 0]]
  ![![11, 0, 0]] where
 M := ![![![121, 0, 0], ![-11, 11, 0]], ![![44, 66, 11], ![66, 0, 33]]]
 hmul := by decide  
 g := ![![![![11, 0, 0]], ![![-1, 1, 0]]], ![![![4, 6, 1]], ![![6, 0, 3]]]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![153, 39, -194]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![153, 39, -194]] 
 ![![13, 0, 0], ![0, 13, 0], ![10, 0, 1]] where
  M :=![![![153, 39, -194], ![-11174, 2171, 622], ![10410, -2912, 1821]]]
  hmulB := by decide  
  f := ![![![443435, 37993, 34264]], ![![2063298, 176781, 159430]], ![![399912, 34264, 30901]]]
  g := ![![![161, 3, -194], ![-1338, 167, 622], ![-600, -224, 1821]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [9, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 12], [0, 1]]
 g := ![![[1, 3], [10], [4, 1]], ![[0, 10], [10], [8, 12]]]
 h' := ![![[4, 12], [10, 4], [3, 7], [0, 1]], ![[0, 1], [0, 9], [5, 6], [4, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [5, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 2
  hpos := by decide
  P := [9, 9, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1249, 494, -498]
  a := ![-2, -1, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![287, 38, -498]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![443435, 37993, 34264]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![443435, 37993, 34264]] 
 ![![13, 0, 0], ![2, 1, 0], ![12, 0, 1]] where
  M :=![![![443435, 37993, 34264], ![2063298, 176781, 159430], ![764506, 65502, 59073]]]
  hmulB := by decide  
  f := ![![![153, 39, -194]], ![![-836, 173, 18]], ![![942, -188, -39]]]
  g := ![![![-3363, 37993, 34264], ![-15648, 176781, 159430], ![-5798, 65502, 59073]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![153, 39, -194]] ![![443435, 37993, 34264]]
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


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [5, 0, 14, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 12, 9], [7, 4, 8], [0, 1]]
 g := ![![[11, 11, 15], [0, 13], [3, 1], []], ![[14, 1, 6, 1], [1, 13], [1, 16], [0, 13]], ![[9, 9, 16, 8], [], [12, 8], [1, 13]]]
 h' := ![![[13, 12, 9], [4, 0, 10], [2, 12, 9], [0, 0, 1], [0, 1]], ![[7, 4, 8], [11, 5, 6], [13, 4, 8], [16, 9, 4], [13, 12, 9]], ![[0, 1], [2, 12, 1], [6, 1], [10, 8, 12], [7, 4, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 11], []]
 b := ![[], [12, 0, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [5, 0, 14, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1904, 1122, -4335]
  a := ![-1, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![112, 66, -255]
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


def P19P0 : CertificateIrreducibleZModOfList' 19 3 2 4 [17, 6, 13, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 12, 15], [15, 6, 4], [0, 1]]
 g := ![![[5, 7, 16], [11, 16, 7], [6, 1], []], ![[16, 13, 13, 3], [3, 7, 1, 13], [3, 17], [0, 16]], ![[0, 10, 2, 11], [13, 12, 0, 7], [17, 11], [11, 16]]]
 h' := ![![[10, 12, 15], [3, 15, 4], [12, 4, 11], [0, 0, 1], [0, 1]], ![[15, 6, 4], [2, 14, 2], [12, 0, 12], [5, 6, 6], [10, 12, 15]], ![[0, 1], [0, 9, 13], [15, 15, 15], [0, 13, 12], [15, 6, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12, 2], []]
 b := ![[], [12, 18, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 3
  hpos := by decide
  P := [17, 6, 13, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1948849, -46246, -179246]
  a := ![2, 21, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![102571, -2434, -9434]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5591, -479, -432]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![-5591, -479, -432]] 
 ![![23, 0, 0], ![0, 23, 0], ![18, 10, 1]] where
  M :=![![![-5591, -479, -432], ![-26014, -2229, -2010], ![-9638, -826, -745]]]
  hmulB := by decide  
  f := ![![![-15, 1, 6]], ![![350, -73, -6]], ![![132, -28, -1]]]
  g := ![![![95, 167, -432], ![442, 777, -2010], ![164, 288, -745]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [8, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 22], [0, 1]]
 g := ![![[20, 3], [21, 2], [8, 1], [1]], ![[0, 20], [0, 21], [9, 22], [1]]]
 h' := ![![[1, 22], [16, 7], [5, 18], [15, 1], [0, 1]], ![[0, 1], [0, 16], [0, 5], [16, 22], [1, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [20, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 2
  hpos := by decide
  P := [8, 22, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1660, 445, -289]
  a := ![-2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![154, 145, -289]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15, -1, -6]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![15, -1, -6]] 
 ![![23, 0, 0], ![11, 1, 0], ![11, 0, 1]] where
  M :=![![![15, -1, -6], ![-350, 73, 6], ![194, -68, 71]]]
  hmulB := by decide  
  f := ![![![5591, 479, 432]], ![![3805, 326, 294]], ![![3093, 265, 239]]]
  g := ![![![4, -1, -6], ![-53, 73, 6], ![7, -68, 71]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![-5591, -479, -432]] ![![15, -1, -6]]
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

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![3, 4, 1]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0], ![3, 4, 1]] 
 ![![29, 0, 0], ![0, 29, 0], ![3, 4, 1]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![3, 4, 1], ![66, 1, 22], ![190, -27, -14]]]
  hmulB := by decide  
  f := ![![![-2, -4, -1], ![29, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-3, -4, 29]], ![![0, 0, 1], ![0, -3, 22], ![8, 1, -14]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [7, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [24, 28], [0, 1]]
 g := ![![[9, 25], [9], [17, 5], [24, 1]], ![[0, 4], [9], [21, 24], [19, 28]]]
 h' := ![![[24, 28], [4, 24], [26, 3], [6, 18], [0, 1]], ![[0, 1], [0, 5], [11, 26], [3, 11], [24, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [21, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [7, 5, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![615, 153, -288]
  a := ![2, 3, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![51, 45, -288]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![7, 1, 0]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![29, 0, 0], ![7, 1, 0]] 
 ![![29, 0, 0], ![7, 1, 0], ![14, 0, 1]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![7, 1, 0], ![2, 9, 6], ![58, -10, 5]]]
  hmulB := by decide  
  f := ![![![545, 2692, 1800], ![232, -8700, 0]], ![![130, 646, 432], ![59, -2088, 0]], ![![259, 1299, 869], ![129, -4200, 0]]]
  g := ![![![1, 0, 0], ![-7, 29, 0], ![-14, 0, 29]], ![![0, 1, 0], ![-5, 9, 6], ![2, -10, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![29, 0, 0], ![3, 4, 1]] ![![29, 0, 0], ![7, 1, 0]]
  ![![29, 0, 0]] where
 M := ![![![841, 0, 0], ![203, 29, 0]], ![![87, 116, 29], ![87, 29, 29]]]
 hmul := by decide  
 g := ![![![![29, 0, 0]], ![![7, 1, 0]]], ![![![3, 4, 1]], ![![3, 1, 1]]]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![-8, -12, 1]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0], ![-8, -12, 1]] 
 ![![31, 0, 0], ![0, 31, 0], ![23, 19, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![-8, -12, 1], ![34, -42, -74], ![-738, 133, 7]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-23, -19, 31]], ![![-1, -1, 1], ![56, 44, -74], ![-29, 0, 7]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [11, 27, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 30], [0, 1]]
 g := ![![[25, 8], [26, 19], [1, 25], [4, 1]], ![[26, 23], [9, 12], [8, 6], [8, 30]]]
 h' := ![![[4, 30], [24, 16], [20, 22], [18, 5], [0, 1]], ![[0, 1], [26, 15], [15, 9], [7, 26], [4, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [22, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [11, 27, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1551, 265, -1120]
  a := ![-5, -5, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![881, 695, -1120]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![12, 1, 0]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![31, 0, 0], ![12, 1, 0]] 
 ![![31, 0, 0], ![12, 1, 0], ![24, 0, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![12, 1, 0], ![2, 14, 6], ![58, -10, 10]]]
  hmulB := by decide  
  f := ![![![-277, -2361, -1014], ![-155, 5239, 0]], ![![-106, -908, -390], ![-61, 2015, 0]], ![![-216, -1828, -785], ![-116, 4056, 0]]]
  g := ![![![1, 0, 0], ![-12, 31, 0], ![-24, 0, 31]], ![![0, 1, 0], ![-10, 14, 6], ![-2, -10, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![31, 0, 0], ![-8, -12, 1]] ![![31, 0, 0], ![12, 1, 0]]
  ![![31, 0, 0]] where
 M := ![![![961, 0, 0], ![372, 31, 0]], ![![-248, -372, 31], ![-62, -186, -62]]]
 hmul := by decide  
 g := ![![![![31, 0, 0]], ![![12, 1, 0]]], ![![![-8, -12, 1]], ![![-2, -6, -2]]]]
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


lemma PB95I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB95I0 : PrimesBelowBoundCertificateInterval O 1 31 95 where
  m := 11
  g := ![3, 3, 1, 1, 3, 2, 1, 1, 2, 2, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB95I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N0, I2N1]
    · exact ![I3N0, I3N0, I3N1]
    · exact ![I5N0]
    · exact ![I7N0]
    · exact ![I11N0, I11N1, I11N2]
    · exact ![I13N0, I13N1]
    · exact ![I17N0]
    · exact ![I19N0]
    · exact ![I23N0, I23N1]
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
    · exact ![125]
    · exact ![343]
    · exact ![11, 11, 11]
    · exact ![169, 13]
    · exact ![4913]
    · exact ![6859]
    · exact ![529, 23]
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
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
    · dsimp ; intro j
      fin_cases j
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
  β := ![I2N0, I2N1, I3N0, I3N1, I11N0, I11N1, I11N2, I13N1, I23N1, I29N1, I31N1]
  Il := ![[I2N0, I2N0, I2N1], [I3N0, I3N0, I3N1], [], [], [I11N0, I11N1, I11N2], [I13N1], [], [], [I23N1], [I29N1], [I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
