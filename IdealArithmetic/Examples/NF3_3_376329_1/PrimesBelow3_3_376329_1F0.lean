
import IdealArithmetic.Examples.NF3_3_376329_1.RI3_3_376329_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-33637, 3065, 671]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![-33637, 3065, 671]] 
 ![![2, 0, 0], ![0, 1, 0], ![1, 0, 1]] where
  M :=![![![-33637, 3065, 671], ![-305976, 27805, 6130], ![-1244652, 113667, 24740]]]
  hmulB := by decide  
  f := ![![![8883010, -442457, -131295]], ![![29935260, -1491056, -442457]], ![![90354071, -4500478, -1335475]]]
  g := ![![![-17154, 3065, 671], ![-156053, 27805, 6130], ![-634696, 113667, 24740]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-653738, 59356, 13115]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![-653738, 59356, 13115]] 
 ![![2, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![-653738, 59356, 13115], ![-5980440, 546623, 118712], ![-24076116, 2173752, 487267]]]
  hmulB := by decide  
  f := ![![![8300901917, -413462572, -122691173]], ![![27973587444, -1393346353, -413462572]], ![![80282672694, -3998828160, -1186615067]]]
  g := ![![![-326869, 59356, 13115], ![-2990220, 546623, 118712], ![-12038058, 2173752, 487267]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5155, -1247, 168]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![5155, -1247, 168]] 
 ![![2, 0, 0], ![1, 1, 0], ![1, 0, 1]] where
  M :=![![![5155, -1247, 168], ![-76608, 18524, -2494], ![606936, -146793, 19771]]]
  hmulB := by decide  
  f := ![![![136262, -6787, -2014]], ![![527323, -26265, -7794]], ![![1385971, -69032, -20485]]]
  g := ![![![3117, -1247, 168], ![-46319, 18524, -2494], ![366979, -146793, 19771]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![-33637, 3065, 671]] ![![-653738, 59356, 13115]]
  ![![-12495337330, 1137429315, 249659182]] where
 M := ![![![-12495337330, 1137429315, 249659182]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![-12495337330, 1137429315, 249659182]] ![![5155, -1247, 168]]
  ![![2, 0, 0]] where
 M := ![![![-22503613318, 3205978244, 46304272]]]
 hmul := by decide  
 g := ![![![![-11251806659, 1602989122, 23152136]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-153987, 7670, 2276]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![-153987, 7670, 2276]] 
 ![![3, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![-153987, 7670, 2276], ![-1037856, 51695, 15340], ![-2978592, 148362, 44025]]]
  hmulB := by decide  
  f := ![![![-705, 162, -20]], ![![3040, -761, 108]], ![![-26144, 6218, -815]]]
  g := ![![![-51329, 7670, 2276], ![-345952, 51695, 15340], ![-992864, 148362, 44025]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-456881359, 22756966, 6752918]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![-456881359, 22756966, 6752918]] 
 ![![3, 0, 0], ![2, 1, 0], ![0, 0, 1]] where
  M :=![![![-456881359, 22756966, 6752918], ![-3079330608, 153379473, 45513932], ![-8837511192, 440190738, 130622507]]]
  hmulB := by decide  
  f := ![![![-30763005, 7439722, -1001902]], ![![131780434, -31869771, 4291880]], ![![-1206982296, 291896490, -39309493]]]
  g := ![![![-167465097, 22756966, 6752918], ![-1128696518, 153379473, 45513932], ![-3239297556, 440190738, 130622507]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![-153987, 7670, 2276]] ![![-153987, 7670, 2276]]
  ![![8972365257, -446907728, -132615712]] where
 M := ![![![8972365257, -446907728, -132615712]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![8972365257, -446907728, -132615712]] ![![-456881359, 22756966, 6752918]]
  ![![3, 0, 0]] where
 M := ![![![-1551136947245356935, 77261131157187462, 22926522135073446]]]
 hmul := by decide  
 g := ![![![![-517045649081785645, 25753710385729154, 7642174045024482]]]]
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
  c := ![-1206800, 670280, -189020]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-241360, 134056, -37804]
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


def P7P0 : CertificateIrreducibleZModOfList' 7 3 2 2 [1, 2, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 3, 6], [5, 3, 1], [0, 1]]
 g := ![![[4, 4, 1], [1]], ![[2, 0, 1, 3], [6, 6, 1, 6]], ![[0, 6, 1, 1], [6, 1, 3, 1]]]
 h' := ![![[3, 3, 6], [6, 5, 1], [0, 1]], ![[5, 3, 1], [0, 0, 5], [3, 3, 6]], ![[0, 1], [0, 2, 1], [5, 3, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2], []]
 b := ![[], [2, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 3
  hpos := by decide
  P := [1, 2, 6, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6018292, -2188809, 483364]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![859756, -312687, 69052]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-41890163, 2086522, 619156]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![-41890163, 2086522, 619156]] 
 ![![11, 0, 0], ![0, 11, 0], ![7, 2, 1]] where
  M :=![![![-41890163, 2086522, 619156], ![-282335136, 14062931, 4173044], ![-810286464, 40359846, 11976409]]]
  hmulB := by decide  
  f := ![![![-18505, 4502, -612]], ![![279072, -67247, 9004]], ![![-160349, 38930, -5275]]]
  g := ![![![-4202205, 77110, 619156], ![-28322404, 519713, 4173044], ![-81283757, 1491548, 11976409]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [6, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 10], [0, 1]]
 g := ![![[9, 9], [0, 1], [1]], ![[7, 2], [1, 10], [1]]]
 h' := ![![[1, 10], [0, 8], [5, 1], [0, 1]], ![[0, 1], [8, 3], [6, 10], [1, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [10, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 2
  hpos := by decide
  P := [6, 10, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3690, -228, 205]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![205, -58, 205]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![18505, -4502, 612]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![18505, -4502, 612]] 
 ![![11, 0, 0], ![7, 1, 0], ![5, 0, 1]] where
  M :=![![![18505, -4502, 612], ![-279072, 67247, -9004], ![2192448, -531210, 71749]]]
  hmulB := by decide  
  f := ![![![41890163, -2086522, -619156]], ![![52324207, -2606235, -773376]], ![![92703389, -4617496, -1370199]]]
  g := ![![![4269, -4502, 612], ![-64071, 67247, -9004], ![504743, -531210, 71749]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![-41890163, 2086522, 619156]] ![![18505, -4502, 612]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![251, -60, 8]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![251, -60, 8]] 
 ![![13, 0, 0], ![0, 13, 0], ![7, 12, 1]] where
  M :=![![![251, -60, 8], ![-3648, 887, -120], ![29184, -7044, 947]]]
  hmulB := by decide  
  f := ![![![407, -36, -8]], ![![3648, -325, -72]], ![![4709, -420, -93]]]
  g := ![![![15, -12, 8], ![-216, 179, -120], ![1735, -1416, 947]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [4, 1, 1] where
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
 g := ![![[10, 10], [9], [12, 1]], ![[0, 3], [9], [11, 12]]]
 h' := ![![[12, 12], [6, 6], [4, 10], [0, 1]], ![[0, 1], [0, 7], [7, 3], [12, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [7, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 2
  hpos := by decide
  P := [4, 1, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3414, -3962, 2168]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1430, -2306, 2168]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-407, 36, 8]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![-407, 36, 8]] 
 ![![13, 0, 0], ![2, 1, 0], ![10, 0, 1]] where
  M :=![![![-407, 36, 8], ![-3648, 325, 72], ![-14592, 1308, 289]]]
  hmulB := by decide  
  f := ![![![-251, 60, -8]], ![![242, -59, 8]], ![![-2438, 588, -79]]]
  g := ![![![-43, 36, 8], ![-386, 325, 72], ![-1546, 1308, 289]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![251, -60, 8]] ![![-407, 36, 8]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1603, 146, 32]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![-1603, 146, 32]] 
 ![![17, 0, 0], ![5, 1, 0], ![2, 0, 1]] where
  M :=![![![-1603, 146, 32], ![-14592, 1327, 292], ![-59280, 5406, 1181]]]
  hmulB := by decide  
  f := ![![![11365, -566, -168]], ![![7849, -391, -116]], ![![14266, -710, -211]]]
  g := ![![![-141, 146, 32], ![-1283, 1327, 292], ![-5216, 5406, 1181]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N0 : Nat.card (O ⧸ I17N0) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N0)

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := prime_ideal_of_norm_prime hp17.out _ NI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-56095, 11210, -1006]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![-56095, 11210, -1006]] 
 ![![17, 0, 0], ![14, 1, 0], ![14, 0, 1]] where
  M :=![![![-56095, 11210, -1006], ![458736, -132407, 22420], ![-5341128, 1204638, -143617]]]
  hmulB := by decide  
  f := ![![![7992087841, -398080742, -118126758]], ![![9750295966, -485655955, -144113888]], ![![15675361606, -780779654, -231689101]]]
  g := ![![![-11703, 11210, -1006], ![117562, -132407, 22420], ![-1187966, 1204638, -143617]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![-1603, 146, 32]] ![![-56095, 11210, -1006]]
  ![![-14020355, 1247364, 290194]] where
 M := ![![![-14020355, 1247364, 290194]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI17N1 : IdealMulLeCertificate' Table 
  ![![-14020355, 1247364, 290194]] ![![-56095, 11210, -1006]]
  ![![17, 0, 0]] where
 M := ![![![-191280713203, 27250815074, 393586312]]]
 hmul := by decide  
 g := ![![![![-11251806659, 1602989122, 23152136]]]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![21022075, -1047096, -310716]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![21022075, -1047096, -310716]] 
 ![![19, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![21022075, -1047096, -310716], ![141686496, -7057313, -2094192], ![406632528, -20254104, -6010217]]]
  hmulB := by decide  
  f := ![![![2953, -1368, 324]], ![![-7776, 1567, -144]], ![![36720, -10152, 1639]]]
  g := ![![![1106425, -1047096, -310716], ![7457184, -7057313, -2094192], ![21401712, -20254104, -6010217]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N0 : Nat.card (O ⧸ I19N0) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N0)

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := prime_ideal_of_norm_prime hp19.out _ NI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2953, 1368, -324]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![-2953, 1368, -324]] 
 ![![19, 0, 0], ![0, 19, 0], ![8, 0, 1]] where
  M :=![![![-2953, 1368, -324], ![147744, -29773, 2736], ![-697680, 192888, -31141]]]
  hmulB := by decide  
  f := ![![![-21022075, 1047096, 310716]], ![![-141686496, 7057313, 2094192]], ![![-30253112, 1506888, 447155]]]
  g := ![![![-19, 72, -324], ![6624, -1567, 2736], ![-23608, 10152, -31141]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P1 : CertificateIrreducibleZModOfList' 19 2 2 4 [3, 11, 1] where
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
 g := ![![[10, 16], [16, 7], [7], [1]], ![[5, 3], [15, 12], [7], [1]]]
 h' := ![![[8, 18], [9, 4], [7, 8], [16, 8], [0, 1]], ![[0, 1], [3, 15], [14, 11], [4, 11], [8, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [6, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N1 : CertifiedPrimeIdeal' SI19N1 19 where
  n := 2
  hpos := by decide
  P := [3, 11, 1]
  hirr := P19P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3417, -1026, 758]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-499, -54, 758]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N1 B_one_repr
lemma NI19N1 : Nat.card (O ⧸ I19N1) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![21022075, -1047096, -310716]] ![![-2953, 1368, -324]]
  ![![19, 0, 0]] where
 M := ![![![-19, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [22, 18, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 16, 20], [9, 6, 3], [0, 1]]
 g := ![![[11, 12, 8], [15, 16, 8], [14, 20, 1], []], ![[21, 5, 4, 21], [4, 16, 15, 15], [14, 7, 16, 7], [15, 9]], ![[10, 20, 20, 13], [21, 10, 10, 6], [3, 21, 18, 9], [9, 9]]]
 h' := ![![[11, 16, 20], [15, 11, 10], [14, 21, 13], [0, 0, 1], [0, 1]], ![[9, 6, 3], [1, 5, 4], [12, 1, 15], [21, 22, 6], [11, 16, 20]], ![[0, 1], [2, 7, 9], [16, 1, 18], [21, 1, 16], [9, 6, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 19], []]
 b := ![[], [14, 2, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [22, 18, 3, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![87836816, -175187320, 64778626]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3818992, -7616840, 2816462]
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


def P29P0 : CertificateIrreducibleZModOfList' 29 3 2 4 [25, 13, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 7, 15], [17, 21, 14], [0, 1]]
 g := ![![[10, 7, 24], [25, 9], [7, 25, 1], [1]], ![[0, 2, 1, 2], [4, 9], [17, 17, 2, 12], [16, 17, 16, 11]], ![[21, 20, 18, 18], [0, 7], [6, 13, 4, 18], [15, 4, 5, 18]]]
 h' := ![![[11, 7, 15], [14, 9, 13], [28, 25, 3], [4, 16, 28], [0, 1]], ![[17, 21, 14], [7, 2, 2], [22, 7, 3], [3, 23, 16], [11, 7, 15]], ![[0, 1], [6, 18, 14], [21, 26, 23], [14, 19, 14], [17, 21, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 22], []]
 b := ![[], [6, 2, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 3
  hpos := by decide
  P := [25, 13, 1, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-118320, 2494, 6989]
  a := ![-1, 2, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4080, 86, 241]
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


def P31P0 : CertificateIrreducibleZModOfList' 31 3 2 4 [15, 21, 26, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 15, 19], [24, 15, 12], [0, 1]]
 g := ![![[24, 26, 16], [3, 3, 8], [23, 8, 25], [1]], ![[0, 29, 24, 4], [17, 14, 0, 14], [27, 28, 21, 4], [25, 4, 10, 8]], ![[5, 9, 4, 22], [24, 6, 0, 13], [11, 22, 14, 11], [20, 27, 23, 23]]]
 h' := ![![[12, 15, 19], [17, 1, 4], [27, 25, 16], [16, 10, 5], [0, 1]], ![[24, 15, 12], [23, 23, 17], [24, 4, 2], [20, 5, 17], [12, 15, 19]], ![[0, 1], [10, 7, 10], [7, 2, 13], [8, 16, 9], [24, 15, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 15], []]
 b := ![[], [30, 15, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 3
  hpos := by decide
  P := [15, 21, 26, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6317211, -3381108, 952692]
  a := ![0, 3, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![203781, -109068, 30732]
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



lemma PB137I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB137I0 : PrimesBelowBoundCertificateInterval O 1 31 137 where
  m := 11
  g := ![3, 3, 1, 1, 2, 2, 3, 2, 1, 1, 1]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB137I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N2]
    · exact ![I3N0, I3N0, I3N1]
    · exact ![I5N0]
    · exact ![I7N0]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1]
    · exact ![I17N0, I17N1, I17N1]
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
    · exact ![125]
    · exact ![343]
    · exact ![121, 11]
    · exact ![169, 13]
    · exact ![17, 17, 17]
    · exact ![19, 361]
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
      exact NI2N2
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
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I5N0, I11N0, I11N1, I13N1, I17N0, I17N1, I19N0]
  Il := ![[I2N0, I2N1, I2N2], [I3N0, I3N0, I3N1], [I5N0], [], [I11N0, I11N1], [I13N1], [I17N0, I17N1, I17N1], [I19N0], [], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
