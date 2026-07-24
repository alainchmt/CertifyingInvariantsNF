
import IdealArithmetic.Examples.NF5_3_1125000000_3.RI5_3_1125000000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0, 0, 0]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0, 0, 0]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![0, 0, 0, 29, 0], ![0, 0, 0, 0, 29]] where
  M :=![![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![0, 0, 0, 29, 0], ![0, 0, 0, 0, 29]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 5 2 4 [20, 20, 16, 23, 10, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 14, 27, 20, 16], [0, 9, 6, 10, 8], [0, 8, 16, 16, 3], [13, 26, 9, 12, 2], [0, 1]]
 g := ![![[20, 8, 11, 27, 13], [0, 20, 23, 25], [19, 19, 1], []], ![[6, 3, 17, 12, 1, 6, 10, 24], [8, 11, 10, 4], [1, 6, 4, 4, 28, 2, 14, 28], [18, 14, 6, 19, 12, 4, 7, 7]], ![[0, 13, 9, 3, 16, 16, 10, 27], [27, 3, 21, 1], [23, 25, 6, 15, 9, 25, 16, 10], [1, 13, 15, 10, 6, 25, 19, 19]], ![[24, 6, 11, 0, 25, 19, 5, 19], [1, 11, 2, 7], [13, 8, 11, 22, 27, 26, 0, 3], [11, 27, 2, 25, 15, 2, 17, 27]], ![[22, 1, 0, 8, 9, 12, 6, 21], [19, 4], [5, 28, 26, 1, 0, 11, 14, 19], [23, 10, 18, 24, 24, 3, 6, 8]]]
 h' := ![![[6, 14, 27, 20, 16], [9, 13, 7, 18, 10], [26, 23, 21, 22, 24], [0, 0, 0, 1], [0, 1]], ![[0, 9, 6, 10, 8], [7, 11, 26, 28, 4], [15, 14, 1, 2, 27], [1, 2, 14, 3, 3], [6, 14, 27, 20, 16]], ![[0, 8, 16, 16, 3], [27, 17, 0, 4, 6], [4, 1, 16, 1, 1], [9, 10, 4, 27, 9], [0, 9, 6, 10, 8]], ![[13, 26, 9, 12, 2], [10, 6, 2, 18, 4], [1, 7, 13, 6, 6], [12, 23, 27, 12, 1], [0, 8, 16, 16, 3]], ![[0, 1], [25, 11, 23, 19, 5], [17, 13, 7, 27], [26, 23, 13, 15, 16], [13, 26, 9, 12, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 7, 26, 5], [], [], []]
 b := ![[], [27, 3, 0, 26, 16], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 5
  hpos := by decide
  P := [20, 20, 16, 23, 10, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-343942636815441426, -342262729762097576, 114545278208793646, -509500252000331884, -471218039279521194]
  a := ![-176, -194, 145, -109, -324]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-11860090924670394, -11802163095244744, 3949837179613574, -17568974206907996, -16248897906190386]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 20511149 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def PBC29 : ContainsPrimesAboveP 29 ![I29N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![29, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 29 (by decide) 𝕀

instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1018, 2459, 1396, -791, -2010]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![1018, 2459, 1396, -791, -2010]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![30, 2, 25, 3, 1]] where
  M :=![![![1018, 2459, 1396, -791, -2010], ![1192, 2824, 1603, -910, -2308], ![1362, 3259, 1848, -1048, -2664], ![-875, -2094, -1189, 672, 1712], ![-333, -791, -448, 255, 643]]]
  hmulB := by decide  
  f := ![![![-2, 1, 0, -1, 0]], ![![-4, -6, 5, -2, -8]], ![![6, 5, -14, -8, 0]], ![![-7, -6, 1, -14, -2]], ![![2, 4, -11, -9, -1]]]
  g := ![![![1978, 209, 1666, 169, -2010], ![2272, 240, 1913, 194, -2308], ![2622, 277, 2208, 224, -2664], ![-1685, -178, -1419, -144, 1712], ![-633, -67, -533, -54, 643]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 4 2 4 [20, 20, 25, 7, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [14, 29, 22, 12], [5, 5, 12, 21], [5, 27, 28, 29], [0, 1]]
 g := ![![[21, 21, 0, 19], [17, 4, 6, 10], [18, 24, 24, 1], []], ![[25, 14, 14, 11, 3, 12], [25, 5, 28, 8, 12, 22], [28, 14, 23, 1, 27, 22], [1, 3, 10, 29, 12, 23]], ![[20, 21, 23, 7, 0, 13], [20, 18, 10, 23, 14, 24], [7, 10, 2, 29], [12, 26, 7, 29, 29, 23]], ![[18, 6, 1, 12, 3, 12], [18, 7, 15, 24, 9, 26], [22, 3, 0, 20, 4, 6], [19, 25, 29, 20, 20, 23]]]
 h' := ![![[14, 29, 22, 12], [1, 3, 16, 9], [12, 28, 16, 14], [0, 0, 0, 1], [0, 1]], ![[5, 5, 12, 21], [5, 27, 4, 1], [5, 21, 14, 10], [27, 15, 16, 10], [14, 29, 22, 12]], ![[5, 27, 28, 29], [22, 13, 16, 16], [17, 11, 0, 14], [9, 18, 5], [5, 5, 12, 21]], ![[0, 1], [14, 19, 26, 5], [22, 2, 1, 24], [24, 29, 10, 20], [5, 27, 28, 29]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [27, 27, 22], []]
 b := ![[], [], [10, 24, 4, 27], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 4
  hpos := by decide
  P := [20, 20, 25, 7, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2082354959533097527, 2068981734767071422, -673475693158652264, 3117944625470047742, 2835961103147717733]
  a := ![-2547, -2778, 1994, -1752, -4457]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2677305746287046273, -116223886178334324, -2308790428124245019, -173868989805584047, 2835961103147717733]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 923521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, -1, 0, 1, 0]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![2, -1, 0, 1, 0]] 
 ![![31, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![12, 0, 1, 0, 0], ![11, 0, 0, 1, 0], ![14, 0, 0, 0, 1]] where
  M :=![![![2, -1, 0, 1, 0], ![4, 6, -5, 2, 8], ![-6, -5, 14, 8, 0], ![7, 6, -1, 14, 2], ![-1, 1, 4, 3, 9]]]
  hmulB := by decide  
  f := ![![![-1018, -2459, -1396, 791, 2010]], ![![-334, -805, -457, 259, 658]], ![![-438, -1057, -600, 340, 864]], ![![-333, -805, -457, 259, 658]], ![![-449, -1085, -616, 349, 887]]]
  g := ![![![0, -1, 0, 1, 0], ![-4, 6, -5, 2, 8], ![-7, -5, 14, 8, 0], ![-7, 6, -1, 14, 2], ![-7, 1, 4, 3, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![1018, 2459, 1396, -791, -2010]] ![![2, -1, 0, 1, 0]]
  ![![31, 0, 0, 0, 0]] where
 M := ![![![-31, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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
instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![707, -97, -211, 214, 404]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![707, -97, -211, 214, 404]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![11, 20, 21, 15, 1]] where
  M :=![![![707, -97, -211, 214, 404], ![398, 912, -145, 1128, 904], ![5450, 5089, -1792, 7748, 7216], ![2370, 2560, -790, 3733, 3384], ![3700, 3589, -1221, 5402, 4995]]]
  hmulB := by decide  
  f := ![![![3, 7, -1, -6, 4]], ![![-22, -22, 39, 8, -56]], ![![154, 149, -166, 36, 176]], ![![-34, -24, 14, -43, 16]], ![![65, 67, -70, 7, 79]]]
  g := ![![![-101, -221, -235, -158, 404], ![-258, -464, -517, -336, 904], ![-1998, -3763, -4144, -2716, 7216], ![-942, -1760, -1942, -1271, 3384], ![-1385, -2603, -2868, -1879, 4995]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 4 2 5 [27, 26, 25, 21, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 15, 24, 22], [12, 5, 9, 30], [34, 16, 4, 22], [0, 1]]
 g := ![![[34, 28, 6, 33], [10, 33, 7], [20, 27, 3, 34], [1], []], ![[4, 3, 26, 7, 3, 6], [12, 11, 26], [21, 10, 18, 24, 7, 18], [7, 5, 26], [29, 31, 3]], ![[21, 17, 0, 22, 4, 33], [17, 0, 16], [31, 33, 35, 2, 20, 1], [29, 14, 30], [27, 29, 12]], ![[0, 26, 10, 17, 8, 18], [11, 27, 11], [5, 5, 30, 20, 10, 8], [23, 22, 12], [11, 2, 3]]]
 h' := ![![[7, 15, 24, 22], [29, 10, 6, 12], [15, 35, 10, 9], [10, 11, 12, 16], [0, 0, 1], [0, 1]], ![[12, 5, 9, 30], [12, 31, 17, 9], [15, 9, 26, 10], [32, 20, 30, 13], [6, 25, 22, 10], [7, 15, 24, 22]], ![[34, 16, 4, 22], [26, 13, 10, 29], [2, 12, 5, 4], [6, 34, 0, 24], [7, 4, 5, 20], [12, 5, 9, 30]], ![[0, 1], [0, 20, 4, 24], [1, 18, 33, 14], [35, 9, 32, 21], [8, 8, 9, 7], [34, 16, 4, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [35, 24, 3], []]
 b := ![[], [], [20, 30, 16, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 4
  hpos := by decide
  P := [27, 26, 25, 21, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![18642413156638, 18528770061070, -6045855779590, 27884675616465, 25419352442405]
  a := ![-139, -151, 107, -99, -239]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-7053255775941, -13239412940190, -14590601542435, -9551503000530, 25419352442405]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1874161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 7, -1, -6, 4]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![3, 7, -1, -6, 4]] 
 ![![37, 0, 0, 0, 0], ![30, 1, 0, 0, 0], ![25, 0, 1, 0, 0], ![18, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![3, 7, -1, -6, 4], ![-22, -22, 39, 8, -56], ![154, 149, -166, 36, 176], ![-34, -24, 14, -43, 16], ![88, 73, -83, 54, 63]]]
  hmulB := by decide  
  f := ![![![707, -97, -211, 214, 404]], ![![584, -54, -175, 204, 352]], ![![625, 72, -191, 354, 468]], ![![408, 22, -124, 205, 288]], ![![100, 97, -33, 146, 135]]]
  g := ![![![-2, 7, -1, -6, 4], ![-13, -22, 39, 8, -56], ![-22, 149, -166, 36, 176], ![30, -24, 14, -43, 16], ![-27, 73, -83, 54, 63]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![707, -97, -211, 214, 404]] ![![3, 7, -1, -6, 4]]
  ![![37, 0, 0, 0, 0]] where
 M := ![![![37, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2781, 2764, -920, 4130, 3802]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![2781, 2764, -920, 4130, 3802]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![27, 24, 10, 1, 0], ![37, 8, 14, 0, 1]] where
  M :=![![![2781, 2764, -920, 4130, 3802], ![18604, 18503, -6152, 27636, 25436], ![124504, 123824, -41169, 184936, 170216], ![60288, 59960, -19934, 89551, 82422], ![86918, 86444, -28740, 129106, 118829]]]
  hmulB := by decide  
  f := ![![![33, -12, -20, 6, 26]], ![![-44, -17, 16, -20, -4]], ![![8, -48, 55, 120, -152]], ![![-1, -28, 8, 21, -20]], ![![23, -32, 6, 44, -33]]]
  g := ![![![-6083, -3092, -2328, 4130, 3802], ![-40700, -20689, -15576, 27636, 25436], ![-272360, -138448, -104233, 184936, 170216], ![-131883, -67040, -50472, 89551, 82422], ![-190137, -96652, -72766, 129106, 118829]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [6, 2, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 21, 37], [12, 19, 4], [0, 1]]
 g := ![![[16, 39, 37], [30, 31], [37, 36], [2, 39, 1], []], ![[40, 6, 3, 20], [39, 18], [37, 37], [27, 34, 9, 32], [5, 16]], ![[1, 14, 19, 8], [39, 39], [19, 21], [33, 11, 1, 1], [38, 16]]]
 h' := ![![[27, 21, 37], [0, 39, 23], [4, 10, 21], [29, 8, 35], [0, 0, 1], [0, 1]], ![[12, 19, 4], [33, 27, 35], [29, 27, 31], [28, 27, 18], [2, 3, 19], [27, 21, 37]], ![[0, 1], [12, 16, 24], [0, 4, 30], [14, 6, 29], [39, 38, 21], [12, 19, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34, 24], []]
 b := ![[], [35, 30, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [6, 2, 2, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1279527762559, 1282674805626, -474610585428, 1814230736414, 1801847180611]
  a := ![1030, 1133, -838, 655, 1873]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2789586531786, -1382283910078, -1069336060442, 1814230736414, 1801847180611]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 68921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 104, 60, -34, -86]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![43, 104, 60, -34, -86]] 
 ![![41, 0, 0, 0, 0], ![20, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![37, 0, 0, 1, 0], ![27, 0, 0, 0, 1]] where
  M :=![![![43, 104, 60, -34, -86], ![52, 121, 68, -36, -100], ![64, 148, 65, -56, -88], ![-44, -96, -42, 29, 62], ![-6, -24, -32, 6, 47]]]
  hmulB := by decide  
  f := ![![![-313, -40, 96, -182, -238]], ![![-168, -39, 52, -116, -140]], ![![-202, -132, 65, -228, -228]], ![![-341, -96, 106, -253, -296]], ![![-293, -112, 92, -248, -275]]]
  g := ![![![23, 104, 60, -34, -86], ![24, 121, 68, -36, -100], ![22, 148, 65, -56, -88], ![-11, -96, -42, 29, 62], ![-17, -24, -32, 6, 47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-165, 60, 48, -12, -68]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![-165, 60, 48, -12, -68]] 
 ![![41, 0, 0, 0, 0], ![24, 1, 0, 0, 0], ![39, 0, 1, 0, 0], ![15, 0, 0, 1, 0], ![31, 0, 0, 0, 1]] where
  M :=![![![-165, 60, 48, -12, -68], ![104, -41, -28, 8, 40], ![-56, 36, 7, 0, -16], ![40, -16, -12, -1, 20], ![-12, 12, 0, 4, -5]]]
  hmulB := by decide  
  f := ![![![-101, -220, -112, 44, 148]], ![![-64, -137, -68, 24, 88]], ![![-115, -232, -105, 20, 124]], ![![-43, -84, -36, 3, 40]], ![![-87, -176, -80, 16, 95]]]
  g := ![![![-29, 60, 48, -12, -68], ![20, -41, -28, 8, 40], ![-17, 36, 7, 0, -16], ![7, -16, -12, -1, 20], ![-5, 12, 0, 4, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![2781, 2764, -920, 4130, 3802]] ![![43, 104, 60, -34, -86]]
  ![![-101, -220, -112, 44, 148]] where
 M := ![![![-101, -220, -112, 44, 148]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![-101, -220, -112, 44, 148]] ![![-165, 60, 48, -12, -68]]
  ![![41, 0, 0, 0, 0]] where
 M := ![![![41, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1, I41N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
    exact isPrimeI41N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0 ⊙ MulI41N1)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![533, 545, -177, 808, 740]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![533, 545, -177, 808, 740]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![6, 3, 1, 0, 0], ![42, 36, 0, 1, 0], ![9, 17, 0, 0, 1]] where
  M :=![![![533, 545, -177, 808, 740], ![3650, 3620, -1207, 5412, 4984], ![24374, 24247, -8060, 36212, 33328], ![11808, 11740, -3904, 17535, 16140], ![17018, 16927, -5627, 25280, 23267]]]
  hmulB := by decide  
  f := ![![![-1, 7, -33, -32, 68]], ![![-190, -226, 271, 84, -392]], ![![14, 11, -17, 8, 16]], ![![-166, -186, 198, 31, -260]], ![![-59, -74, 85, 36, -129]]]
  g := ![![![-907, -944, -177, 808, 740], ![-6076, -6333, -1207, 5412, 4984], ![-40654, -42367, -8060, 36212, 33328], ![-19686, -20516, -3904, 17535, 16140], ![-28381, -29577, -5627, 25280, 23267]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [37, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 42], [0, 1]]
 g := ![![[26, 15], [31, 17], [16], [12, 41], [1]], ![[1, 28], [17, 26], [16], [1, 2], [1]]]
 h' := ![![[27, 42], [14, 31], [34, 19], [29, 4], [6, 27], [0, 1]], ![[0, 1], [34, 12], [31, 24], [8, 39], [4, 16], [27, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [11, 39]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [37, 16, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1277064, 1135898, -6739, 2616102, 1074169]
  a := ![-241, -275, 228, -100, -509]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2749449, -2588010, -6739, 2616102, 1074169]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![168, 222, -57, 307, 268]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![168, 222, -57, 307, 268]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![32, 34, 1, 0, 0], ![3, 25, 0, 1, 0], ![34, 29, 0, 0, 1]] where
  M :=![![![168, 222, -57, 307, 268], ![1422, 1379, -470, 2074, 1920], ![9316, 9288, -3077, 13868, 12752], ![4533, 4494, -1499, 6718, 6186], ![6511, 6482, -2151, 9681, 8907]]]
  hmulB := by decide  
  f := ![![![-21576, -51454, -29193, 16561, 42034]], ![![-24846, -59263, -33630, 19078, 48420]], ![![-36368, -86738, -49217, 27920, 70864]], ![![-15523, -37025, -21010, 11919, 30250]], ![![-33655, -80267, -45545, 25837, 65577]]]
  g := ![![![-187, -309, -57, 307, 268], ![-1280, -2097, -470, 2074, 1920], ![-8544, -14014, -3077, 13868, 12752], ![-4139, -6788, -1499, 6718, 6186], ![-5966, -9784, -2151, 9681, 8907]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P1 : CertificateIrreducibleZModOfList' 43 2 2 5 [21, 38, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 42], [0, 1]]
 g := ![![[10, 41], [12, 36], [6], [1, 25], [1]], ![[0, 2], [20, 7], [6], [40, 18], [1]]]
 h' := ![![[5, 42], [6, 16], [14, 37], [22, 7], [22, 5], [0, 1]], ![[0, 1], [0, 27], [27, 6], [14, 36], [4, 38], [5, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [40, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N1 : CertifiedPrimeIdeal' SI43N1 43 where
  n := 2
  hpos := by decide
  P := [21, 38, 1]
  hirr := P43P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![273253, 172172, 32884, 644928, -106912]
  a := ![98, 126, -136, -32, 304]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![21423, -324852, 32884, 644928, -106912]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N1 B_one_repr
lemma NI43N1 : Nat.card (O ⧸ I43N1) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N1

def I43N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![654, 1590, 903, -511, -1300]] i)))

def SI43N2: IdealEqSpanCertificate' Table ![![654, 1590, 903, -511, -1300]] 
 ![![43, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![16, 0, 0, 1, 0], ![28, 0, 0, 0, 1]] where
  M :=![![![654, 1590, 903, -511, -1300], ![774, 1825, 1034, -586, -1488], ![884, 2112, 1193, -668, -1712], ![-561, -1350, -769, 440, 1110], ![-211, -506, -291, 171, 423]]]
  hmulB := by decide  
  f := ![![![-78, -134, 207, 203, -406]], ![![18, 13, -12, 20, 0]], ![![-178, -174, 212, -21, -246]], ![![1, -34, 67, 126, -176]], ![![-143, -162, 215, 67, -315]]]
  g := ![![![683, 1590, 903, -511, -1300], ![782, 1825, 1034, -586, -1488], ![895, 2112, 1193, -668, -1712], ![-586, -1350, -769, 440, 1110], ![-226, -506, -291, 171, 423]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N2 : Nat.card (O ⧸ I43N2) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N2)

lemma isPrimeI43N2 : Ideal.IsPrime I43N2 := prime_ideal_of_norm_prime hp43.out _ NI43N2
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![533, 545, -177, 808, 740]] ![![168, 222, -57, 307, 268]]
  ![![7696406, 7653737, -2544834, 11431409, 10521608]] where
 M := ![![![7696406, 7653737, -2544834, 11431409, 10521608]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![7696406, 7653737, -2544834, 11431409, 10521608]] ![![654, 1590, 903, -511, -1300]]
  ![![43, 0, 0, 0, 0]] where
 M := ![![![74728969, 74330359, -24709735, 111010692, 102171526]]]
 hmul := by decide  
 g := ![![![![1737883, 1728613, -574645, 2581644, 2376082]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1, I43N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
    exact isPrimeI43N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0 ⊙ MulI43N1)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0, 0, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0, 0, 0]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![0, 0, 0, 0, 47]] where
  M :=![![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![0, 0, 0, 0, 47]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 5 2 5 [35, 0, 17, 5, 38, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [41, 5, 21, 6, 46], [14, 11, 26, 11, 19], [9, 34, 28, 10, 17], [39, 43, 19, 20, 12], [0, 1]]
 g := ![![[23, 17, 5, 40, 28], [24, 21, 12, 7, 1], [42, 11, 36, 28, 34], [1], []], ![[45, 3, 26, 9, 30, 5, 11, 31], [22, 37, 6, 34, 37, 33, 40, 38], [27, 27, 42, 21, 7, 20, 19, 23], [9, 35, 26, 3, 1, 45, 21, 35], [39, 9, 44, 1]], ![[9, 3, 9, 14, 31, 19, 5, 11], [20, 0, 43, 31, 22, 18, 29, 5], [43, 9, 19, 26, 7, 39, 12, 5], [33, 23, 36, 16, 16, 0, 13, 29], [39, 18, 1, 32]], ![[7, 38, 28, 42, 24, 8, 4, 3], [37, 16, 20, 31, 29, 24, 13, 4], [20, 30, 39, 40, 4, 33, 8, 6], [13, 0, 4, 4, 22, 29, 26, 42], [18, 38, 27, 7]], ![[8, 6, 25, 6, 20, 11, 1, 37], [2, 35, 28, 44, 6, 30, 11, 21], [27, 30, 10, 33, 15, 21, 21, 8], [29, 25, 2, 30, 10, 4, 11, 24], [43, 46, 37, 3]]]
 h' := ![![[41, 5, 21, 6, 46], [6, 45, 33, 19, 34], [34, 41, 0, 1, 46], [12, 0, 30, 42, 9], [0, 0, 1], [0, 1]], ![[14, 11, 26, 11, 19], [42, 21, 6, 22, 4], [15, 18, 29, 28, 3], [34, 11, 22, 34, 27], [34, 1, 14, 37, 24], [41, 5, 21, 6, 46]], ![[9, 34, 28, 10, 17], [12, 42, 17, 38, 14], [27, 15, 44, 28, 42], [7, 15, 8, 34, 5], [6, 7, 10, 11, 2], [14, 11, 26, 11, 19]], ![[39, 43, 19, 20, 12], [29, 36, 20, 18, 25], [11, 43, 1, 9, 35], [19, 4, 8, 32, 34], [15, 34, 33, 22, 14], [9, 34, 28, 10, 17]], ![[0, 1], [24, 44, 18, 44, 17], [0, 24, 20, 28, 15], [39, 17, 26, 46, 19], [16, 5, 36, 24, 7], [39, 43, 19, 20, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13, 2, 36, 43], [], [], []]
 b := ![[], [13, 36, 3, 1, 43], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 5
  hpos := by decide
  P := [35, 0, 17, 5, 38, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![14507163167189769516, 14439788139832471260, -4834465797072962887, 21483848650120979372, 19892232828149029719]
  a := ![374, 413, -313, 219, 701]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![308663046110420628, 307229534890052580, -102860974405807721, 457103162768531476, 423238996343596377]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 229345007 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def PBC47 : ContainsPrimesAboveP 47 ![I47N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![47, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 47 (by decide) 𝕀

instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17890, -42963, -24386, 13823, 35112]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-17890, -42963, -24386, 13823, 35112]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![5, 13, 12, 20, 1]] where
  M :=![![![-17890, -42963, -24386, 13823, 35112], ![-20800, -49416, -28031, 15910, 40360], ![-23826, -56955, -32336, 18328, 46560], ![15313, 36602, 20777, -11782, -29914], ![5817, 13831, 7834, -4451, -11281]]]
  hmulB := by decide  
  f := ![![![78, 77, -26, 115, 106]], ![![516, 514, -171, 766, 708]], ![![3454, 3433, -1134, 5144, 4712]], ![![1679, 1670, -559, 2488, 2296]], ![![1595, 1586, -527, 2370, 2179]]]
  g := ![![![-3650, -9423, -8410, -12989, 35112], ![-4200, -10832, -9667, -14930, 40360], ![-4842, -12495, -11152, -17224, 46560], ![3111, 8028, 7165, 11066, -29914], ![1174, 3028, 2702, 4173, -11281]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 4 2 5 [41, 29, 43, 50, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [33, 46, 22, 14], [30, 21, 8, 11], [46, 38, 23, 28], [0, 1]]
 g := ![![[16, 11, 45, 29], [26, 42, 43], [43, 22, 6, 25], [19, 3, 1], []], ![[29, 10, 43, 47, 27, 23], [12, 33, 9], [39, 5, 19, 12, 5, 32], [17, 51, 46], [12, 17, 48, 43, 21, 41]], ![[42, 45, 3, 48, 33, 36], [34, 39, 13], [15, 32, 35, 52, 33, 36], [45, 3, 25], [46, 7, 0, 11, 7, 6]], ![[12, 40, 11, 34, 50, 38], [26, 9, 49], [37, 14, 44, 16, 19, 29], [37, 45, 6], [46, 21, 24, 20, 13, 10]]]
 h' := ![![[33, 46, 22, 14], [31, 19, 9, 33], [39, 15, 26, 34], [16, 15, 9, 5], [0, 0, 0, 1], [0, 1]], ![[30, 21, 8, 11], [0, 47, 29, 15], [11, 12, 52, 50], [30, 12, 36, 48], [41, 42, 25, 29], [33, 46, 22, 14]], ![[46, 38, 23, 28], [38, 19, 0, 39], [1, 30, 0, 15], [21, 23, 0, 14], [45, 12, 14, 5], [30, 21, 8, 11]], ![[0, 1], [38, 21, 15, 19], [16, 49, 28, 7], [29, 3, 8, 39], [50, 52, 14, 18], [46, 38, 23, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [27, 9, 32], []]
 b := ![[], [], [2, 38, 42, 26], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 4
  hpos := by decide
  P := [41, 29, 43, 50, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5143357824211, 5115700950261, -1683454389004, 7667107609057, 7031959855279]
  a := ![-100, -107, 72, -79, -161]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-566347951928, -1628297682422, -1623905144384, -2508907348991, 7031959855279]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 7890481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-78, -77, 26, -115, -106]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-78, -77, 26, -115, -106]] 
 ![![53, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![52, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![16, 0, 0, 0, 1]] where
  M :=![![![-78, -77, 26, -115, -106], ![-516, -514, 171, -766, -708], ![-3454, -3433, 1134, -5144, -4712], ![-1679, -1670, 559, -2488, -2296], ![-2409, -2395, 790, -3589, -3289]]]
  hmulB := by decide  
  f := ![![![17890, 42963, 24386, -13823, -35112]], ![![730, 1743, 989, -561, -1424]], ![![18002, 43227, 24536, -13908, -35328]], ![![2749, 6605, 3749, -2125, -5398]], ![![5291, 12709, 7214, -4089, -10387]]]
  g := ![![![26, -77, 26, -115, -106], ![176, -514, 171, -766, -708], ![1183, -3433, 1134, -5144, -4712], ![567, -1670, 559, -2488, -2296], ![827, -2395, 790, -3589, -3289]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-17890, -42963, -24386, 13823, 35112]] ![![-78, -77, 26, -115, -106]]
  ![![53, 0, 0, 0, 0]] where
 M := ![![![-53, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15134, 36089, 20476, -11615, -29482]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![15134, 36089, 20476, -11615, -29482]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![41, 35, 10, 7, 1]] where
  M :=![![![15134, 36089, 20476, -11615, -29482], ![17432, 41572, 23585, -13374, -33956], ![20102, 47905, 27156, -15376, -39080], ![-12891, -30758, -17461, 9920, 25152], ![-4857, -11609, -6604, 3767, 9523]]]
  hmulB := by decide  
  f := ![![![34, -9, -12, 3, 16]], ![![-28, 2, 11, -10, -8]], ![![10, -21, 26, 48, -64]], ![![13, 26, -27, -6, 38]], ![![10, -6, 0, 4, -1]]]
  g := ![![![20744, 18101, 5344, 3301, -29482], ![23892, 20848, 6155, 3802, -33956], ![27498, 23995, 7084, 4376, -39080], ![-17697, -15442, -4559, -2816, 25152], ![-6700, -5846, -1726, -1066, 9523]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 4 2 5 [5, 31, 26, 56, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [49, 53, 9, 52], [48, 45, 42, 34], [24, 19, 8, 32], [0, 1]]
 g := ![![[2, 48, 43, 16], [12, 20, 1, 48], [15, 45, 29], [17, 42, 3, 1], []], ![[3, 52, 23, 31, 34, 47], [15, 55, 20, 52, 26, 33], [29, 38, 12], [49, 26, 54, 37, 43, 44], [19, 17, 30, 19, 58, 11]], ![[32, 16, 28, 16, 38, 52], [34, 13, 26, 37, 51, 40], [2, 56, 53], [28, 52, 46, 16, 17, 30], [43, 25, 24, 4, 15, 10]], ![[58, 11, 31, 1, 8, 18], [57, 47, 31, 15, 29, 31], [28, 55, 4], [14, 40, 10, 47, 50, 38], [31, 52, 37, 25, 42, 23]]]
 h' := ![![[49, 53, 9, 52], [58, 3, 8, 55], [11, 51, 50, 44], [33, 30, 11, 41], [0, 0, 0, 1], [0, 1]], ![[48, 45, 42, 34], [25, 12, 35, 26], [52, 10, 43, 18], [16, 3, 8, 37], [26, 4, 36, 45], [49, 53, 9, 52]], ![[24, 19, 8, 32], [42, 12, 57, 51], [41, 38, 21, 50], [46, 58, 36, 42], [47, 9, 39, 39], [48, 45, 42, 34]], ![[0, 1], [28, 32, 18, 45], [24, 19, 4, 6], [39, 27, 4, 57], [40, 46, 43, 33], [24, 19, 8, 32]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [3, 20, 28], []]
 b := ![[], [], [12, 28, 57, 20], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 4
  hpos := by decide
  P := [5, 31, 26, 56, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![506680804281277, 500861107341589, -160585342855183, 764999007546334, 677634437412856]
  a := ![325, 365, -289, 164, 647]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-462310697112641, -393497359357769, -117575079948877, -67431221260062, 677634437412856]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 12117361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-34, 9, 12, -3, -16]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![-34, 9, 12, -3, -16]] 
 ![![59, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![34, 0, 1, 0, 0], ![58, 0, 0, 1, 0], ![38, 0, 0, 0, 1]] where
  M :=![![![-34, 9, 12, -3, -16], ![28, -2, -11, 10, 8], ![-10, 21, -26, -48, 64], ![-13, -26, 27, 6, -38], ![15, 27, -36, -25, 61]]]
  hmulB := by decide  
  f := ![![![-15134, -36089, -20476, 11615, 29482]], ![![-1578, -3763, -2135, 1211, 3074]], ![![-9062, -21609, -12260, 6954, 17652]], ![![-14659, -34956, -19833, 11250, 28556]], ![![-9665, -23047, -13076, 7417, 18827]]]
  g := ![![![5, 9, 12, -3, -16], ![-8, -2, -11, 10, 8], ![19, 21, -26, -48, 64], ![5, -26, 27, 6, -38], ![4, 27, -36, -25, 61]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![15134, 36089, 20476, -11615, -29482]] ![![-34, 9, 12, -3, -16]]
  ![![59, 0, 0, 0, 0]] where
 M := ![![![-59, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-41, -12, 4, -12, -14]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![-41, -12, 4, -12, -14]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![32, 24, 52, 1, 0], ![6, 50, 51, 0, 1]] where
  M :=![![![-41, -12, 4, -12, -14], ![-52, -83, 8, -88, -68], ![-440, -432, 133, -624, -568], ![-194, -196, 72, -307, -286], ![-296, -288, 100, -440, -407]]]
  hmulB := by decide  
  f := ![![![3, 4, -4, 4, 2]], ![![-4, 1, -8, -24, 28]], ![![-88, -112, 153, 80, -248]], ![![-74, -92, 124, 61, -198]], ![![-78, -94, 123, 48, -187]]]
  g := ![![![7, 16, 22, -12, -14], ![52, 89, 132, -88, -68], ![376, 704, 1009, -624, -568], ![186, 352, 502, -307, -286], ![266, 502, 717, -440, -407]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [10, 37, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [20, 54, 14], [41, 6, 47], [0, 1]]
 g := ![![[59, 57, 14], [25, 15], [34, 12, 3], [27], [1]], ![[45, 18, 3, 25], [53, 5], [25, 11, 46, 57], [36, 15, 10, 34], [21, 8, 32, 60]], ![[53, 32, 35, 41], [55, 1], [11, 4, 53, 34], [34, 51, 35, 27], [42, 50, 51, 1]]]
 h' := ![![[20, 54, 14], [60, 58, 21], [26, 30, 36], [35, 16, 8], [51, 24], [0, 1]], ![[41, 6, 47], [28, 48, 23], [3, 28, 26], [20, 29, 28], [43, 15, 31], [20, 54, 14]], ![[0, 1], [2, 16, 17], [8, 3, 60], [7, 16, 25], [59, 22, 30], [41, 6, 47]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12, 14], []]
 b := ![[], [52, 16, 60], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [10, 37, 0, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7954850141, 8093331939, -3127689976, 10946002905, 11779804794]
  a := ![194, 219, -176, 93, 393]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6770427403, -13829524221, -19230981730, 10946002905, 11779804794]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 226981 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-201, -300, -54, -138, -38]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![-201, -300, -54, -138, -38]] 
 ![![61, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![52, 0, 1, 0, 0], ![32, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![-201, -300, -54, -138, -38], ![-952, -1061, 176, -1228, -1028], ![-5912, -6012, 1795, -8568, -7768], ![-2756, -2656, 1014, -4231, -3970], ![-4038, -3984, 1374, -6050, -5597]]]
  hmulB := by decide  
  f := ![![![-265, -524, 646, 394, -1078]], ![![41, 31, -38, 18, 34]], ![![-476, -660, 787, 192, -1104]], ![![-120, -280, 362, 293, -658]], ![![-139, -124, 128, -100, -83]]]
  g := ![![![133, -300, -54, -138, -38], ![615, -1061, 176, -1228, -1028], ![3800, -6012, 1795, -8568, -7768], ![1766, -2656, 1014, -4231, -3970], ![2591, -3984, 1374, -6050, -5597]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![615, -197, -181, 70, 274]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![615, -197, -181, 70, 274]] 
 ![![61, 0, 0, 0, 0], ![44, 1, 0, 0, 0], ![16, 0, 1, 0, 0], ![15, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  M :=![![![615, -197, -181, 70, 274], ![-258, 264, 71, 160, 12], ![1090, 749, -352, 1268, 1256], ![256, 460, -90, 595, 494], ![656, 561, -215, 878, 833]]]
  hmulB := by decide  
  f := ![![![58847, 140339, 79621, -45166, -114646]], ![![43558, 103878, 58935, -33432, -84860]], ![![16714, 39861, 22618, -12828, -32568]], ![![13649, 32549, 18465, -10475, -26588]], ![![6441, 15362, 8718, -4944, -12553]]]
  g := ![![![151, -197, -181, 70, 274], ![-254, 264, 71, 160, 12], ![-886, 749, -352, 1268, 1256], ![-507, 460, -90, 595, 494], ![-649, 561, -215, 878, 833]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![-41, -12, 4, -12, -14]] ![![-201, -300, -54, -138, -38]]
  ![![85621, 88632, -24122, 121594, 108820]] where
 M := ![![![85621, 88632, -24122, 121594, 108820]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![85621, 88632, -24122, 121594, 108820]] ![![615, -197, -181, 70, 274]]
  ![![61, 0, 0, 0, 0]] where
 M := ![![![106010863, 105445393, -35053345, 157480284, 144941002]]]
 hmul := by decide  
 g := ![![![![1737883, 1728613, -574645, 2581644, 2376082]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1, I61N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
    exact isPrimeI61N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0 ⊙ MulI61N1)


lemma PB1640I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB1640I1 : PrimesBelowBoundCertificateInterval O 23 61 1640 where
  m := 9
  g := ![1, 2, 2, 3, 3, 1, 2, 2, 3]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB1640I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0]
    · exact ![I31N0, I31N1]
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0, I43N1, I43N2]
    · exact ![I47N0]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1, I61N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC29
    · exact PBC31
    · exact PBC37
    · exact PBC41
    · exact PBC43
    · exact PBC47
    · exact PBC53
    · exact PBC59
    · exact PBC61
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![20511149]
    · exact ![923521, 31]
    · exact ![1874161, 37]
    · exact ![68921, 41, 41]
    · exact ![1849, 1849, 43]
    · exact ![229345007]
    · exact ![7890481, 53]
    · exact ![12117361, 59]
    · exact ![226981, 61, 61]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
      exact NI41N2
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
      exact NI43N2
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
      exact NI61N2
  β := ![I31N1, I37N1, I41N1, I41N2, I43N2, I53N1, I59N1, I61N1, I61N2]
  Il := ![[], [I31N1], [I37N1], [I41N1, I41N2], [I43N2], [], [I53N1], [I59N1], [I61N1, I61N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
