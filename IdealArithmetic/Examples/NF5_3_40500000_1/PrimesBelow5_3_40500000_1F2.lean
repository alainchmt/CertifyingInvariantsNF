
import IdealArithmetic.Examples.NF5_3_40500000_1.RI5_3_40500000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1794, -395, -585, -104, 1831]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![-1794, -395, -585, -104, 1831]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![0, 0, 67, 0, 0], ![38, 14, 51, 1, 0], ![25, 33, 47, 0, 1]] where
  M :=![![![-1794, -395, -585, -104, 1831], ![-7699, -1692, -2497, -442, 7825], ![-32937, -7233, -10712, -1900, 33559], ![-66748, -14649, -21677, -3841, 67944], ![-24743, -5431, -8043, -1426, 25204]]]
  hmulB := by decide  
  f := ![![![44, 15, -25, -8, 47]], ![![-123, -22, 41, 6, -55]], ![![191, -71, -2, 40, -97]], ![![145, -46, -11, 25, -49]], ![![91, -55, 9, 28, -77]]]
  g := ![![![-651, -886, -1214, -104, 1831], ![-2784, -3787, -5190, -442, 7825], ![-11936, -16240, -22255, -1900, 33559], ![-24170, -32881, -45062, -3841, 67944], ![-8965, -12197, -16715, -1426, 25204]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [32, 35, 41, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [61, 63, 27], [32, 3, 40], [0, 1]]
 g := ![![[63, 28, 19], [37], [44, 17], [55, 37], [26, 1], []], ![[5, 48, 19, 41], [33, 35, 43, 48], [27, 14], [30, 36], [45, 9], [45, 59]], ![[35, 55, 43, 10], [42, 65, 41, 19], [27, 40], [58, 60], [30, 16], [32, 59]]]
 h' := ![![[61, 63, 27], [22, 1, 35], [36, 29], [29, 63, 33], [39, 63, 38], [0, 0, 1], [0, 1]], ![[32, 3, 40], [54, 66, 65], [63, 18, 46], [18, 15, 58], [43, 25, 6], [3, 2, 3], [61, 63, 27]], ![[0, 1], [54, 0, 34], [26, 20, 21], [35, 56, 43], [45, 46, 23], [0, 65, 63], [32, 3, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 13], []]
 b := ![[], [43, 35, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [32, 35, 41, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![268755957, 58223898, 77137471, 13355116, -254976024]
  a := ![77, -62, 79, 36, -264]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![91577047, 123663598, 169849249, 13355116, -254976024]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 300763 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![12, 7, -5, -2, 9]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![12, 7, -5, -2, 9]] 
 ![![67, 0, 0, 0, 0], ![12, 1, 0, 0, 0], ![57, 0, 1, 0, 0], ![54, 0, 0, 1, 0], ![58, 0, 0, 0, 1]] where
  M :=![![![12, 7, -5, -2, 9], ![-17, -6, 19, 4, -33], ![109, 13, 0, 10, -39], ![36, 93, -39, -37, 120], ![45, 15, -3, 0, -4]]]
  hmulB := by decide  
  f := ![![![538, 77, -49, -34, 33]], ![![101, 16, -1, -4, -15]], ![![533, 80, -29, -28, -18]], ![![540, 87, 3, -19, -102]], ![![517, 77, -31, -28, -10]]]
  g := ![![![-3, 7, -5, -2, 9], ![10, -6, 19, 4, -33], ![25, 13, 0, 10, -39], ![-57, 93, -39, -37, 120], ![4, 15, -3, 0, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1

def I67N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![99, 8, -36, -14, 76]] i)))

def SI67N2: IdealEqSpanCertificate' Table ![![99, 8, -36, -14, 76]] 
 ![![67, 0, 0, 0, 0], ![20, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![37, 0, 0, 1, 0], ![29, 0, 0, 0, 1]] where
  M :=![![![99, 8, -36, -14, 76], ![-184, -15, 66, 26, -140], ![336, 28, -125, -50, 268], ![-228, -28, 88, 37, -192], ![152, 12, -56, -22, 119]]]
  hmulB := by decide  
  f := ![![![73, 0, 28, 6, -100]], ![![28, 1, 10, 2, -36]], ![![30, 4, 11, 2, -36]], ![![107, 12, 36, 7, -124]], ![![55, 4, 20, 4, -69]]]
  g := ![![![-25, 8, -36, -14, 76], ![46, -15, 66, 26, -140], ![-88, 28, -125, -50, 268], ![65, -28, 88, 37, -192], ![-39, 12, -56, -22, 119]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N2 : Nat.card (O ⧸ I67N2) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N2)

lemma isPrimeI67N2 : Ideal.IsPrime I67N2 := prime_ideal_of_norm_prime hp67.out _ NI67N2
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![-1794, -395, -585, -104, 1831]] ![![12, 7, -5, -2, 9]]
  ![![73, 0, 28, 6, -100]] where
 M := ![![![73, 0, 28, 6, -100]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![73, 0, 28, 6, -100]] ![![99, 8, -36, -14, 76]]
  ![![67, 0, 0, 0, 0]] where
 M := ![![![67, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1, I67N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
    exact isPrimeI67N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0 ⊙ MulI67N1)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2891, 634, 938, 166, -2942]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![2891, 634, 938, 166, -2942]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![69, 25, 1, 0, 0], ![25, 42, 0, 1, 0], ![3, 15, 0, 0, 1]] where
  M :=![![![2891, 634, 938, 166, -2942], ![12386, 2713, 4028, 714, -12626], ![53134, 11642, 17255, 3058, -54110], ![107676, 23602, 34982, 6195, -109680], ![39930, 8750, 12970, 2298, -40669]]]
  hmulB := by decide  
  f := ![![![33, -62, -174, -54, 394]], ![![-1214, -341, -40, 30, 166]], ![![-413, -191, -199, -46, 478]], ![![-761, -242, -96, -3, 266]], ![![-267, -81, -24, 2, 71]]]
  g := ![![![-805, 202, 938, 166, -2942], ![-3458, 865, 4028, 714, -12626], ![-14811, 3711, 17255, 3058, -54110], ![-30027, 7522, 34982, 6195, -109680], ![-11133, 2789, 12970, 2298, -40669]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [52, 49, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 70], [0, 1]]
 g := ![![[46, 20], [18, 10], [21, 60], [40], [58], [1]], ![[60, 51], [25, 61], [63, 11], [40], [58], [1]]]
 h' := ![![[22, 70], [58, 37], [44, 9], [53, 42], [43, 53], [19, 22], [0, 1]], ![[0, 1], [20, 34], [29, 62], [54, 29], [2, 18], [6, 49], [22, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36]]
 b := ![[], [15, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [52, 49, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6727019, -1319156, -2265292, -297338, 7352019]
  a := ![379, -328, 378, 160, -1299]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1900782, -598295, -2265292, -297338, 7352019]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![33, 9, 11, 2, -32]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![33, 9, 11, 2, -32]] 
 ![![71, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![50, 0, 0, 0, 1]] where
  M :=![![![33, 9, 11, 2, -32], ![132, 34, 43, 8, -128], ![528, 135, 170, 30, -512], ![1004, 241, 333, 61, -1008], ![378, 93, 123, 22, -373]]]
  hmulB := by decide  
  f := ![![![-1509, -133, 557, 220, -1184]], ![![40, 4, -15, -6, 32]], ![![-76, -9, 30, 12, -64]], ![![56, 9, -23, -9, 48]], ![![-1096, -97, 405, 160, -861]]]
  g := ![![![23, 9, 11, 2, -32], ![92, 34, 43, 8, -128], ![368, 135, 170, 30, -512], ![724, 241, 333, 61, -1008], ![268, 93, 123, 22, -373]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2, 0, 0, 0, 1]] i)))

def SI71N2: IdealEqSpanCertificate' Table ![![-2, 0, 0, 0, 1]] 
 ![![71, 0, 0, 0, 0], ![15, 1, 0, 0, 0], ![59, 0, 1, 0, 0], ![47, 0, 0, 1, 0], ![69, 0, 0, 0, 1]] where
  M :=![![![-2, 0, 0, 0, 1], ![-5, -1, -2, 0, 7], ![-35, 0, -15, -4, 49], ![-92, -22, -18, -1, 72], ![-31, -4, -10, -2, 34]]]
  hmulB := by decide  
  f := ![![![-128, -8, 54, 22, -119]], ![![-23, -1, 10, 4, -22]], ![![-113, -8, 49, 20, -108]], ![![-76, -2, 32, 13, -71]], ![![-127, -8, 54, 22, -119]]]
  g := ![![![-1, 0, 0, 0, 1], ![-5, -1, -2, 0, 7], ![-33, 0, -15, -4, 49], ![-51, -22, -18, -1, 72], ![-23, -4, -10, -2, 34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2

def I71N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-25, -6, -10, -2, 30]] i)))

def SI71N3: IdealEqSpanCertificate' Table ![![-25, -6, -10, -2, 30]] 
 ![![71, 0, 0, 0, 0], ![31, 1, 0, 0, 0], ![33, 0, 1, 0, 0], ![41, 0, 0, 1, 0], ![12, 0, 0, 0, 1]] where
  M :=![![![-25, -6, -10, -2, 30], ![-122, -27, -36, -6, 114], ![-486, -110, -165, -30, 510], ![-1004, -222, -322, -57, 1008], ![-366, -82, -122, -22, 379]]]
  hmulB := by decide  
  f := ![![![45, 50, -66, -30, 150]], ![![15, 19, -26, -12, 60]], ![![33, 28, -39, -16, 84]], ![![7, 28, -36, -19, 90]], ![![10, 10, -14, -6, 31]]]
  g := ![![![3, -6, -10, -2, 30], ![11, -27, -36, -6, 114], ![49, -110, -165, -30, 510], ![95, -222, -322, -57, 1008], ![36, -82, -122, -22, 379]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N3 : Nat.card (O ⧸ I71N3) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N3)

lemma isPrimeI71N3 : Ideal.IsPrime I71N3 := prime_ideal_of_norm_prime hp71.out _ NI71N3
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![2891, 634, 938, 166, -2942]] ![![33, 9, 11, 2, -32]]
  ![![-271057, -59395, -88065, -15604, 276118]] where
 M := ![![![-271057, -59395, -88065, -15604, 276118]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![-271057, -59395, -88065, -15604, 276118]] ![![-2, 0, 0, 0, 1]]
  ![![-3202726, -701789, -1040543, -184372, 3262517]] where
 M := ![![![-3202726, -701789, -1040543, -184372, 3262517]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI71N2 : IdealMulLeCertificate' Table 
  ![![-3202726, -701789, -1040543, -184372, 3262517]] ![![-25, -6, -10, -2, 30]]
  ![![71, 0, 0, 0, 0]] where
 M := ![![![-337581428, -73971421, -109678031, -19433694, 343884311]]]
 hmul := by decide  
 g := ![![![![-4754668, -1041851, -1544761, -273714, 4843441]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1, I71N2, I71N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
    exact isPrimeI71N2
    exact isPrimeI71N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0 ⊙ MulI71N1 ⊙ MulI71N2)
instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11, -6, 4, 2, -8]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![-11, -6, 4, 2, -8]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![20, 54, 1, 0, 0], ![44, 49, 0, 1, 0], ![68, 40, 0, 0, 1]] where
  M :=![![![-11, -6, 4, 2, -8], ![12, 7, -20, -6, 40], ![-116, -34, 17, 2, -8], ![0, -46, -14, 13, 0], ![-46, -18, 4, 2, -1]]]
  hmulB := by decide  
  f := ![![![-51, -10, 0, 2, 8]], ![![-68, -21, -56, -14, 152]], ![![-72, -20, -43, -10, 120]], ![![-88, -23, -42, -9, 120]], ![![-90, -22, -32, -6, 95]]]
  g := ![![![5, 0, 4, 2, -8], ![-28, -3, -20, -6, 40], ![0, -10, 17, 2, -8], ![-4, 1, -14, 13, 0], ![-2, -4, 4, 2, -1]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [41, 68, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 72], [0, 1]]
 g := ![![[7, 57], [6], [18], [12, 49], [25], [1]], ![[0, 16], [6], [18], [38, 24], [25], [1]]]
 h' := ![![[5, 72], [44, 35], [61, 15], [19, 23], [72, 7], [32, 5], [0, 1]], ![[0, 1], [0, 38], [63, 58], [61, 50], [34, 66], [57, 68], [5, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62]]
 b := ![[], [32, 31]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [41, 68, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-56606, -14502, -18344, -1388, 57452]
  a := ![40, -33, 41, 18, -137]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-48430, -17178, -18344, -1388, 57452]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![0, 5, -1, -2, 5]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![0, 5, -1, -2, 5]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![3, 24, 1, 0, 0], ![37, 6, 0, 1, 0], ![30, 52, 0, 0, 1]] where
  M :=![![![0, 5, -1, -2, 5], ![3, -18, 25, 12, -61], ![137, 99, -76, -34, 149], ![-136, -73, 143, 37, -264], ![39, 29, -11, -8, 22]]]
  hmulB := by decide  
  f := ![![![-162, -11, 69, 26, -149]], ![![381, 44, -103, -44, 205]], ![![113, 14, -27, -12, 52]], ![![-40, 0, 26, 9, -59]], ![![203, 27, -43, -20, 80]]]
  g := ![![![-1, -3, -1, -2, 5], ![18, 34, 25, 12, -61], ![-39, -77, -76, -34, 149], ![82, 137, 143, 37, -264], ![-4, -11, -11, -8, 22]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P1 : CertificateIrreducibleZModOfList' 73 2 2 6 [67, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [71, 72], [0, 1]]
 g := ![![[24, 12], [50], [6], [25, 2], [4], [1]], ![[0, 61], [50], [6], [21, 71], [4], [1]]]
 h' := ![![[71, 72], [11, 42], [52, 14], [4, 58], [60, 41], [6, 71], [0, 1]], ![[0, 1], [0, 31], [24, 59], [34, 15], [51, 32], [10, 2], [71, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52]]
 b := ![[], [26, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N1 : CertifiedPrimeIdeal' SI73N1 73 where
  n := 2
  hpos := by decide
  P := [67, 2, 1]
  hirr := P73P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2012136, -399856, -776131, -100673, 2399540]
  a := ![-240, 198, -243, -111, 823]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-930754, -1451298, -776131, -100673, 2399540]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N1 B_one_repr
lemma NI73N1 : Nat.card (O ⧸ I73N1) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N1

def I73N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![68, 7, -19, -8, 37]] i)))

def SI73N2: IdealEqSpanCertificate' Table ![![68, 7, -19, -8, 37]] 
 ![![73, 0, 0, 0, 0], ![68, 1, 0, 0, 0], ![48, 0, 1, 0, 0], ![13, 0, 0, 1, 0], ![48, 0, 0, 0, 1]] where
  M :=![![![68, 7, -19, -8, 37], ![-73, -2, 53, 18, -125], ![373, 53, -22, -20, -11], ![204, 61, 161, 39, -456], ![219, 35, 7, -6, -58]]]
  hmulB := by decide  
  f := ![![![-54, 71, -69, -48, 203]], ![![-55, 60, -59, -42, 177]], ![![-13, 65, -68, -40, 179]], ![![-62, -8, 12, -3, -1]], ![![-33, 51, -51, -34, 146]]]
  g := ![![![-16, 7, -19, -8, 37], ![45, -2, 53, 18, -125], ![-19, 53, -22, -20, -11], ![133, 61, 161, 39, -456], ![5, 35, 7, -6, -58]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N2 : Nat.card (O ⧸ I73N2) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N2)

lemma isPrimeI73N2 : Ideal.IsPrime I73N2 := prime_ideal_of_norm_prime hp73.out _ NI73N2
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![-11, -6, 4, 2, -8]] ![![0, 5, -1, -2, 5]]
  ![![-54, 71, -69, -48, 203]] where
 M := ![![![-54, 71, -69, -48, 203]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI73N1 : IdealMulLeCertificate' Table 
  ![![-54, 71, -69, -48, 203]] ![![68, 7, -19, -8, 37]]
  ![![73, 0, 0, 0, 0]] where
 M := ![![![73, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1, I73N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
    exact isPrimeI73N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0 ⊙ MulI73N1)
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1553, -330, -512, -94, 1604]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![-1553, -330, -512, -94, 1604]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![0, 0, 79, 0, 0], ![0, 0, 0, 79, 0], ![11, 6, 5, 29, 1]] where
  M :=![![![-1553, -330, -512, -94, 1604], ![-6704, -1495, -2128, -366, 6716], ![-28456, -6142, -9437, -1694, 29444], ![-58400, -12794, -18746, -3325, 59040], ![-21506, -4678, -7032, -1254, 22025]]]
  hmulB := by decide  
  f := ![![![-487, -42, 180, 70, -380]], ![![920, 83, -332, -130, 700]], ![![-1680, -142, 633, 246, -1340]], ![![1168, 118, -410, -163, 864]], ![![315, 34, -107, -43, 225]]]
  g := ![![![-243, -126, -108, -590, 1604], ![-1020, -529, -452, -2470, 6716], ![-4460, -2314, -1983, -10830, 29444], ![-8960, -4646, -3974, -21715, 59040], ![-3339, -1732, -1483, -8101, 22025]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 4 2 6 [51, 12, 52, 52, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 53, 48, 36], [9, 12, 59, 29], [2, 13, 51, 14], [0, 1]]
 g := ![![[57, 60, 16, 51], [12, 40, 5, 51], [4, 47, 22, 18], [26, 46, 48, 18], [1], []], ![[47, 13, 46, 34, 18, 65], [6, 54, 44, 38, 14, 51], [18, 54, 7, 15, 14, 31], [39, 56, 10, 58, 21, 8], [12, 28, 38], [68, 54, 32]], ![[68, 59, 11, 15, 29, 39], [12, 25, 74, 35, 34, 66], [43, 9, 41, 66, 16, 41], [5, 31, 25, 21, 17, 43], [77, 28, 76], [37, 59, 51]], ![[67, 78, 73, 35, 76, 59], [33, 1, 69, 48, 76, 24], [52, 55, 33, 75, 33, 47], [54, 2, 47, 9, 74, 54], [42, 60, 62], [18, 5, 38]]]
 h' := ![![[16, 53, 48, 36], [20, 11, 46, 29], [33, 56, 39, 29], [17, 22, 32, 52], [28, 67, 27, 27], [0, 0, 1], [0, 1]], ![[9, 12, 59, 29], [41, 69, 8, 2], [32, 9, 62, 61], [22, 0, 42, 5], [38, 11, 75, 3], [27, 22, 30, 65], [16, 53, 48, 36]], ![[2, 13, 51, 14], [17, 42, 73, 71], [42, 15, 28, 20], [8, 18, 28, 19], [65, 62, 48, 42], [11, 2, 2, 47], [9, 12, 59, 29]], ![[0, 1], [57, 36, 31, 56], [1, 78, 29, 48], [55, 39, 56, 3], [41, 18, 8, 7], [34, 55, 46, 46], [2, 13, 51, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [22, 62, 57], []]
 b := ![[], [], [51, 31, 43, 28], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 4
  hpos := by decide
  P := [51, 12, 52, 52, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1261287797569, -236169262874, -470406353633, -96224718326, 1433223631776]
  a := ![135, -105, 140, 70, -463]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-215528452495, -111841912070, -96664867247, -527338101770, 1433223631776]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 38950081 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![487, 42, -180, -70, 380]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![487, 42, -180, -70, 380]] 
 ![![79, 0, 0, 0, 0], ![23, 1, 0, 0, 0], ![24, 0, 1, 0, 0], ![68, 0, 0, 1, 0], ![27, 0, 0, 0, 1]] where
  M :=![![![487, 42, -180, -70, 380], ![-920, -83, 332, 130, -700], ![1680, 142, -633, -246, 1340], ![-1168, -118, 410, 163, -864], ![750, 62, -284, -110, 601]]]
  hmulB := by decide  
  f := ![![![1553, 330, 512, 94, -1604]], ![![537, 115, 176, 32, -552]], ![![832, 178, 275, 50, -860]], ![![2076, 446, 678, 123, -2128]], ![![803, 172, 264, 48, -827]]]
  g := ![![![-21, 42, -180, -70, 380], ![39, -83, 332, 130, -700], ![-74, 142, -633, -246, 1340], ![50, -118, 410, 163, -864], ![-33, 62, -284, -110, 601]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![-1553, -330, -512, -94, 1604]] ![![487, 42, -180, -70, 380]]
  ![![79, 0, 0, 0, 0]] where
 M := ![![![-79, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0)
instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0, 0, 0]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0, 0, 0]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![0, 0, 83, 0, 0], ![0, 0, 0, 83, 0], ![0, 0, 0, 0, 83]] where
  M :=![![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![0, 0, 83, 0, 0], ![0, 0, 0, 83, 0], ![0, 0, 0, 0, 83]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 5 2 6 [9, 25, 50, 49, 48, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 27, 75, 10, 22], [65, 66, 2, 26, 76], [79, 12, 6, 69, 33], [57, 60, 0, 61, 35], [0, 1]]
 g := ![![[0, 74, 26, 52, 33], [44, 39, 62, 53, 63], [44, 81, 24, 29], [16, 0, 20, 63], [1], []], ![[2, 16, 57, 61, 77, 15, 27, 6], [19, 10, 69, 43, 42, 71, 43, 55], [41, 60, 74, 49], [49, 63, 68, 81], [61, 51, 78, 80, 16, 28, 8, 72], [33, 12, 33, 69]], ![[50, 42, 69, 0, 67, 12, 6, 67], [59, 74, 27, 26, 8, 31, 2, 74], [75, 16, 9, 49], [36, 27, 65, 12], [10, 62, 66, 58, 82, 1, 9, 22], [22, 48, 23, 49]], ![[22, 4, 71, 20, 18, 56, 37, 9], [10, 48, 76, 53, 69, 36, 82, 78], [29, 29, 79, 37], [61, 67, 78, 75], [4, 48, 10, 19, 43, 38, 81, 16], [57, 15, 7, 10]], ![[43, 15, 8, 2, 65, 65, 15, 24], [57, 67, 25, 51, 77, 2, 5, 56], [78, 25, 17, 10], [19, 13, 54, 3], [26, 42, 43, 55, 9, 14, 20, 43], [14, 5, 1, 63]]]
 h' := ![![[0, 27, 75, 10, 22], [19, 59, 42, 44, 45], [4, 5, 22, 26, 48], [20, 50, 47, 37, 64], [74, 58, 33, 34, 35], [0, 0, 1], [0, 1]], ![[65, 66, 2, 26, 76], [78, 37, 32, 58, 11], [50, 76, 9, 8, 25], [2, 16, 17, 31, 7], [32, 49, 78, 20, 74], [35, 63, 59, 55, 37], [0, 27, 75, 10, 22]], ![[79, 12, 6, 69, 33], [7, 61, 27, 16, 62], [16, 16, 5, 32, 78], [44, 75, 21, 56, 7], [77, 23, 64, 65, 26], [43, 45, 34, 63, 63], [65, 66, 2, 26, 76]], ![[57, 60, 0, 61, 35], [66, 0, 38, 63, 11], [25, 15, 82, 13, 78], [55, 34, 21, 81, 55], [43, 29, 14, 33, 18], [1, 4, 45, 17, 13], [79, 12, 6, 69, 33]], ![[0, 1], [38, 9, 27, 68, 37], [27, 54, 48, 4, 20], [56, 74, 60, 44, 33], [12, 7, 60, 14, 13], [52, 54, 27, 31, 53], [57, 60, 0, 61, 35]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37, 30, 31, 45], [], [], []]
 b := ![[], [53, 62, 27, 79, 47], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 5
  hpos := by decide
  P := [9, 25, 50, 49, 48, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![73495332055125, 35851097914424, -45224649926726, -12671109359438, 77975845219104]
  a := ![-84, 56, -86, -62, 288]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![885485928375, 431940938728, -544875300322, -152663968186, 939468014688]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 3939040643 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def PBC83 : ContainsPrimesAboveP 83 ![I83N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![83, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 83 (by decide) 𝕀

instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-31, -8, 4, 2, -6]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![-31, -8, 4, 2, -6]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![82, 65, 1, 0, 0], ![5, 65, 0, 1, 0], ![17, 7, 0, 0, 1]] where
  M :=![![![-31, -8, 4, 2, -6], ![2, -11, -26, -6, 54], ![-186, -36, -29, -10, 90], ![-156, -112, -20, 9, 48], ![-98, -28, -12, -2, 37]]]
  hmulB := by decide  
  f := ![![![149, 32, 52, 10, -162]], ![![670, 149, 206, 34, -654]], ![![658, 145, 209, 36, -660]], ![![563, 125, 174, 29, -552]], ![![105, 23, 34, 6, -107]]]
  g := ![![![-3, -4, 4, 2, -6], ![14, 19, -26, -6, 54], ![8, 21, -29, -10, 90], ![7, 3, -20, 9, 48], ![3, 7, -12, -2, 37]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [79, 51, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 88], [0, 1]]
 g := ![![[75, 80], [32], [9], [49, 45], [7, 20], [1]], ![[0, 9], [32], [9], [68, 44], [55, 69], [1]]]
 h' := ![![[38, 88], [49, 76], [68, 78], [45, 3], [70, 32], [10, 38], [0, 1]], ![[0, 1], [0, 13], [6, 11], [70, 86], [40, 57], [30, 51], [38, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [83]]
 b := ![[], [57, 86]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [79, 51, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-167070, -2504, -89738, -19706, 275161]
  a := ![-12, 22, -8, 15, 43]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![29351, 58261, -89738, -19706, 275161]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-28, -3, 9, 0, -9]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![-28, -3, 9, 0, -9]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![41, 56, 1, 0, 0], ![9, 55, 0, 1, 0], ![54, 86, 0, 0, 1]] where
  M :=![![![-28, -3, 9, 0, -9], ![45, -28, 15, 18, -63], ![63, 195, -172, -96, 423], ![-408, -357, 387, 155, -792], ![-21, 33, -21, -18, 68]]]
  hmulB := by decide  
  f := ![![![-62, -3, -9, 0, 45]], ![![-225, -26, -93, -18, 315]], ![![-185, -20, -67, -12, 234]], ![![-177, -22, -69, -13, 234]], ![![-267, -29, -99, -18, 344]]]
  g := ![![![1, 3, 9, 0, -9], ![30, 40, 15, 18, -63], ![-167, -239, -172, -96, 423], ![282, 422, 387, 155, -792], ![-30, -41, -21, -18, 68]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P1 : CertificateIrreducibleZModOfList' 89 2 2 6 [58, 65, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 88], [0, 1]]
 g := ![![[18, 36], [2], [18], [41, 67], [4, 42], [1]], ![[81, 53], [2], [18], [47, 22], [33, 47], [1]]]
 h' := ![![[24, 88], [26, 83], [26, 64], [25, 14], [35, 45], [31, 24], [0, 1]], ![[0, 1], [60, 6], [49, 25], [5, 75], [47, 44], [73, 65], [24, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [87, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N1 : CertifiedPrimeIdeal' SI89N1 89 where
  n := 2
  hpos := by decide
  P := [58, 65, 1]
  hirr := P89P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6403, 3978, -5242, -1974, 10623]
  a := ![-12, 6, -13, -11, 41]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3759, -5702, -5242, -1974, 10623]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N1 B_one_repr
lemma NI89N1 : Nat.card (O ⧸ I89N1) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N1

def I89N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-664, -145, -215, -38, 675]] i)))

def SI89N2: IdealEqSpanCertificate' Table ![![-664, -145, -215, -38, 675]] 
 ![![89, 0, 0, 0, 0], ![57, 1, 0, 0, 0], ![44, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![31, 0, 0, 0, 1]] where
  M :=![![![-664, -145, -215, -38, 675], ![-2843, -622, -925, -164, 2901], ![-12209, -2671, -3964, -702, 12435], ![-24752, -5419, -8043, -1425, 25224], ![-9179, -2009, -2981, -528, 9350]]]
  hmulB := by decide  
  f := ![![![-70, -185, 187, 110, -483]], ![![-35, -109, 110, 66, -288]], ![![-79, -119, 126, 66, -303]], ![![68, 5, -15, 5, 0]], ![![-33, -72, 74, 42, -187]]]
  g := ![![![-40, -145, -215, -38, 675], ![-172, -622, -925, -164, 2901], ![-735, -2671, -3964, -702, 12435], ![-1489, -5419, -8043, -1425, 25224], ![-552, -2009, -2981, -528, 9350]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N2 : Nat.card (O ⧸ I89N2) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N2)

lemma isPrimeI89N2 : Ideal.IsPrime I89N2 := prime_ideal_of_norm_prime hp89.out _ NI89N2
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![-31, -8, 4, 2, -6]] ![![-28, -3, 9, 0, -9]]
  ![![70, 185, -187, -110, 483]] where
 M := ![![![70, 185, -187, -110, 483]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI89N1 : IdealMulLeCertificate' Table 
  ![![70, 185, -187, -110, 483]] ![![-664, -145, -215, -38, 675]]
  ![![89, 0, 0, 0, 0]] where
 M := ![![![-89, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N1, I89N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N1
    exact isPrimeI89N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0 ⊙ MulI89N1)
instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3100, 680, 1006, 178, -3155]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![3100, 680, 1006, 178, -3155]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![74, 70, 1, 0, 0], ![29, 61, 0, 1, 0], ![28, 74, 0, 0, 1]] where
  M :=![![![3100, 680, 1006, 178, -3155], ![13283, 2909, 4320, 766, -13541], ![56981, 12488, 18501, 3278, -58019], ![115460, 25306, 37518, 6645, -117624], ![42819, 9384, 13908, 2464, -43610]]]
  hmulB := by decide  
  f := ![![![798, 112, -216, -92, 443]], ![![-927, 13, 606, 212, -1315]], ![![-23, 102, 267, 80, -601]], ![![-345, 47, 328, 109, -720]], ![![-459, 46, 398, 134, -872]]]
  g := ![![![122, 1576, 1006, 178, -3155], ![521, 6761, 4320, 766, -13541], ![2241, 28978, 18501, 3278, -58019], ![4535, 58741, 37518, 6645, -117624], ![1683, 21780, 13908, 2464, -43610]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [73, 36, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [61, 96], [0, 1]]
 g := ![![[47, 4], [72], [22], [9], [86], [61, 1]], ![[0, 93], [72], [22], [9], [86], [25, 96]]]
 h' := ![![[61, 96], [25, 95], [25, 13], [46, 33], [11, 3], [9, 59], [0, 1]], ![[0, 1], [0, 2], [42, 84], [22, 64], [0, 94], [19, 38], [61, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [56, 57]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [73, 36, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-296777, -40696, -202598, -33016, 550986]
  a := ![-125, 97, -125, -66, 429]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2323, -253792, -202598, -33016, 550986]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 14, 6, 0, -14]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![23, 14, 6, 0, -14]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![17, 57, 1, 0, 0], ![49, 82, 0, 1, 0], ![68, 65, 0, 0, 1]] where
  M :=![![![23, 14, 6, 0, -14], ![70, 15, 42, 12, -98], ![322, 146, 31, 0, -110], ![240, 114, 162, 25, -336], ![154, 70, 34, 4, -89]]]
  hmulB := by decide  
  f := ![![![211, 50, 82, 16, -250]], ![![1026, 219, 310, 52, -982]], ![![683, 147, 211, 36, -666]], ![![1063, 230, 332, 57, -1046]], ![![868, 189, 276, 48, -867]]]
  g := ![![![9, 6, 6, 0, -14], ![56, 31, 42, 12, -98], ![75, 57, 31, 0, -110], ![197, 110, 162, 25, -336], ![56, 37, 34, 4, -89]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P1 : CertificateIrreducibleZModOfList' 97 2 2 6 [85, 91, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 96], [0, 1]]
 g := ![![[49, 8], [65], [49], [96], [73], [6, 1]], ![[0, 89], [65], [49], [96], [73], [12, 96]]]
 h' := ![![[6, 96], [26, 28], [33, 68], [67, 7], [46, 75], [72, 48], [0, 1]], ![[0, 1], [0, 69], [53, 29], [12, 90], [11, 22], [69, 49], [6, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60]]
 b := ![[], [7, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N1 : CertifiedPrimeIdeal' SI97N1 97 where
  n := 2
  hpos := by decide
  P := [85, 91, 1]
  hirr := P97P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-186588, -31188, -91512, -14144, 268695]
  a := ![-86, 68, -89, -43, 295]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-167104, -114643, -91512, -14144, 268695]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N1 B_one_repr
lemma NI97N1 : Nat.card (O ⧸ I97N1) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N1

def I97N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![164, 14, -62, -24, 131]] i)))

def SI97N2: IdealEqSpanCertificate' Table ![![164, 14, -62, -24, 131]] 
 ![![97, 0, 0, 0, 0], ![67, 1, 0, 0, 0], ![70, 0, 1, 0, 0], ![95, 0, 0, 1, 0], ![35, 0, 0, 0, 1]] where
  M :=![![![164, 14, -62, -24, 131], ![-319, -31, 112, 44, -235], ![559, 42, -221, -84, 467], ![-420, -44, 128, 51, -264], ![247, 18, -100, -38, 212]]]
  hmulB := by decide  
  f := ![![![318, 82, 88, 10, -287]], ![![233, 59, 66, 8, -214]], ![![293, 74, 81, 10, -265]], ![![430, 106, 128, 17, -409]], ![![161, 40, 46, 6, -149]]]
  g := ![![![13, 14, -62, -24, 131], ![-21, -31, 112, 44, -235], ![50, 42, -221, -84, 467], ![-21, -44, 128, 51, -264], ![23, 18, -100, -38, 212]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N2 : Nat.card (O ⧸ I97N2) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N2)

lemma isPrimeI97N2 : Ideal.IsPrime I97N2 := prime_ideal_of_norm_prime hp97.out _ NI97N2
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![3100, 680, 1006, 178, -3155]] ![![23, 14, 6, 0, -14]]
  ![![-318, -82, -88, -10, 287]] where
 M := ![![![-318, -82, -88, -10, 287]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI97N1 : IdealMulLeCertificate' Table 
  ![![-318, -82, -88, -10, 287]] ![![164, 14, -62, -24, 131]]
  ![![97, 0, 0, 0, 0]] where
 M := ![![![-97, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC97 : ContainsPrimesAboveP 97 ![I97N0, I97N1, I97N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
    exact isPrimeI97N1
    exact isPrimeI97N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 97 (by decide) (𝕀 ⊙ MulI97N0 ⊙ MulI97N1)
instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-22, -4, 4, 2, -7]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![-22, -4, 4, 2, -7]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![73, 70, 1, 0, 0], ![71, 11, 0, 1, 0], ![94, 87, 0, 0, 1]] where
  M :=![![![-22, -4, 4, 2, -7], ![7, -3, -20, -6, 47], ![-151, -32, -7, 2, 41], ![-120, -46, -62, -11, 168], ![-87, -20, -10, 0, 38]]]
  hmulB := by decide  
  f := ![![![-20, -12, 6, 4, -13]], ![![9, 17, -46, -16, 101]], ![![-11, 2, -27, -8, 60]], ![![-13, -7, -2, 1, 4]], ![![-12, 3, -34, -10, 75]]]
  g := ![![![2, 3, 4, 2, -7], ![-25, -26, -20, -6, 47], ![-36, -31, -7, 2, 41], ![-105, -101, -62, -11, 168], ![-29, -26, -10, 0, 38]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [23, 76, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [25, 100], [0, 1]]
 g := ![![[56, 22], [95], [2, 14], [76], [16], [25, 1]], ![[0, 79], [95], [49, 87], [76], [16], [50, 100]]]
 h' := ![![[25, 100], [32, 27], [55, 87], [37, 69], [88, 51], [31, 97], [0, 1]], ![[0, 1], [0, 74], [8, 14], [45, 32], [50, 50], [32, 4], [25, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [72]]
 b := ![[], [55, 36]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [23, 76, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-69531, -8110, -23880, -4395, 81104]
  a := ![-22, 22, -22, -3, 76]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-55822, -52913, -23880, -4395, 81104]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, 0, -2, 0, 2]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![9, 0, -2, 0, 2]] 
 ![![101, 0, 0, 0, 0], ![71, 1, 0, 0, 0], ![9, 0, 1, 0, 0], ![49, 0, 0, 1, 0], ![64, 0, 0, 0, 1]] where
  M :=![![![9, 0, -2, 0, 2], ![-10, 9, -4, -4, 14], ![-14, -44, 41, 20, -94], ![100, 72, -76, -27, 144], ![8, -8, 6, 4, -17]]]
  hmulB := by decide  
  f := ![![![321, 88, 94, 16, -274]], ![![237, 65, 70, 12, -204]], ![![75, 20, 23, 4, -68]], ![![241, 64, 74, 13, -218]], ![![236, 64, 70, 12, -205]]]
  g := ![![![-1, 0, -2, 0, 2], ![-13, 9, -4, -4, 14], ![77, -44, 41, 20, -94], ![-121, 72, -76, -27, 144], ![14, -8, 6, 4, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 4, -8, -2, 14]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![11, 4, -8, -2, 14]] 
 ![![101, 0, 0, 0, 0], ![76, 1, 0, 0, 0], ![82, 0, 1, 0, 0], ![78, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![11, 4, -8, -2, 14], ![-42, -5, 6, -2, 2], ![18, -56, 21, 26, -82], ![44, 124, -144, -69, 336], ![10, -8, -8, 2, 7]]]
  hmulB := by decide  
  f := ![![![2899, 628, 912, 158, -2878]], ![![2302, 499, 726, 126, -2290]], ![![2876, 624, 909, 158, -2866]], ![![3294, 716, 1048, 183, -3300]], ![![421, 92, 136, 24, -427]]]
  g := ![![![5, 4, -8, -2, 14], ![0, -5, 6, -2, 2], ![6, -56, 21, 26, -82], ![74, 124, -144, -69, 336], ![11, -8, -8, 2, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2

def I101N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1774, 388, 576, 102, -1807]] i)))

def SI101N3: IdealEqSpanCertificate' Table ![![1774, 388, 576, 102, -1807]] 
 ![![101, 0, 0, 0, 0], ![86, 1, 0, 0, 0], ![78, 0, 1, 0, 0], ![37, 0, 0, 1, 0], ![55, 0, 0, 0, 1]] where
  M :=![![![1774, 388, 576, 102, -1807], ![7607, 1665, 2472, 438, -7753], ![32633, 7144, 10601, 1878, -33247], ![66168, 14490, 21498, 3809, -67416], ![24533, 5372, 7970, 1412, -24994]]]
  hmulB := by decide  
  f := ![![![-200, -388, 346, 160, -757]], ![![-155, -319, 282, 132, -621]], ![![-213, -320, 295, 128, -623]], ![![-16, -158, 128, 73, -317]], ![![-123, -220, 198, 90, -429]]]
  g := ![![![189, 388, 576, 102, -1807], ![810, 1665, 2472, 438, -7753], ![3470, 7144, 10601, 1878, -33247], ![7031, 14490, 21498, 3809, -67416], ![2607, 5372, 7970, 1412, -24994]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N3 : Nat.card (O ⧸ I101N3) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N3)

lemma isPrimeI101N3 : Ideal.IsPrime I101N3 := prime_ideal_of_norm_prime hp101.out _ NI101N3
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![-22, -4, 4, 2, -7]] ![![9, 0, -2, 0, 2]]
  ![![-70, -12, 30, 14, -69]] where
 M := ![![![-70, -12, 30, 14, -69]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![-70, -12, 30, 14, -69]] ![![11, 4, -8, -2, 14]]
  ![![200, 388, -346, -160, 757]] where
 M := ![![![200, 388, -346, -160, 757]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI101N2 : IdealMulLeCertificate' Table 
  ![![200, 388, -346, -160, 757]] ![![1774, 388, 576, 102, -1807]]
  ![![101, 0, 0, 0, 0]] where
 M := ![![![-101, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC101 : ContainsPrimesAboveP 101 ![I101N0, I101N1, I101N2, I101N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
    exact isPrimeI101N1
    exact isPrimeI101N2
    exact isPrimeI101N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 101 (by decide) (𝕀 ⊙ MulI101N0 ⊙ MulI101N1 ⊙ MulI101N2)
instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![627, 133, 183, 30, -586]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![627, 133, 183, 30, -586]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![70, 44, 35, 1, 0], ![28, 82, 92, 0, 1]] where
  M :=![![![627, 133, 183, 30, -586], ![2510, 554, 855, 156, -2662], ![11126, 2419, 3538, 618, -11146], ![22284, 4881, 7293, 1297, -22848], ![8336, 1817, 2675, 470, -8411]]]
  hmulB := by decide  
  f := ![![![21, 15, -23, -8, 46]], ![![-118, -44, 43, 10, -62]], ![![170, -27, -70, 16, 46]], ![![20, -16, -23, 3, 26]], ![![64, -55, -35, 20, 5]]]
  g := ![![![145, 455, 515, 30, -586], ![642, 2058, 2333, 156, -2662], ![2718, 8633, 9780, 618, -11146], ![5546, 17683, 20038, 1297, -22848], ![2048, 6513, 7379, 470, -8411]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [7, 58, 86, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [75, 88, 61], [45, 14, 42], [0, 1]]
 g := ![![[4, 101, 92], [28, 78, 8], [28, 32, 38], [25, 4], [57, 83], [1]], ![[66, 49, 68, 97], [7, 14, 71, 64], [58, 62, 74, 15], [24, 50], [84, 16], [27, 8, 21, 72]], ![[12, 47, 74, 65], [10, 48, 41, 31], [76, 48, 20, 73], [46, 15], [19, 66], [28, 46, 43, 31]]]
 h' := ![![[75, 88, 61], [10, 93, 68], [10, 85, 76], [64, 73, 48], [62, 15, 2], [96, 45, 17], [0, 1]], ![[45, 14, 42], [18, 60, 33], [4, 24, 69], [94, 29, 78], [46, 45, 16], [4, 75, 99], [75, 88, 61]], ![[0, 1], [60, 53, 2], [86, 97, 61], [0, 1, 80], [61, 43, 85], [83, 86, 90], [45, 14, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [69, 78], []]
 b := ![[], [54, 58, 46], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [7, 58, 86, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5115943860, 1511601065, 747412944, -3119282, -3145653967]
  a := ![245, -185, 244, 134, -839]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![906918492, 2520315289, 2818026726, -3119282, -3145653967]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 1092727 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![21, 15, -23, -8, 46]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![21, 15, -23, -8, 46]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![55, 33, 1, 0, 0], ![71, 50, 0, 1, 0], ![0, 30, 0, 0, 1]] where
  M :=![![![21, 15, -23, -8, 46], ![-118, -44, 43, 10, -62], ![170, -27, -70, 16, 46], ![-168, 183, -201, -131, 576], ![40, 7, -47, -8, 79]]]
  hmulB := by decide  
  f := ![![![627, 133, 183, 30, -586]], ![![2510, 554, 855, 156, -2662]], ![![1247, 272, 406, 72, -1274]], ![![1867, 408, 612, 109, -1918]], ![![812, 179, 275, 50, -857]]]
  g := ![![![18, -2, -23, -8, 46], ![-31, -1, 43, 10, -62], ![28, 1, -70, 16, 46], ![196, -38, -201, -131, 576], ![31, -4, -47, -8, 79]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P1 : CertificateIrreducibleZModOfList' 103 2 2 6 [47, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [74, 102], [0, 1]]
 g := ![![[5, 63], [4, 14], [101, 82], [79], [76], [74, 1]], ![[32, 40], [10, 89], [92, 21], [79], [76], [45, 102]]]
 h' := ![![[74, 102], [18, 28], [94, 23], [76, 59], [94, 64], [24, 73], [0, 1]], ![[0, 1], [30, 75], [45, 80], [13, 44], [92, 39], [70, 30], [74, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [97]]
 b := ![[], [8, 100]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N1 : CertifiedPrimeIdeal' SI103N1 103 where
  n := 2
  hpos := by decide
  P := [47, 29, 1]
  hirr := P103P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-142586, -27765, -79421, -10538, 220439]
  a := ![82, -63, 83, 42, -281]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![48289, -33914, -79421, -10538, 220439]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N1 B_one_repr
lemma NI103N1 : Nat.card (O ⧸ I103N1) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![627, 133, 183, 30, -586]] ![![21, 15, -23, -8, 46]]
  ![![103, 0, 0, 0, 0]] where
 M := ![![![103, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC103 : ContainsPrimesAboveP 103 ![I103N0, I103N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
    exact isPrimeI103N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 103 (by decide) (𝕀 ⊙ MulI103N0)


lemma PB312I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 103 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 103 (by omega)

def PB312I2 : PrimesBelowBoundCertificateInterval O 61 103 312 where
  m := 9
  g := ![3, 4, 3, 2, 1, 3, 3, 4, 2]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103]
  hP := PB312I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0, I67N1, I67N2]
    · exact ![I71N0, I71N1, I71N2, I71N3]
    · exact ![I73N0, I73N1, I73N2]
    · exact ![I79N0, I79N1]
    · exact ![I83N0]
    · exact ![I89N0, I89N1, I89N2]
    · exact ![I97N0, I97N1, I97N2]
    · exact ![I101N0, I101N1, I101N2, I101N3]
    · exact ![I103N0, I103N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC67
    · exact PBC71
    · exact PBC73
    · exact PBC79
    · exact PBC83
    · exact PBC89
    · exact PBC97
    · exact PBC101
    · exact PBC103
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![300763, 67, 67]
    · exact ![5041, 71, 71, 71]
    · exact ![5329, 5329, 73]
    · exact ![38950081, 79]
    · exact ![3939040643]
    · exact ![7921, 7921, 89]
    · exact ![9409, 9409, 97]
    · exact ![10201, 101, 101, 101]
    · exact ![1092727, 10609]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
      exact NI67N2
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
      exact NI71N2
      exact NI71N3
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
      exact NI73N2
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
      exact NI89N2
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
      exact NI97N2
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
      exact NI101N2
      exact NI101N3
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
  β := ![I67N1, I67N2, I71N1, I71N2, I71N3, I73N2, I79N1, I89N2, I97N2, I101N1, I101N2, I101N3]
  Il := ![[I67N1, I67N2], [I71N1, I71N2, I71N3], [I73N2], [I79N1], [], [I89N2], [I97N2], [I101N1, I101N2, I101N3], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
