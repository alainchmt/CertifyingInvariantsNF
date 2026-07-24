
import IdealArithmetic.Examples.NF5_1_9000000_1.RI5_1_9000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0, 0, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0, 0, 0]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![0, 0, 67, 0, 0], ![0, 0, 0, 67, 0], ![0, 0, 0, 0, 67]] where
  M :=![![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![0, 0, 67, 0, 0], ![0, 0, 0, 67, 0], ![0, 0, 0, 0, 67]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 5 2 6 [26, 56, 53, 62, 20, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [66, 2, 14, 39, 4], [17, 29, 4, 6, 21], [52, 5, 40, 23, 36], [46, 30, 9, 66, 6], [0, 1]]
 g := ![![[49, 37, 6, 42, 40], [45, 17, 26, 16, 40], [50, 37, 55, 62], [55, 3, 47, 1], [], []], ![[50, 61, 58, 50, 60, 52, 15, 29], [5, 48, 41, 32, 59, 37, 59, 40], [3, 6, 2, 59], [53, 65, 10, 55], [61, 12, 8, 26], [12, 64, 59, 16]], ![[12, 61, 11, 60, 34, 56, 14, 21], [62, 13, 22, 25, 48, 27, 11, 10], [19, 31, 48, 36], [14, 42, 14, 10], [21, 11, 19, 4], [20, 38, 8, 39]], ![[36, 12, 55, 57, 35, 18, 14, 49], [40, 53, 61, 21, 35, 23, 66, 14], [20, 62, 6, 4], [5, 53, 30, 59], [0, 8, 26, 26], [17, 39, 57, 23]], ![[31, 66, 17, 10, 11, 54], [10, 37, 12, 59, 26, 55, 53, 1], [26, 37, 28, 25], [38, 58, 60, 4], [24, 35, 3, 4], [39, 55, 5, 36]]]
 h' := ![![[66, 2, 14, 39, 4], [36, 3, 5, 65, 24], [33, 2, 4, 17, 24], [44, 58, 50, 4, 53], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[17, 29, 4, 6, 21], [31, 43, 31, 57, 52], [24, 15, 21, 0, 12], [54, 5, 59, 7, 27], [62, 63, 35, 64, 16], [24, 5, 51, 28, 19], [66, 2, 14, 39, 4]], ![[52, 5, 40, 23, 36], [60, 37, 14, 7, 1], [51, 20, 26, 65, 48], [64, 20, 56, 3, 61], [19, 64, 27, 48, 12], [37, 17, 60, 8, 2], [17, 29, 4, 6, 21]], ![[46, 30, 9, 66, 6], [26, 30, 46, 2, 57], [11, 19, 36, 30, 32], [14, 48, 29, 12, 65], [55, 35, 25, 57, 40], [51, 28, 20, 35, 48], [52, 5, 40, 23, 36]], ![[0, 1], [13, 21, 38, 3], [56, 11, 47, 22, 18], [14, 3, 7, 41, 62], [8, 39, 47, 32, 65], [30, 17, 2, 63, 65], [46, 30, 9, 66, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36, 49, 44, 4], [], [], []]
 b := ![[], [64, 4, 63, 29, 66], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 5
  hpos := by decide
  P := [26, 56, 53, 62, 20, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-321837850, 148856312, 83497544, 73704958, -91412522]
  a := ![0, -7, 2, -8, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4803550, 2221736, 1246232, 1100074, -1364366]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 1350125107 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def PBC67 : ContainsPrimesAboveP 67 ![I67N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![67, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 67 (by decide) 𝕀

instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, -13, 3, -4, -3]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![11, -13, 3, -4, -3]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![28, 45, 1, 0, 0], ![18, 13, 0, 1, 0], ![24, 32, 0, 0, 1]] where
  M :=![![![11, -13, 3, -4, -3], ![-12, 15, -18, 4, -18], ![-36, 16, 11, 4, 30], ![66, -61, 21, -17, -9], ![-36, 34, -12, 10, 5]]]
  hmulB := by decide  
  f := ![![![13, -13, -9, -10, -3]], ![![-12, -7, -6, -32, -54]], ![![-4, -9, -7, -24, -36]], ![![0, -4, -3, -7, -9]], ![![0, -8, -6, -18, -25]]]
  g := ![![![1, 0, 3, -4, -3], ![12, 19, -18, 4, -18], ![-16, -21, 11, 4, 30], ![0, -7, 21, -17, -9], ![0, 4, -12, 10, 5]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [32, 28, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [43, 70], [0, 1]]
 g := ![![[63, 20], [12, 49], [21, 40], [16], [3], [1]], ![[0, 51], [60, 22], [37, 31], [16], [3], [1]]]
 h' := ![![[43, 70], [42, 37], [38, 7], [10, 18], [5, 4], [39, 43], [0, 1]], ![[0, 1], [0, 34], [55, 64], [3, 53], [35, 67], [42, 28], [43, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [61, 50]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [32, 28, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-33587, 11759, 18643, 15657, 3989]
  a := ![3, -62, -1, -63, -119]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-13143, -16315, 18643, 15657, 3989]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-179, -84, -59, -38, -61]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![-179, -84, -59, -38, -61]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![16, 33, 1, 0, 0], ![40, 20, 0, 1, 0], ![51, 28, 0, 0, 1]] where
  M :=![![![-179, -84, -59, -38, -61], ![-244, -131, -92, -72, -106], ![-212, -81, -59, -58, -110], ![-98, 37, 23, 29, -11], ![36, 7, 6, 16, 35]]]
  hmulB := by decide  
  f := ![![![-261, 222, -53, 64, 71]], ![![284, -399, 316, -120, 242]], ![![80, -138, 131, -42, 120]], ![![-86, 29, 55, 7, 113]], ![![-65, -7, 89, -4, 144]]]
  g := ![![![76, 61, -59, -38, -61], ![134, 103, -92, -72, -106], ![122, 86, -59, -58, -110], ![-15, -14, 23, 29, -11], ![-35, -21, 6, 16, 35]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P1 : CertificateIrreducibleZModOfList' 71 2 2 6 [50, 37, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 70], [0, 1]]
 g := ![![[5, 27], [6, 4], [10, 54], [58], [20], [1]], ![[0, 44], [0, 67], [0, 17], [58], [20], [1]]]
 h' := ![![[34, 70], [55, 13], [68, 69], [21, 14], [9, 49], [21, 34], [0, 1]], ![[0, 1], [0, 58], [0, 2], [0, 57], [42, 22], [41, 37], [34, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [29, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N1 : CertifiedPrimeIdeal' SI71N1 71 where
  n := 2
  hpos := by decide
  P := [50, 37, 1]
  hirr := P71P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-512, 35, 277, -2, -339]
  a := ![1, -6, 1, -7, -12]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![175, 6, 277, -2, -339]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N1 B_one_repr
lemma NI71N1 : Nat.card (O ⧸ I71N1) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N1

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, 1, 2, 0, 4]] i)))

def SI71N2: IdealEqSpanCertificate' Table ![![-3, 1, 2, 0, 4]] 
 ![![71, 0, 0, 0, 0], ![57, 1, 0, 0, 0], ![44, 0, 1, 0, 0], ![31, 0, 0, 1, 0], ![34, 0, 0, 0, 1]] where
  M :=![![![-3, 1, 2, 0, 4], ![16, -13, 2, -4, -8], ![-16, 17, -9, 6, -4], ![-16, 6, 10, 3, 26], ![12, -5, -6, -2, -13]]]
  hmulB := by decide  
  f := ![![![851, 367, 260, 180, 316]], ![![701, 302, 214, 148, 260]], ![![540, 233, 165, 114, 200]], ![![371, 161, 114, 79, 138]], ![![406, 175, 124, 86, 151]]]
  g := ![![![-4, 1, 2, 0, 4], ![15, -13, 2, -4, -8], ![-9, 17, -9, 6, -4], ![-25, 6, 10, 3, 26], ![15, -5, -6, -2, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![11, -13, 3, -4, -3]] ![![-179, -84, -59, -38, -61]]
  ![![851, 367, 260, 180, 316]] where
 M := ![![![851, 367, 260, 180, 316]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![851, 367, 260, 180, 316]] ![![-3, 1, 2, 0, 4]]
  ![![71, 0, 0, 0, 0]] where
 M := ![![![71, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1, I71N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
    exact isPrimeI71N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0 ⊙ MulI71N1)
instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![45, 28, -100, 10, -148]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![45, 28, -100, 10, -148]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![66, 51, 1, 0, 0], ![65, 24, 0, 1, 0], ![32, 38, 0, 0, 1]] where
  M :=![![![45, 28, -100, 10, -148], ![-592, 409, 36, 116, 356], ![712, -696, 293, -204, -8], ![280, 106, -510, 39, -782], ![-180, -38, 278, -16, 439]]]
  hmulB := by decide  
  f := ![![![3869, 1696, 1200, 818, 1408]], ![![5632, 2481, 1756, 1220, 2092]], ![![7490, 3291, 2329, 1604, 2756]], ![![5301, 2326, 1646, 1129, 1942]], ![![4620, 2032, 1438, 992, 1703]]]
  g := ![![![147, 144, -100, 10, -148], ![-300, -243, 36, 116, 356], ![-70, -143, 293, -204, -8], ![773, 752, -510, 39, -782], ![-432, -418, 278, -16, 439]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [55, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [55, 72], [0, 1]]
 g := ![![[72, 4], [27], [72], [67, 70], [32], [1]], ![[0, 69], [27], [72], [48, 3], [32], [1]]]
 h' := ![![[55, 72], [36, 2], [39, 10], [38, 46], [24, 17], [18, 55], [0, 1]], ![[0, 1], [0, 71], [5, 63], [13, 27], [10, 56], [50, 18], [55, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [63, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [55, 18, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2834, 630, 3574, 4858, 6014]
  a := ![1, 25, -3, 24, 59]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-10232, -7216, 3574, 4858, 6014]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![57, 26, 18, 12, 20]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![57, 26, 18, 12, 20]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![56, 54, 1, 0, 0], ![42, 69, 0, 1, 0], ![55, 50, 0, 0, 1]] where
  M :=![![![57, 26, 18, 12, 20], ![80, 39, 28, 20, 32], ![64, 26, 19, 16, 28], ![16, -4, -4, -3, 4], ![-8, -4, -2, -4, -7]]]
  hmulB := by decide  
  f := ![![![17, -18, 10, -4, 4]], ![![16, 7, -28, 4, -32]], ![![24, -8, -13, 0, -20]], ![![26, -5, -20, 1, -28]], ![![23, -8, -12, 0, -19]]]
  g := ![![![-35, -38, 18, 12, 20], ![-56, -61, 28, 20, 32], ![-44, -48, 19, 16, 28], ![2, 3, -4, -3, 4], ![9, 10, -2, -4, -7]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P1 : CertificateIrreducibleZModOfList' 73 2 2 6 [7, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [64, 72], [0, 1]]
 g := ![![[43, 50], [49], [23], [10, 69], [8], [1]], ![[31, 23], [49], [23], [46, 4], [8], [1]]]
 h' := ![![[64, 72], [58, 59], [67, 7], [3, 60], [66, 54], [66, 64], [0, 1]], ![[0, 1], [38, 14], [4, 66], [47, 13], [18, 19], [1, 9], [64, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44]]
 b := ![[], [26, 22]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N1 : CertifiedPrimeIdeal' SI73N1 73 where
  n := 2
  hpos := by decide
  P := [7, 9, 1]
  hirr := P73P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2207, -1606, 294, 464, 1530]
  a := ![-1, -7, 5, -5, -27]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1615, -1726, 294, 464, 1530]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N1 B_one_repr
lemma NI73N1 : Nat.card (O ⧸ I73N1) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N1

def I73N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-37, -14, -10, -6, -12]] i)))

def SI73N2: IdealEqSpanCertificate' Table ![![-37, -14, -10, -6, -12]] 
 ![![73, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![69, 0, 1, 0, 0], ![50, 0, 0, 1, 0], ![50, 0, 0, 0, 1]] where
  M :=![![![-37, -14, -10, -6, -12], ![-48, -23, -16, -8, -12], ![-24, -22, -15, -12, -12], ![0, -2, -2, -11, -18], ![-4, 6, 4, 4, 1]]]
  hmulB := by decide  
  f := ![![![251, -214, 50, -62, -72]], ![![27, -21, 2, -6, -12]], ![![231, -200, 51, -58, -60]], ![![190, -162, 38, -47, -54]], ![![162, -138, 32, -40, -47]]]
  g := ![![![23, -14, -10, -6, -12], ![31, -23, -16, -8, -12], ![33, -22, -15, -12, -12], ![22, -2, -2, -11, -18], ![-8, 6, 4, 4, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N2 : Nat.card (O ⧸ I73N2) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N2)

lemma isPrimeI73N2 : Ideal.IsPrime I73N2 := prime_ideal_of_norm_prime hp73.out _ NI73N2
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![45, 28, -100, 10, -148]] ![![57, 26, 18, 12, 20]]
  ![![-251, 214, -50, 62, 72]] where
 M := ![![![-251, 214, -50, 62, 72]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI73N1 : IdealMulLeCertificate' Table 
  ![![-251, 214, -50, 62, 72]] ![![-37, -14, -10, -6, -12]]
  ![![73, 0, 0, 0, 0]] where
 M := ![![![-73, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0, 0, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0, 0, 0]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![0, 0, 79, 0, 0], ![0, 0, 0, 79, 0], ![0, 0, 0, 0, 79]] where
  M :=![![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![0, 0, 79, 0, 0], ![0, 0, 0, 79, 0], ![0, 0, 0, 0, 79]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 5 2 6 [60, 66, 66, 33, 59, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [76, 19, 2, 44, 10], [9, 26, 30, 7, 66], [0, 50, 75, 77, 11], [14, 62, 51, 30, 71], [0, 1]]
 g := ![![[4, 24, 53, 57, 18], [37, 29, 41, 51, 10], [28, 25, 42, 35, 45], [46, 57, 51, 20, 1], [], []], ![[65, 38, 13, 39, 53, 77, 24, 10], [77, 45, 37, 61, 57, 5, 41, 67], [47, 4, 52, 5, 51, 29, 56, 22], [15, 5, 46, 64, 11, 39, 22, 44], [34, 34, 77, 4], [43, 28, 36, 21]], ![[29, 68, 43, 72, 69, 62, 8, 57], [59, 76, 41, 48, 64, 41, 58, 57], [72, 59, 75, 45, 19, 0, 63, 15], [27, 17, 14, 1, 42, 50, 17, 68], [13, 17, 78, 76], [11, 61, 38, 11]], ![[34, 74, 49, 19, 49, 52, 15, 1], [36, 25, 63, 12, 64, 34, 46, 38], [24, 49, 12, 53, 75, 51, 54, 18], [34, 46, 5, 50, 73, 43, 15, 23], [13, 55, 57, 72], [60, 72, 6, 42]], ![[23, 52, 10, 62, 76, 60, 45, 39], [12, 40, 31, 32, 51, 68, 11, 15], [51, 35, 4, 62, 50, 49, 0, 53], [55, 67, 63, 60, 19, 75, 10, 69], [24, 39, 57, 2], [59, 68, 10, 64]]]
 h' := ![![[76, 19, 2, 44, 10], [71, 51, 30, 10, 52], [58, 74, 48, 2, 22], [5, 22, 17, 29, 60], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[9, 26, 30, 7, 66], [35, 64, 4, 11, 78], [9, 69, 13, 17, 33], [20, 54, 59, 25, 52], [46, 16, 3, 31, 6], [36, 29, 60, 19, 2], [76, 19, 2, 44, 10]], ![[0, 50, 75, 77, 11], [3, 52, 49, 19, 42], [74, 4, 69, 0, 37], [55, 14, 12, 36, 66], [54, 13, 72, 19, 48], [53, 32, 30, 54, 32], [9, 26, 30, 7, 66]], ![[14, 62, 51, 30, 71], [52, 0, 10, 43, 6], [61, 62, 72, 27, 5], [14, 11, 77, 31, 4], [60, 22, 66, 56, 14], [34, 15, 64, 64, 54], [0, 50, 75, 77, 11]], ![[0, 1], [47, 70, 65, 75, 59], [77, 28, 35, 33, 61], [2, 57, 72, 37, 55], [26, 28, 17, 52, 10], [53, 3, 3, 21, 70], [14, 62, 51, 30, 71]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12, 14, 43, 9], [], [], []]
 b := ![[], [29, 7, 45, 54, 7], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 5
  hpos := by decide
  P := [60, 66, 66, 33, 59, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11102882148, 4924165432, 2142725532, -5673762620, -14030527980]
  a := ![0, -4, -2, -14, 18]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-140542812, 62331208, 27123108, -71819780, -177601620]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 3077056399 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def PBC79 : ContainsPrimesAboveP 79 ![I79N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![79, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 79 (by decide) 𝕀

instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![257, -139, -79, -38, -233]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![257, -139, -79, -38, -233]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![16, 79, 1, 0, 0], ![64, 34, 0, 1, 0], ![24, 16, 0, 0, 1]] where
  M :=![![![257, -139, -79, -38, -233], ![-932, 801, -202, 232, 238], ![476, -692, 569, -208, 458], ![1382, -773, -383, -213, -1201], ![-792, 456, 198, 126, 661]]]
  hmulB := by decide  
  f := ![![![1011, 485, 341, 232, 367]], ![![1468, 715, 506, 412, 658]], ![![1608, 779, 551, 440, 704]], ![![1386, 665, 469, 345, 551]], ![![572, 278, 196, 146, 231]]]
  g := ![![![115, 134, -79, -38, -233], ![-220, 61, -202, 232, 238], ![-76, -553, 569, -208, 458], ![602, 674, -383, -213, -1201], ![-336, -362, 198, 126, 661]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [11, 70, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 82], [0, 1]]
 g := ![![[29, 68], [82, 26], [49], [48], [2, 3], [1]], ![[0, 15], [5, 57], [49], [48], [41, 80], [1]]]
 h' := ![![[13, 82], [11, 63], [69, 21], [39, 7], [61, 31], [72, 13], [0, 1]], ![[0, 1], [0, 20], [10, 62], [47, 76], [49, 52], [75, 70], [13, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [75]]
 b := ![[], [26, 79]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [11, 70, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![146, -170, -118, -210, 126]
  a := ![-1, -1, -1, -2, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![150, 172, -118, -210, 126]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![25, -13, -8, -6, 8]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![25, -13, -8, -6, 8]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![9, 11, 1, 0, 0], ![67, 50, 0, 1, 0], ![52, 78, 0, 0, 1]] where
  M :=![![![25, -13, -8, -6, 8], ![32, -19, -14, -44, -52], ![-104, 43, 25, -6, -80], ![-176, 84, 56, 121, 88], ![72, -31, -18, 2, 53]]]
  hmulB := by decide  
  f := ![![![27, -19, -26, -6, -52]], ![![-208, 145, -26, 40, 68]], ![![-23, 15, -5, 4, 4]], ![![-101, 71, -38, 19, -4]], ![![-180, 125, -40, 34, 33]]]
  g := ![![![1, -3, -8, -6, 8], ![70, 77, -14, -44, -52], ![51, 76, 25, -6, -80], ![-161, -162, 56, 121, 88], ![-32, -49, -18, 2, 53]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P1 : CertificateIrreducibleZModOfList' 83 2 2 6 [74, 42, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [41, 82], [0, 1]]
 g := ![![[23, 65], [68, 69], [81], [17], [22, 21], [1]], ![[32, 18], [75, 14], [81], [17], [53, 62], [1]]]
 h' := ![![[41, 82], [31, 27], [41, 22], [15, 9], [32, 10], [9, 41], [0, 1]], ![[0, 1], [59, 56], [30, 61], [52, 74], [27, 73], [30, 42], [41, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [64]]
 b := ![[], [8, 32]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N1 : CertifiedPrimeIdeal' SI83N1 83 where
  n := 2
  hpos := by decide
  P := [74, 42, 1]
  hirr := P83P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2897, -1339, -538, -487, 489]
  a := ![3, 3, 0, -1, 21]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![180, -111, -538, -487, 489]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N1 B_one_repr
lemma NI83N1 : Nat.card (O ⧸ I83N1) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N1

def I83N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-277, -120, -85, -58, -101]] i)))

def SI83N2: IdealEqSpanCertificate' Table ![![-277, -120, -85, -58, -101]] 
 ![![83, 0, 0, 0, 0], ![69, 1, 0, 0, 0], ![68, 0, 1, 0, 0], ![68, 0, 0, 1, 0], ![25, 0, 0, 0, 1]] where
  M :=![![![-277, -120, -85, -58, -101], ![-404, -175, -124, -84, -146], ![-292, -129, -91, -62, -106], ![-10, -7, -5, -5, -7], ![36, 17, 12, 8, 13]]]
  hmulB := by decide  
  f := ![![![105, -66, -19, -16, -89]], ![![83, -51, -17, -12, -73]], ![![88, -57, -13, -14, -70]], ![![94, -59, -17, -15, -79]], ![![27, -17, -5, -4, -24]]]
  g := ![![![244, -120, -85, -58, -101], ![355, -175, -124, -84, -146], ![261, -129, -91, -62, -106], ![16, -7, -5, -5, -7], ![-34, 17, 12, 8, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N2 : Nat.card (O ⧸ I83N2) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N2)

lemma isPrimeI83N2 : Ideal.IsPrime I83N2 := prime_ideal_of_norm_prime hp83.out _ NI83N2
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![257, -139, -79, -38, -233]] ![![25, -13, -8, -6, 8]]
  ![![105, -66, -19, -16, -89]] where
 M := ![![![105, -66, -19, -16, -89]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI83N1 : IdealMulLeCertificate' Table 
  ![![105, -66, -19, -16, -89]] ![![-277, -120, -85, -58, -101]]
  ![![83, 0, 0, 0, 0]] where
 M := ![![![83, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC83 : ContainsPrimesAboveP 83 ![I83N0, I83N1, I83N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
    exact isPrimeI83N1
    exact isPrimeI83N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 83 (by decide) (𝕀 ⊙ MulI83N0 ⊙ MulI83N1)
instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![91, -72, 9, -18, -39]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![91, -72, 9, -18, -39]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![6, 31, 1, 0, 0], ![81, 66, 0, 1, 0], ![21, 47, 0, 0, 1]] where
  M :=![![![91, -72, 9, -18, -39], ![-156, 181, -108, 60, -30], ![-60, -27, 121, -18, 210], ![498, -393, 45, -137, -249], ![-300, 231, -24, 72, 109]]]
  hmulB := by decide  
  f := ![![![308915, 134298, 95085, 64944, 112659]], ![![450636, 195911, 138708, 94740, 164346]], ![![181482, 78898, 55861, 38154, 66186]], ![![615489, 267579, 189450, 129397, 224466]], ![![310395, 134942, 95541, 65256, 113200]]]
  g := ![![![26, 30, 9, -18, -39], ![-42, 11, -108, 60, -30], ![-42, -140, 121, -18, 210], ![186, 213, 45, -137, -249], ![-93, -100, -24, 72, 109]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [78, 56, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 88], [0, 1]]
 g := ![![[3, 8], [50], [9], [81, 81], [84, 21], [1]], ![[0, 81], [50], [9], [84, 8], [65, 68], [1]]]
 h' := ![![[33, 88], [48, 39], [11, 36], [1, 3], [34, 9], [11, 33], [0, 1]], ![[0, 1], [0, 50], [42, 53], [11, 86], [64, 80], [32, 56], [33, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [32, 52]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [78, 56, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![731, -180, -8, 506, 1692]
  a := ![1, 5, -3, 4, 17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-851, -1268, -8, 506, 1692]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-55, 26, 17, 34, 21]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![-55, 26, 17, 34, 21]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![71, 48, 1, 0, 0], ![63, 46, 0, 1, 0], ![71, 32, 0, 0, 1]] where
  M :=![![![-55, 26, 17, 34, 21], ![84, -33, -16, 60, 162], ![324, -149, -93, -118, 18], ![-6, -13, -23, -259, -453], ![-220, 101, 64, 84, -5]]]
  hmulB := by decide  
  f := ![![![-143, -112, -59, -48, -93]], ![![-372, -19, -128, -28, -102]], ![![-317, -101, -116, -54, -129]], ![![-291, -91, -108, -49, -120]], ![![-249, -95, -93, -48, -110]]]
  g := ![![![-55, -34, 17, 34, 21], ![-158, -81, -16, 60, 162], ![147, 103, -93, -118, 18], ![563, 309, -23, -259, -453], ![-109, -75, 64, 84, -5]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P1 : CertificateIrreducibleZModOfList' 89 2 2 6 [55, 42, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [47, 88], [0, 1]]
 g := ![![[4, 34], [10], [10], [77, 73], [41, 73], [1]], ![[0, 55], [10], [10], [37, 16], [1, 16], [1]]]
 h' := ![![[47, 88], [41, 37], [18, 30], [37, 59], [59, 47], [34, 47], [0, 1]], ![[0, 1], [0, 52], [4, 59], [51, 30], [43, 42], [18, 42], [47, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [86]]
 b := ![[], [13, 43]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N1 : CertifiedPrimeIdeal' SI89N1 89 where
  n := 2
  hpos := by decide
  P := [55, 42, 1]
  hirr := P89P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![335, -49, -28, 19, -201]
  a := ![4, 0, 0, 1, -3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![173, 77, -28, 19, -201]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N1 B_one_repr
lemma NI89N1 : Nat.card (O ⧸ I89N1) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N1

def I89N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-117, 55, 36, 66, 34]] i)))

def SI89N2: IdealEqSpanCertificate' Table ![![-117, 55, 36, 66, 34]] 
 ![![89, 0, 0, 0, 0], ![20, 1, 0, 0, 0], ![67, 0, 1, 0, 0], ![32, 0, 0, 1, 0], ![17, 0, 0, 0, 1]] where
  M :=![![![-117, 55, 36, 66, 34], ![136, -51, -22, 136, 328], ![656, -299, -187, -214, 80], ![92, -74, -74, -549, -886], ![-448, 205, 128, 154, -41]]]
  hmulB := by decide  
  f := ![![![37835, 16527, 11650, 7982, 13834]], ![![9124, 3983, 2810, 1924, 3336]], ![![28937, 12638, 8909, 6104, 10578]], ![![13620, 5954, 4194, 2875, 4982]], ![![7171, 3130, 2208, 1512, 2621]]]
  g := ![![![-71, 55, 36, 66, 34], ![-82, -51, -22, 136, 328], ![277, -299, -187, -214, 80], ![440, -74, -74, -549, -886], ![-195, 205, 128, 154, -41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N2 : Nat.card (O ⧸ I89N2) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N2)

lemma isPrimeI89N2 : Ideal.IsPrime I89N2 := prime_ideal_of_norm_prime hp89.out _ NI89N2
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![91, -72, 9, -18, -39]] ![![-55, 26, 17, 34, 21]]
  ![![551, -304, -220, -902, -1242]] where
 M := ![![![551, -304, -220, -902, -1242]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI89N1 : IdealMulLeCertificate' Table 
  ![![551, -304, -220, -902, -1242]] ![![-117, 55, 36, 66, 34]]
  ![![89, 0, 0, 0, 0]] where
 M := ![![![223301, -76273, -24564, 346032, 751516]]]
 hmul := by decide  
 g := ![![![![2509, -857, -276, 3888, 8444]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-199, 88, 52, 12, -116]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![-199, 88, 52, 12, -116]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![43, 14, 1, 0, 0], ![77, 20, 0, 1, 0], ![90, 31, 0, 0, 1]] where
  M :=![![![-199, 88, 52, 12, -116], ![-464, 225, 152, 360, 304], ![608, -252, -135, 208, 776], ![1784, -832, -536, -883, -304], ![-440, 184, 100, -128, -523]]]
  hmulB := by decide  
  f := ![![![105, -104, 156, -28, 164]], ![![656, -287, -152, -72, -496]], ![![131, -78, 45, -20, 4]], ![![221, -148, 100, -39, 36]], ![![306, -185, 92, -48, -11]]]
  g := ![![![73, 28, 52, 12, -116], ![-640, -191, 152, 360, 304], ![-819, -274, -135, 208, 776], ![1239, 348, -536, -883, -304], ![538, 181, 100, -128, -523]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [16, 85, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 96], [0, 1]]
 g := ![![[72, 91], [6], [73], [62], [88], [12, 1]], ![[0, 6], [6], [73], [62], [88], [24, 96]]]
 h' := ![![[12, 96], [94, 73], [44, 43], [57, 48], [51, 16], [2, 31], [0, 1]], ![[0, 1], [0, 24], [75, 54], [51, 49], [49, 81], [83, 66], [12, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [63]]
 b := ![[], [5, 80]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [16, 85, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1164, -3648, 2412, 1892, -2728]
  a := ![7, -21, -1, -21, -65]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-28, 96, 2412, 1892, -2728]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-195, 91, 84, 24, 208]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![-195, 91, 84, 24, 208]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![87, 55, 1, 0, 0], ![65, 26, 0, 1, 0], ![94, 13, 0, 0, 1]] where
  M :=![![![-195, 91, 84, 24, 208], ![832, -687, 134, -200, -272], ![-544, 691, -487, 206, -328], ![-1072, 526, 418, 147, 1082], ![620, -317, -220, -86, -593]]]
  hmulB := by decide  
  f := ![![![-128171, -55725, -39454, -26948, -46744]], ![![-186976, -81289, -57554, -39316, -68200]], ![![-222381, -96683, -68453, -46758, -81108]], ![![-136067, -59157, -41884, -28609, -49626]], ![![-149086, -64818, -45892, -31346, -54373]]]
  g := ![![![-295, -81, 84, 24, 208], ![286, 7, 134, -200, -272], ![611, 272, -487, 206, -328], ![-1533, -416, 418, 147, 1082], ![836, 224, -220, -86, -593]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P1 : CertificateIrreducibleZModOfList' 97 2 2 6 [53, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [89, 96], [0, 1]]
 g := ![![[88, 11], [36], [33], [33], [24], [89, 1]], ![[0, 86], [36], [33], [33], [24], [81, 96]]]
 h' := ![![[89, 96], [5, 37], [78, 91], [88, 18], [24, 18], [36, 11], [0, 1]], ![[0, 1], [0, 60], [29, 6], [41, 79], [74, 79], [45, 86], [89, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [42, 59]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N1 : CertifiedPrimeIdeal' SI97N1 97 where
  n := 2
  hpos := by decide
  P := [53, 8, 1]
  hirr := P97P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-322, 17, 332, 393, 273]
  a := ![1, -6, 1, -7, -18]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-829, -330, 332, 393, 273]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N1 B_one_repr
lemma NI97N1 : Nat.card (O ⧸ I97N1) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N1

def I97N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-151, 64, 36, -28, -152]] i)))

def SI97N2: IdealEqSpanCertificate' Table ![![-151, 64, 36, -28, -152]] 
 ![![97, 0, 0, 0, 0], ![56, 1, 0, 0, 0], ![81, 0, 1, 0, 0], ![32, 0, 0, 1, 0], ![87, 0, 0, 0, 1]] where
  M :=![![![-151, 64, 36, -28, -152], ![-608, 285, 184, 320, 136], ![272, -96, -35, 368, 824], ![1952, -892, -556, -651, 212], ![-216, 80, 32, -240, -563]]]
  hmulB := by decide  
  f := ![![![406713, 176848, 125180, 85516, 148328]], ![![240920, 104757, 74152, 50656, 87864]], ![![344089, 149616, 105905, 72348, 125488]], ![![134368, 58428, 41356, 28253, 49004]], ![![364215, 158368, 112100, 76580, 132829]]]
  g := ![![![77, 64, 36, -28, -152], ![-552, 285, 184, 320, 136], ![-773, -96, -35, 368, 824], ![1024, -892, -556, -651, 212], ![509, 80, 32, -240, -563]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N2 : Nat.card (O ⧸ I97N2) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N2)

lemma isPrimeI97N2 : Ideal.IsPrime I97N2 := prime_ideal_of_norm_prime hp97.out _ NI97N2
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![-199, 88, 52, 12, -116]] ![![-195, 91, 84, 24, 208]]
  ![![-1051, 451, 288, 76, -612]] where
 M := ![![![-1051, 451, 288, 76, -612]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI97N1 : IdealMulLeCertificate' Table 
  ![![-1051, 451, 288, 76, -612]] ![![-151, 64, 36, -28, -152]]
  ![![97, 0, 0, 0, 0]] where
 M := ![![![243373, -83129, -26772, 377136, 819068]]]
 hmul := by decide  
 g := ![![![![2509, -857, -276, 3888, 8444]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0, 0, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0, 0, 0]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![0, 0, 101, 0, 0], ![0, 0, 0, 101, 0], ![0, 0, 0, 0, 101]] where
  M :=![![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![0, 0, 101, 0, 0], ![0, 0, 0, 101, 0], ![0, 0, 0, 0, 101]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 5 2 6 [81, 2, 75, 12, 76, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 69, 20, 51, 40], [77, 50, 81, 77, 44], [7, 22, 100, 77, 16], [42, 60, 1, 98, 1], [0, 1]]
 g := ![![[0, 73, 70, 84, 81], [97, 47, 48, 13], [70, 47, 67, 100, 78], [79, 4, 15, 49], [25, 1], []], ![[19, 99, 85, 54, 0, 48, 27, 41], [98, 30, 50, 54], [9, 36, 7, 47, 94, 33, 34, 15], [93, 50, 88, 16], [64, 81, 70, 96], [45, 14, 1, 42, 82, 50, 35, 67]], ![[42, 80, 7, 36, 22, 88, 37, 42], [77, 46, 100, 58], [6, 22, 75, 35, 93, 3, 34, 89], [86, 88, 42, 49], [86, 11, 17, 17], [36, 6, 86, 45, 34, 57, 3, 41]], ![[64, 11, 66, 17, 38, 1, 27, 43], [1, 79, 93, 37], [70, 43, 47, 23, 6, 97, 32, 49], [43, 78, 72, 79], [35, 22, 67, 52], [77, 64, 18, 85, 34, 65, 37, 56]], ![[7, 40, 7, 100, 75, 75, 46, 45], [40, 1, 64, 37], [40, 56, 94, 100, 0, 88, 97, 21], [91, 82, 66, 56], [35, 69, 89, 33], [97, 6, 81, 25, 16, 14, 16, 1]]]
 h' := ![![[0, 69, 20, 51, 40], [15, 6, 98, 91, 92], [87, 12, 0, 66, 66], [90, 20, 99, 23, 52], [96, 71, 42, 29, 7], [0, 0, 0, 1], [0, 1]], ![[77, 50, 81, 77, 44], [20, 76, 63, 87, 7], [79, 35, 46, 73, 16], [23, 51, 84, 94, 66], [48, 92, 7, 62, 4], [92, 89, 51, 12, 46], [0, 69, 20, 51, 40]], ![[7, 22, 100, 77, 16], [9, 97, 51, 98, 33], [40, 3, 88, 7, 19], [80, 77, 96, 51, 93], [73, 36, 66, 34, 94], [26, 93, 83, 23, 57], [77, 50, 81, 77, 44]], ![[42, 60, 1, 98, 1], [85, 83, 17, 25, 3], [41, 84, 84, 86, 21], [22, 46, 53, 75, 74], [77, 55, 32, 89, 33], [65, 17, 30, 15, 70], [7, 22, 100, 77, 16]], ![[0, 1], [93, 41, 74, 2, 67], [0, 68, 85, 71, 80], [45, 8, 72, 60, 18], [12, 49, 55, 89, 64], [76, 3, 38, 50, 29], [42, 60, 1, 98, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 83, 13, 26], [], [], []]
 b := ![[], [51, 18, 2, 29, 65], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 5
  hpos := by decide
  P := [81, 2, 75, 12, 76, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1013988591, 520778119, 288254404, 720726506, 614810028]
  a := ![3, 8, -1, 13, 9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-10039491, 5156219, 2854004, 7135906, 6087228]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10510100501 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def PBC101 : ContainsPrimesAboveP 101 ![I101N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![101, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 101 (by decide) 𝕀

instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, -5, 2, 0, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![5, -5, 2, 0, 0]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![54, 49, 1, 0, 0], ![32, 47, 0, 1, 0], ![54, 97, 0, 0, 1]] where
  M :=![![![5, -5, 2, 0, 0], ![0, 7, -10, 4, 0], ![0, -1, 3, -6, 12], ![24, -26, 10, -17, -30], ![-28, 21, -2, 10, 7]]]
  hmulB := by decide  
  f := ![![![-325, -139, -100, -68, -120]], ![![-480, -201, -142, -96, -168]], ![![-402, -170, -121, -82, -144]], ![![-320, -135, -96, -65, -114]], ![![-622, -262, -186, -126, -221]]]
  g := ![![![-1, -1, 2, 0, 0], ![4, 3, -10, 4, 0], ![-6, -10, 3, -6, 12], ![16, 31, 10, -17, -30], ![-6, -10, -2, 10, 7]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [57, 49, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [54, 102], [0, 1]]
 g := ![![[37, 68], [50, 16], [33, 68], [50], [7], [54, 1]], ![[1, 35], [90, 87], [100, 35], [50], [7], [5, 102]]]
 h' := ![![[54, 102], [34, 45], [76, 99], [66, 45], [54, 87], [12, 78], [0, 1]], ![[0, 1], [95, 58], [66, 4], [24, 58], [14, 16], [1, 25], [54, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [82]]
 b := ![[], [26, 41]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [57, 49, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9901, -7604, 1402, 1564, 3304]
  a := ![3, -15, 8, -11, -59]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2857, -4566, 1402, 1564, 3304]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1241, -535, -379, -258, -451]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![-1241, -535, -379, -258, -451]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![90, 98, 1, 0, 0], ![38, 72, 0, 1, 0], ![89, 101, 0, 0, 1]] where
  M :=![![![-1241, -535, -379, -258, -451], ![-1804, -783, -554, -372, -646], ![-1292, -582, -411, -280, -470], ![-38, -35, -25, -35, -47], ![152, 80, 56, 38, 55]]]
  hmulB := by decide  
  f := ![![![129, -187, 153, -56, 121]], ![![484, -193, -262, -48, -578]], ![![562, -338, -117, -92, -440]], ![![392, -213, -119, -57, -353]], ![![583, -346, -129, -94, -466]]]
  g := ![![![804, 978, -379, -258, -451], ![1162, 1413, -554, -372, -646], ![856, 1042, -411, -280, -470], ![75, 94, -25, -35, -47], ![-109, -133, 56, 38, 55]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P1 : CertificateIrreducibleZModOfList' 103 2 2 6 [37, 52, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [51, 102], [0, 1]]
 g := ![![[71, 93], [92, 82], [25, 49], [16], [18], [51, 1]], ![[76, 10], [51, 21], [52, 54], [16], [18], [102, 102]]]
 h' := ![![[51, 102], [98, 14], [2, 59], [44, 7], [11, 99], [70, 92], [0, 1]], ![[0, 1], [91, 89], [24, 44], [92, 96], [13, 4], [24, 11], [51, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49]]
 b := ![[], [19, 76]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N1 : CertifiedPrimeIdeal' SI103N1 103 where
  n := 2
  hpos := by decide
  P := [37, 52, 1]
  hirr := P103P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3887, 1506, 815, -364, -2556]
  a := ![0, -12, 2, -18, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1593, 2000, 815, -364, -2556]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N1 B_one_repr
lemma NI103N1 : Nat.card (O ⧸ I103N1) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N1

def I103N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, -14, 3, -4, -5]] i)))

def SI103N2: IdealEqSpanCertificate' Table ![![17, -14, 3, -4, -5]] 
 ![![103, 0, 0, 0, 0], ![15, 1, 0, 0, 0], ![42, 0, 1, 0, 0], ![38, 0, 0, 1, 0], ![73, 0, 0, 0, 1]] where
  M :=![![![17, -14, 3, -4, -5], ![-20, 27, -20, 8, -14], ![-28, 9, 19, 2, 38], ![86, -73, 17, -21, -25], ![-48, 41, -10, 12, 13]]]
  hmulB := by decide  
  f := ![![![231, 76, 53, 10, 35]], ![![35, 13, 9, 2, 5]], ![![94, 33, 23, 6, 16]], ![![88, 27, 19, 5, 17]], ![![165, 53, 37, 6, 24]]]
  g := ![![![6, -14, 3, -4, -5], ![11, 27, -20, 8, -14], ![-37, 9, 19, 2, 38], ![30, -73, 17, -21, -25], ![-16, 41, -10, 12, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N2 : Nat.card (O ⧸ I103N2) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N2)

lemma isPrimeI103N2 : Ideal.IsPrime I103N2 := prime_ideal_of_norm_prime hp103.out _ NI103N2
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![5, -5, 2, 0, 0]] ![![-1241, -535, -379, -258, -451]]
  ![![231, 76, 53, 10, 35]] where
 M := ![![![231, 76, 53, 10, 35]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI103N1 : IdealMulLeCertificate' Table 
  ![![231, 76, 53, 10, 35]] ![![17, -14, 3, -4, -5]]
  ![![103, 0, 0, 0, 0]] where
 M := ![![![103, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC103 : ContainsPrimesAboveP 103 ![I103N0, I103N1, I103N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
    exact isPrimeI103N1
    exact isPrimeI103N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 103 (by decide) (𝕀 ⊙ MulI103N0 ⊙ MulI103N1)


lemma PB187I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 103 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 103 (by omega)

def PB187I2 : PrimesBelowBoundCertificateInterval O 61 103 187 where
  m := 9
  g := ![1, 3, 3, 1, 3, 3, 3, 1, 3]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103]
  hP := PB187I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0]
    · exact ![I71N0, I71N1, I71N2]
    · exact ![I73N0, I73N1, I73N2]
    · exact ![I79N0]
    · exact ![I83N0, I83N1, I83N2]
    · exact ![I89N0, I89N1, I89N2]
    · exact ![I97N0, I97N1, I97N2]
    · exact ![I101N0]
    · exact ![I103N0, I103N1, I103N2]
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
    · exact ![1350125107]
    · exact ![5041, 5041, 71]
    · exact ![5329, 5329, 73]
    · exact ![3077056399]
    · exact ![6889, 6889, 83]
    · exact ![7921, 7921, 89]
    · exact ![9409, 9409, 97]
    · exact ![10510100501]
    · exact ![10609, 10609, 103]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
      exact NI71N2
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
      exact NI73N2
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
      exact NI83N1
      exact NI83N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
      exact NI103N2
  β := ![I71N2, I73N2, I83N2, I89N2, I97N2, I103N2]
  Il := ![[], [I71N2], [I73N2], [], [I83N2], [I89N2], [I97N2], [], [I103N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
