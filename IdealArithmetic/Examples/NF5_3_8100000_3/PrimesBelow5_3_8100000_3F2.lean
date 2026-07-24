
import IdealArithmetic.Examples.NF5_3_8100000_3.RI5_3_8100000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![317, 32, -22, 0, -80]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![317, 32, -22, 0, -80]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![0, 0, 67, 0, 0], ![53, 47, 53, 1, 0], ![22, 13, 12, 0, 1]] where
  M :=![![![317, 32, -22, 0, -80], ![-240, 11, 32, 28, 80], ![240, 96, 11, 60, -24], ![108, 28, 0, 15, -16], ![-78, 16, 14, 16, 31]]]
  hmulB := by decide  
  f := ![![![-1, 0, -2, 8, 0]], ![![0, -7, 0, -4, 16]], ![![48, 48, -7, -36, -24]], ![![37, 33, -7, -25, -8]], ![![8, 7, -2, -4, -1]]]
  g := ![![![31, 16, 14, 0, -80], ![-52, -35, -36, 28, 80], ![-36, -36, -43, 60, -24], ![-5, -7, -9, 15, -16], ![-24, -17, -18, 16, 31]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [29, 64, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 51, 56], [46, 15, 11], [0, 1]]
 g := ![![[64, 45, 60], [51, 12, 25], [20, 19], [63, 16], [66, 1], []], ![[14, 56, 11, 23], [40, 56, 38, 1], [9, 65], [52, 33], [12, 24], [30, 54]], ![[11, 26, 14, 27], [18, 11, 44, 27], [9, 24], [32, 62], [37, 55], [8, 54]]]
 h' := ![![[20, 51, 56], [62, 62, 23], [49, 3, 62], [19, 13, 35], [29, 35, 4], [0, 0, 1], [0, 1]], ![[46, 15, 11], [6, 54, 65], [47, 13, 26], [43, 35, 47], [55, 21, 10], [66, 28, 15], [20, 51, 56]], ![[0, 1], [16, 18, 46], [13, 51, 46], [26, 19, 52], [63, 11, 53], [8, 39, 51], [46, 15, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46, 7], []]
 b := ![[], [64, 21, 25], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [29, 64, 1, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11149, -48058, -24622, -68072, -34692]
  a := ![0, -2, -4, -10, -13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![65073, 53766, 59694, -68072, -34692]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 300763 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 0, -2, 8, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![-1, 0, -2, 8, 0]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![10, 17, 1, 0, 0], ![61, 21, 0, 1, 0], ![32, 9, 0, 0, 1]] where
  M :=![![![-1, 0, -2, 8, 0], ![0, -7, 0, -4, 16], ![48, 48, -7, -36, -24], ![-12, -4, 8, -3, -16], ![-18, -16, -6, 40, 13]]]
  hmulB := by decide  
  f := ![![![317, 32, -22, 0, -80]], ![![-240, 11, 32, 28, 80]], ![![-10, 9, 5, 8, 8]], ![![215, 33, -10, 9, -48]], ![![118, 17, -6, 4, -27]]]
  g := ![![![-7, -2, -2, 8, 0], ![-4, -1, 0, -4, 16], ![46, 17, -7, -36, -24], ![9, 1, 8, -3, -16], ![-42, -13, -6, 40, 13]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P1 : CertificateIrreducibleZModOfList' 67 2 2 6 [10, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [44, 66], [0, 1]]
 g := ![![[9, 47], [51, 62], [64], [56], [60], [1]], ![[0, 20], [32, 5], [64], [56], [60], [1]]]
 h' := ![![[44, 66], [26, 39], [31, 53], [66, 8], [36, 18], [57, 44], [0, 1]], ![[0, 1], [0, 28], [18, 14], [16, 59], [24, 49], [50, 23], [44, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40]]
 b := ![[], [29, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N1 : CertifiedPrimeIdeal' SI67N1 67 where
  n := 2
  hpos := by decide
  P := [10, 23, 1]
  hirr := P67P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![36172, 165912, 85036, 255486, 133496]
  a := ![3, -65, -62, -191, -186]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-308518, -117110, 85036, 255486, 133496]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N1 B_one_repr
lemma NI67N1 : Nat.card (O ⧸ I67N1) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![317, 32, -22, 0, -80]] ![![-1, 0, -2, 8, 0]]
  ![![67, 0, 0, 0, 0]] where
 M := ![![![67, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-131, -175, 77, -70, 110]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-131, -175, 77, -70, 110]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![0, 0, 0, 71, 0], ![64, 21, 22, 51, 1]] where
  M :=![![![-131, -175, 77, -70, 110], ![330, 430, -175, 172, -250], ![-750, -945, 430, -378, 594], ![132, 172, -70, 83, -100], ![-216, -275, 121, -110, 183]]]
  hmulB := by decide  
  f := ![![![11, 1, -1, 0, -2]], ![![-6, 2, 1, -2, 2]], ![![6, 3, 2, 0, -6]], ![![0, -2, 0, 5, 0]], ![![10, 1, 0, 3, -3]]]
  g := ![![![-101, -35, -33, -80, 110], ![230, 80, 75, 182, -250], ![-546, -189, -178, -432, 594], ![92, 32, 30, 73, -100], ![-168, -58, -55, -133, 183]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 4 2 6 [5, 56, 48, 17, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [58, 60, 51, 21], [25, 7, 41, 5], [42, 3, 50, 45], [0, 1]]
 g := ![![[31, 40, 53, 48], [52, 40, 0, 20], [23, 8, 47, 2], [34, 56, 5], [1], []], ![[14, 54, 3, 42, 12, 59], [27, 54, 46, 22, 29, 67], [55, 36, 42, 46, 28, 67], [0, 62, 50], [20, 45, 36], [12, 41, 15]], ![[56, 61, 32, 60, 23, 50], [54, 64, 12, 22, 55, 16], [66, 25, 7, 69, 64, 25], [39, 6, 3], [38, 17, 9], [25, 56, 25]], ![[66, 61, 45, 16, 37, 36], [48, 8, 67, 61, 25, 6], [1, 60, 22, 6, 40, 6], [48], [9, 30, 10], [10, 37, 37]]]
 h' := ![![[58, 60, 51, 21], [24, 31, 8, 41], [27, 30, 5, 34], [68, 9, 30, 12], [66, 15, 23, 54], [0, 0, 1], [0, 1]], ![[25, 7, 41, 5], [34, 11, 41, 18], [49, 22, 47, 26], [25, 19, 3, 45], [66, 31, 36, 60], [38, 48, 37, 6], [58, 60, 51, 21]], ![[42, 3, 50, 45], [63, 6, 13, 62], [44, 49, 36, 42], [48, 54, 0, 54], [32, 31, 53, 28], [3, 19, 52, 3], [25, 7, 41, 5]], ![[0, 1], [36, 23, 9, 21], [26, 41, 54, 40], [16, 60, 38, 31], [55, 65, 30], [10, 4, 52, 62], [42, 3, 50, 45]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [16, 42, 65], []]
 b := ![[], [], [65, 14, 5, 58], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 4
  hpos := by decide
  P := [5, 56, 48, 17, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2777059, 7040820, 2792824, 5637726, 2428986]
  a := ![1, -4, -4, -13, -13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2150395, -619266, -713308, -1665360, 2428986]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 25411681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 1, -1, 0, -2]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![11, 1, -1, 0, -2]] 
 ![![71, 0, 0, 0, 0], ![41, 1, 0, 0, 0], ![23, 0, 1, 0, 0], ![59, 0, 0, 1, 0], ![39, 0, 0, 0, 1]] where
  M :=![![![11, 1, -1, 0, -2], ![-6, 2, 1, -2, 2], ![6, 3, 2, 0, -6], ![0, -2, 0, 5, 0], ![0, 1, -1, 0, 5]]]
  hmulB := by decide  
  f := ![![![-131, -175, 77, -70, 110]], ![![-71, -95, 42, -38, 60]], ![![-53, -70, 31, -28, 44]], ![![-107, -143, 63, -57, 90]], ![![-75, -100, 44, -40, 63]]]
  g := ![![![1, 1, -1, 0, -2], ![-1, 2, 1, -2, 2], ![1, 3, 2, 0, -6], ![-3, -2, 0, 5, 0], ![-3, 1, -1, 0, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-131, -175, 77, -70, 110]] ![![11, 1, -1, 0, -2]]
  ![![71, 0, 0, 0, 0]] where
 M := ![![![71, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0)
instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 64, -28, 26, -40]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![59, 64, -28, 26, -40]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![0, 0, 73, 0, 0], ![36, 72, 40, 1, 0], ![42, 16, 34, 0, 1]] where
  M :=![![![59, 64, -28, 26, -40], ![-120, -145, 64, -62, 92], ![276, 348, -145, 138, -216], ![-48, -62, 26, -19, 36], ![78, 100, -44, 42, -55]]]
  hmulB := by decide  
  f := ![![![11, 4, 0, 2, 0]], ![![0, 11, 4, 2, 4]], ![![12, 24, 11, 18, 0]], ![![12, 26, 10, 13, 4]], ![![12, 16, 6, 10, 1]]]
  g := ![![![11, -16, 4, 26, -40], ![-24, 39, -8, -62, 92], ![60, -84, 23, 138, -216], ![-12, 10, -6, -19, 36], ![12, -28, 2, 42, -55]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [9, 69, 51, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [32, 55, 33], [63, 17, 40], [0, 1]]
 g := ![![[37, 50, 54], [59, 71], [64, 48], [30, 47, 18], [22, 1], []], ![[70, 60, 6, 40], [25, 64], [63, 23], [8, 23, 21, 43], [38, 70], [67, 67]], ![[13, 21, 22, 39], [27, 35], [64, 65], [21, 23, 65, 68], [24, 32], [60, 67]]]
 h' := ![![[32, 55, 33], [49, 24, 28], [54, 56, 12], [22, 65, 62], [21, 6, 50], [0, 0, 1], [0, 1]], ![[63, 17, 40], [49, 53, 27], [36, 55, 8], [26, 3, 60], [20, 2, 26], [56, 46, 17], [32, 55, 33]], ![[0, 1], [45, 69, 18], [54, 35, 53], [51, 5, 24], [7, 65, 70], [71, 27, 55], [63, 17, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27, 19], []]
 b := ![[], [70, 51, 68], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [9, 69, 51, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3668974, 12644010, 5889377, 15377602, 7556183]
  a := ![1, 18, 23, 62, 71]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-11880608, -16649894, -11864725, 15377602, 7556183]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 389017 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 4, 0, 2, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![11, 4, 0, 2, 0]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![12, 52, 1, 0, 0], ![42, 2, 0, 1, 0], ![40, 41, 0, 0, 1]] where
  M :=![![![11, 4, 0, 2, 0], ![0, 11, 4, 2, 4], ![12, 24, 11, 18, 0], ![0, 2, 2, 13, 4], ![6, 8, 0, 2, 9]]]
  hmulB := by decide  
  f := ![![![59, 64, -28, 26, -40]], ![![-120, -145, 64, -62, 92]], ![![-72, -88, 39, -38, 56]], ![![30, 32, -14, 13, -20]], ![![-34, -45, 20, -20, 29]]]
  g := ![![![-1, 0, 0, 2, 0], ![-4, -5, 4, 2, 4], ![-12, -8, 11, 18, 0], ![-10, -4, 2, 13, 4], ![-6, -5, 0, 2, 9]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P1 : CertificateIrreducibleZModOfList' 73 2 2 6 [40, 47, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [26, 72], [0, 1]]
 g := ![![[3, 72], [46], [50], [54, 35], [19], [1]], ![[50, 1], [46], [50], [15, 38], [19], [1]]]
 h' := ![![[26, 72], [10, 27], [68, 22], [30, 59], [37, 20], [33, 26], [0, 1]], ![[0, 1], [55, 46], [56, 51], [31, 14], [46, 53], [52, 47], [26, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43]]
 b := ![[], [49, 58]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N1 : CertifiedPrimeIdeal' SI73N1 73 where
  n := 2
  hpos := by decide
  P := [40, 47, 1]
  hirr := P73P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![18, 55, 5, 330, 408]
  a := ![-1, 2, -4, -5, -18]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-414, -241, 5, 330, 408]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N1 B_one_repr
lemma NI73N1 : Nat.card (O ⧸ I73N1) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![59, 64, -28, 26, -40]] ![![11, 4, 0, 2, 0]]
  ![![73, 0, 0, 0, 0]] where
 M := ![![![73, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0)
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-242, -15, 19, 9, 65]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![-242, -15, 19, 9, 65]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![0, 0, 79, 0, 0], ![26, 19, 47, 1, 0], ![34, 2, 74, 0, 1]] where
  M :=![![![-242, -15, 19, 9, 65], ![195, 10, -15, -7, -47], ![-141, 9, 10, -3, 33], ![-81, -7, 9, 2, 17], ![66, 2, -8, 10, -15]]]
  hmulB := by decide  
  f := ![![![4, 7, 1, 3, 1]], ![![3, 10, 7, 7, 5]], ![![15, 39, 10, 39, 9]], ![![11, 28, 8, 26, 7]], ![![16, 40, 10, 38, 9]]]
  g := ![![![-34, -4, -66, 9, 65], ![25, 3, 48, -7, -47], ![-15, 0, -29, -3, 33], ![-9, -1, -17, 2, 17], ![4, -2, 8, 10, -15]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [58, 29, 61, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [26, 23], [71, 55], [0, 1]]
 g := ![![[5], [65, 77, 20], [42, 41, 42], [33, 66, 46], [18, 1], []], ![[5], [24, 16, 73], [33, 62, 19], [60, 49, 2], [44, 23], []], ![[5], [18, 65, 65], [32, 55, 18], [0, 43, 31], [10, 55], []]]
 h' := ![![[26, 23], [22, 59], [13, 46, 39], [61, 7, 11], [62, 52, 58], [0, 0, 1], [0, 1]], ![[71, 55], [55, 14], [2, 65, 12], [16, 45, 52], [16, 17, 30], [44, 11, 55], [26, 23]], ![[0, 1], [24, 6], [8, 47, 28], [77, 27, 16], [40, 10, 70], [64, 68, 23], [71, 55]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47], []]
 b := ![[], [38, 40, 23], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [58, 29, 61, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-59894, -97270, 76860, -167466, 53300]
  a := ![0, -10, 4, -14, 12]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![31418, 37696, 50678, -167466, 53300]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 493039 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4, -7, -1, -3, -1]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![-4, -7, -1, -3, -1]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![18, 34, 1, 0, 0], ![56, 61, 0, 1, 0], ![55, 27, 0, 0, 1]] where
  M :=![![![-4, -7, -1, -3, -1], ![-3, -10, -7, -7, -5], ![-15, -39, -10, -39, -9], ![-3, -7, -3, -10, -9], ![-12, -16, -2, 0, -1]]]
  hmulB := by decide  
  f := ![![![242, 15, -19, -9, -65]], ![![-195, -10, 15, 7, 47]], ![![-27, -1, 2, 1, 5]], ![![22, 3, -2, -1, -10]], ![![101, 7, -8, -4, -29]]]
  g := ![![![3, 3, -1, -3, -1], ![10, 10, -7, -7, -5], ![36, 37, -10, -39, -9], ![14, 12, -3, -10, -9], ![1, 1, -2, 0, -1]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P1 : CertificateIrreducibleZModOfList' 79 2 2 6 [52, 74, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 78], [0, 1]]
 g := ![![[47, 38], [53, 21], [4, 64], [], [25], [1]], ![[0, 41], [0, 58], [8, 15], [], [25], [1]]]
 h' := ![![[5, 78], [9, 14], [29, 10], [0, 8], [61], [27, 5], [0, 1]], ![[0, 1], [0, 65], [0, 69], [40, 71], [61], [52, 74], [5, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [76]]
 b := ![[], [63, 38]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N1 : CertifiedPrimeIdeal' SI79N1 79 where
  n := 2
  hpos := by decide
  P := [52, 74, 1]
  hirr := P79P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1210, 193, -169, 111, -616]
  a := ![13, 0, -4, -8, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![404, 200, -169, 111, -616]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N1 B_one_repr
lemma NI79N1 : Nat.card (O ⧸ I79N1) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![-242, -15, 19, 9, 65]] ![![-4, -7, -1, -3, -1]]
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

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![50, 41, -7, -65, 17]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![50, 41, -7, -65, 17]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![0, 0, 83, 0, 0], ![0, 0, 0, 83, 0], ![42, 61, 24, 45, 1]] where
  M :=![![![50, 41, -7, -65, 17], ![51, 80, 41, -141, -147], ![-441, -267, 80, 399, -135], ![-93, -141, -65, 262, 229], ![390, 270, -38, -424, 33]]]
  hmulB := by decide  
  f := ![![![-8, -1, 3, 1, 5]], ![![15, 16, -1, 9, -3]], ![![-9, 3, 16, 9, 21]], ![![3, 9, 1, 6, 1]], ![![6, 17, 6, 13, 7]]]
  g := ![![![-8, -12, -5, -10, 17], ![75, 109, 43, 78, -147], ![63, 96, 40, 78, -135], ![-117, -170, -67, -121, 229], ![-12, -21, -10, -23, 33]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 4 2 6 [10, 66, 71, 17, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 75, 40, 15], [17, 53, 29, 72], [16, 37, 14, 79], [0, 1]]
 g := ![![[5, 12, 54, 27], [62, 34, 60, 7], [61, 23, 28], [5, 71, 48], [66, 1], []], ![[55, 23, 57, 17, 52, 50], [30, 24, 79, 10, 11, 24], [46, 76, 12], [75, 75, 81], [29, 22, 12, 26, 72, 45], [47, 31, 59]], ![[16, 72, 30, 80, 7, 24], [43, 18, 4, 77, 41, 6], [70, 5, 17], [24, 17, 78], [79, 26, 56, 28, 73, 73], [47, 44, 38]], ![[65, 3, 78, 31, 65, 14], [39, 46, 10, 77, 31, 60], [36, 71, 63], [27, 82, 4], [46, 43, 58, 15, 72, 6], [63, 31, 16]]]
 h' := ![![[33, 75, 40, 15], [44, 30, 80, 39], [48, 40, 80, 67], [49, 54, 48, 32], [4, 33, 62, 52], [0, 0, 1], [0, 1]], ![[17, 53, 29, 72], [53, 20, 70, 23], [71, 15, 58, 20], [45, 82, 82, 26], [52, 54, 53, 9], [38, 44, 51, 13], [33, 75, 40, 15]], ![[16, 37, 14, 79], [78, 44, 12, 32], [78, 43, 3, 16], [60, 4, 60, 73], [47, 24, 47, 24], [68, 3, 79, 4], [17, 53, 29, 72]], ![[0, 1], [36, 72, 4, 72], [55, 68, 25, 63], [0, 26, 59, 35], [42, 55, 4, 81], [41, 36, 35, 66], [16, 37, 14, 79]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [19, 6, 68], []]
 b := ![[], [], [67, 40, 65, 59], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 4
  hpos := by decide
  P := [10, 66, 71, 17, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![128228, 251383, 81834, 173255, 116684]
  a := ![-1, -4, -1, -8, -3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-57500, -82727, -32754, -61175, 116684]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 47458321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8, 1, -3, -1, -5]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![8, 1, -3, -1, -5]] 
 ![![83, 0, 0, 0, 0], ![77, 1, 0, 0, 0], ![47, 0, 1, 0, 0], ![50, 0, 0, 1, 0], ![42, 0, 0, 0, 1]] where
  M :=![![![8, 1, -3, -1, -5], ![-15, -16, 1, -9, 3], ![9, -3, -16, -9, -21], ![-3, -9, -1, -6, -1], ![0, 0, -4, -2, -5]]]
  hmulB := by decide  
  f := ![![![-50, -41, 7, 65, -17]], ![![-47, -39, 6, 62, -14]], ![![-23, -20, 3, 32, -8]], ![![-29, -23, 5, 36, -13]], ![![-30, -24, 4, 38, -9]]]
  g := ![![![4, 1, -3, -1, -5], ![18, -16, 1, -9, 3], ![28, -3, -16, -9, -21], ![13, -9, -1, -6, -1], ![6, 0, -4, -2, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![50, 41, -7, -65, 17]] ![![8, 1, -3, -1, -5]]
  ![![83, 0, 0, 0, 0]] where
 M := ![![![-83, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC83 : ContainsPrimesAboveP 83 ![I83N0, I83N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
    exact isPrimeI83N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 83 (by decide) (𝕀 ⊙ MulI83N0)
instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0, 0, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0, 0, 0]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![0, 0, 89, 0, 0], ![0, 0, 0, 89, 0], ![0, 0, 0, 0, 89]] where
  M :=![![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![0, 0, 89, 0, 0], ![0, 0, 0, 89, 0], ![0, 0, 0, 0, 89]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 5 2 6 [22, 60, 3, 17, 42, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 65, 14, 28, 86], [6, 67, 31, 41, 41], [71, 42, 22, 55, 29], [54, 3, 22, 54, 22], [0, 1]]
 g := ![![[20, 26, 71, 32, 5], [3, 71, 25, 25], [74, 68, 65, 69], [61, 0, 11, 53, 73], [1], []], ![[74, 34, 63, 27, 76, 83, 25, 86], [24, 41, 40, 67], [9, 38, 0, 72], [80, 50, 63, 22, 12, 75, 82, 41], [86, 5, 62, 68, 9, 18, 70, 14], [39, 72, 77, 9]], ![[32, 44, 41, 68, 68, 81, 21, 54], [68, 43, 18, 45], [86, 11, 81, 34], [6, 9, 15, 25, 26, 28, 46, 3], [42, 24, 14, 11, 29, 38, 51, 24], [19, 53, 44, 79]], ![[80, 18, 59, 28, 70, 51, 2, 6], [67, 18, 24, 11], [34, 21, 41, 55], [40, 35, 80, 50, 87, 18, 67, 3], [1, 61, 31, 21, 74, 19, 52, 60], [48, 9, 86, 40]], ![[51, 1, 4, 60, 24, 15, 11, 71], [54, 2, 87, 9], [13, 39, 3, 88], [45, 43, 12, 18, 9, 31, 42, 40], [46, 45, 86, 34, 82, 86, 66, 45], [18, 82, 26, 39]]]
 h' := ![![[5, 65, 14, 28, 86], [18, 69, 65, 86, 19], [23, 80, 87, 63, 5], [82, 28, 79, 68, 46], [67, 29, 86, 72, 47], [0, 0, 1], [0, 1]], ![[6, 67, 31, 41, 41], [24, 68, 49, 23, 88], [14, 67, 65, 6, 45], [52, 25, 69, 54, 28], [24, 30, 30, 77, 4], [57, 19, 14, 52, 84], [5, 65, 14, 28, 86]], ![[71, 42, 22, 55, 29], [12, 51, 10, 72, 30], [66, 27, 80, 2, 32], [0, 56, 69, 24, 37], [17, 8, 24, 54, 53], [63, 11, 33, 53, 20], [6, 67, 31, 41, 41]], ![[54, 3, 22, 54, 22], [39, 34, 80, 3, 13], [0, 38, 73, 51, 10], [83, 85, 81, 72, 12], [76, 38, 47, 44, 60], [69, 38, 87, 16, 34], [71, 42, 22, 55, 29]], ![[0, 1], [1, 45, 63, 83, 28], [78, 55, 51, 56, 86], [50, 73, 58, 49, 55], [28, 73, 80, 20, 14], [28, 21, 43, 57, 40], [54, 3, 22, 54, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62, 69, 52, 69], [], [], []]
 b := ![[], [30, 28, 30, 41, 23], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 5
  hpos := by decide
  P := [22, 60, 3, 17, 42, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-340233383, -314303055, 386159608, -56500849, 516575758]
  a := ![3, -4, 7, -1, 14]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3822847, -3531495, 4338872, -634841, 5804222]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 5584059449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def PBC89 : ContainsPrimesAboveP 89 ![I89N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![89, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 89 (by decide) 𝕀

instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 50, 6, -84, -30]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![53, 50, 6, -84, -30]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![0, 0, 97, 0, 0], ![22, 60, 32, 1, 0], ![11, 89, 46, 0, 1]] where
  M :=![![![53, 50, 6, -84, -30], ![-90, -19, 50, 12, -138], ![-414, -354, -19, 588, 162], ![126, 12, -84, 19, 238], ![294, 288, 48, -490, -219]]]
  hmulB := by decide  
  f := ![![![-79, -14, 14, 0, 30]], ![![90, 53, -14, 24, -30]], ![![-90, -42, 53, 0, 78]], ![![8, 16, 12, 15, 14]], ![![31, 27, 14, 22, 13]]]
  g := ![![![23, 80, 42, -84, -30], ![12, 119, 62, 12, -138], ![-156, -516, -271, 588, 162], ![-30, -230, -120, 19, 238], ![139, 507, 266, -490, -219]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [87, 24, 23, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [21, 65, 60], [53, 31, 37], [0, 1]]
 g := ![![[70, 59, 31], [84, 89], [55, 75], [84, 73], [92, 44], [1]], ![[19, 40, 90, 92], [34, 27], [94, 1], [43, 95], [50, 70], [38, 80, 60, 78]], ![[51, 5, 33, 45], [26, 22], [36, 73], [60, 88], [59, 18], [45, 8, 4, 19]]]
 h' := ![![[21, 65, 60], [66, 71, 15], [83, 30, 63], [42, 21, 47], [50, 80, 48], [10, 73, 74], [0, 1]], ![[53, 31, 37], [84, 26, 69], [36, 78, 67], [58, 10, 1], [4, 60, 80], [38, 38, 78], [21, 65, 60]], ![[0, 1], [4, 0, 13], [61, 86, 64], [34, 66, 49], [4, 54, 66], [44, 83, 42], [53, 31, 37]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51, 55], []]
 b := ![[], [89, 20, 88], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [87, 24, 23, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1215, 12266, 10344, 50720, 48800]
  a := ![1, 0, 3, 6, 13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-17025, -76022, -39768, 50720, 48800]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 912673 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-79, -14, 14, 0, 30]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![-79, -14, 14, 0, 30]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![35, 2, 1, 0, 0], ![53, 38, 0, 1, 0], ![36, 18, 0, 0, 1]] where
  M :=![![![-79, -14, 14, 0, 30], ![90, 53, -14, 24, -30], ![-90, -42, 53, 0, 78], ![-6, 24, 0, 15, 2], ![6, -12, 12, -2, 13]]]
  hmulB := by decide  
  f := ![![![53, 50, 6, -84, -30]], ![![-90, -19, 50, 12, -138]], ![![13, 14, 3, -24, -12]], ![![-5, 20, 22, -41, -68]], ![![6, 18, 12, -34, -39]]]
  g := ![![![-17, -6, 14, 0, 30], ![4, -3, -14, 24, -30], ![-49, -16, 53, 0, 78], ![-9, -6, 0, 15, 2], ![-8, -2, 12, -2, 13]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P1 : CertificateIrreducibleZModOfList' 97 2 2 6 [82, 80, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [17, 96], [0, 1]]
 g := ![![[27, 64], [3], [86], [9], [72], [17, 1]], ![[48, 33], [3], [86], [9], [72], [34, 96]]]
 h' := ![![[17, 96], [36, 89], [31, 10], [14, 59], [48, 94], [61, 13], [0, 1]], ![[0, 1], [94, 8], [7, 87], [47, 38], [94, 3], [88, 84], [17, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20]]
 b := ![[], [12, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N1 : CertifiedPrimeIdeal' SI97N1 97 where
  n := 2
  hpos := by decide
  P := [82, 80, 1]
  hirr := P97P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![406, 71, -75, 73, -158]
  a := ![4, 1, -1, 1, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![50, 3, -75, 73, -158]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N1 B_one_repr
lemma NI97N1 : Nat.card (O ⧸ I97N1) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![53, 50, 6, -84, -30]] ![![-79, -14, 14, 0, 30]]
  ![![97, 0, 0, 0, 0]] where
 M := ![![![97, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC97 : ContainsPrimesAboveP 97 ![I97N0, I97N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
    exact isPrimeI97N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 97 (by decide) (𝕀 ⊙ MulI97N0)
instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-208, -12, 18, 7, 57]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![-208, -12, 18, 7, 57]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![37, 21, 1, 0, 0], ![22, 51, 0, 1, 0], ![5, 56, 0, 0, 1]] where
  M :=![![![-208, -12, 18, 7, 57], ![171, 17, -12, 1, -43], ![-129, 6, 17, 15, 45], ![-63, 1, 7, 4, 19], ![60, 7, -3, 2, -15]]]
  hmulB := by decide  
  f := ![![![-14, -14, 10, -11, 3]], ![![9, 25, -14, 43, -25]], ![![-4, -1, 1, 5, -3]], ![![2, 10, -5, 19, -12]], ![![4, 13, -7, 23, -14]]]
  g := ![![![-13, -39, 18, 7, 57], ![8, 26, -12, 1, -43], ![-13, -36, 17, 15, 45], ![-5, -14, 7, 4, 19], ![2, 8, -3, 2, -15]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [57, 87, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [14, 100], [0, 1]]
 g := ![![[60, 1], [24], [93, 95], [14], [30], [14, 1]], ![[74, 100], [24], [9, 6], [14], [30], [28, 100]]]
 h' := ![![[14, 100], [23, 1], [52, 23], [46, 14], [6, 69], [10, 38], [0, 1]], ![[0, 1], [37, 100], [71, 78], [40, 87], [63, 32], [37, 63], [14, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38]]
 b := ![[], [69, 19]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [57, 87, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![163, 3115, 3203, 3578, 3694]
  a := ![7, 2, -22, -17, -40]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2134, -4490, 3203, 3578, 3694]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![74, 7, -7, -1, -21]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![74, 7, -7, -1, -21]] 
 ![![101, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![27, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![74, 7, -7, -1, -21], ![-63, -10, 7, -1, 19], ![57, 15, -10, 3, -21], ![21, -1, -1, -2, -5], ![-18, 2, 0, 2, 3]]]
  hmulB := by decide  
  f := ![![![4, 11, 9, -41, -47]], ![![-1, 0, 1, -3, -5]], ![![-1, -2, -1, 2, 2]], ![![3, 4, 2, -13, -12]], ![![0, 1, 1, -3, -4]]]
  g := ![![![1, 7, -7, -1, -21], ![0, -10, 7, -1, 19], ![-1, 15, -10, 3, -21], ![1, -1, -1, -2, -5], ![-1, 2, 0, 2, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 6, -8, -2, -26]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![97, 6, -8, -2, -26]] 
 ![![101, 0, 0, 0, 0], ![74, 1, 0, 0, 0], ![79, 0, 1, 0, 0], ![66, 0, 0, 1, 0], ![50, 0, 0, 0, 1]] where
  M :=![![![97, 6, -8, -2, -26], ![-78, -5, 6, 2, 22], ![66, 6, -5, -6, -18], ![30, 2, -2, -1, -10], ![-30, -4, 2, 4, 9]]]
  hmulB := by decide  
  f := ![![![-55, -94, 4, -62, 10]], ![![-40, -69, 2, -46, 6]], ![![-47, -80, 3, -52, 8]], ![![-36, -62, 2, -41, 6]], ![![-28, -48, 2, -32, 5]]]
  g := ![![![17, 6, -8, -2, -26], ![-14, -5, 6, 2, 22], ![13, 6, -5, -6, -18], ![6, 2, -2, -1, -10], ![-6, -4, 2, 4, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2

def I101N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8, 9, -5, 3, -7]] i)))

def SI101N3: IdealEqSpanCertificate' Table ![![8, 9, -5, 3, -7]] 
 ![![101, 0, 0, 0, 0], ![97, 1, 0, 0, 0], ![85, 0, 1, 0, 0], ![25, 0, 0, 1, 0], ![88, 0, 0, 0, 1]] where
  M :=![![![8, 9, -5, 3, -7], ![-21, -28, 9, -13, 13], ![39, 45, -28, 15, -39], ![-9, -13, 3, -6, 5], ![12, 14, -8, 4, -11]]]
  hmulB := by decide  
  f := ![![![238, 1, -25, 19, -53]], ![![227, 1, -24, 18, -50]], ![![203, 2, -21, 14, -46]], ![![59, 0, -6, 5, -14]], ![![206, 0, -22, 18, -45]]]
  g := ![![![1, 9, -5, 3, -7], ![11, -28, 9, -13, 13], ![11, 45, -28, 15, -39], ![7, -13, 3, -6, 5], ![2, 14, -8, 4, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N3 : Nat.card (O ⧸ I101N3) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N3)

lemma isPrimeI101N3 : Ideal.IsPrime I101N3 := prime_ideal_of_norm_prime hp101.out _ NI101N3
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![-208, -12, 18, 7, 57]] ![![74, 7, -7, -1, -21]]
  ![![-14489, -959, 1185, 374, 3898]] where
 M := ![![![-14489, -959, 1185, 374, 3898]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![-14489, -959, 1185, 374, 3898]] ![![97, 6, -8, -2, -26]]
  ![![-1358141, -89873, 111281, 35168, 365628]] where
 M := ![![![-1358141, -89873, 111281, 35168, 365628]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI101N2 : IdealMulLeCertificate' Table 
  ![![-1358141, -89873, 111281, 35168, 365628]] ![![8, 9, -5, 3, -7]]
  ![![101, 0, 0, 0, 0]] where
 M := ![![![-566812, -37572, 46460, 14645, 152611]]]
 hmul := by decide  
 g := ![![![![-5612, -372, 460, 145, 1511]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-49, -79, 33, -34, 44]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![-49, -79, 33, -34, 44]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![81, 32, 75, 1, 0], ![17, 44, 47, 0, 1]] where
  M :=![![![-49, -79, 33, -34, 44], ![132, 182, -79, 76, -112], ![-336, -441, 182, -174, 264], ![66, 76, -34, 27, -46], ![-102, -125, 55, -56, 73]]]
  hmulB := by decide  
  f := ![![![5, -3, -1, 0, -4]], ![![-12, -10, -3, 2, 4]], ![![12, -9, -10, -24, 0]], ![![9, -12, -9, -17, -2]], ![![1, -9, -6, -10, 1]]]
  g := ![![![19, -9, 5, -34, 44], ![-40, 26, -5, 76, -112], ![90, -63, 8, -174, 264], ![-13, 12, 1, 27, -46], ![31, -15, 8, -56, 73]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [86, 90, 53, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [83, 101, 84], [70, 1, 19], [0, 1]]
 g := ![![[17, 21, 46], [82, 56, 19], [15, 43, 34], [59, 30], [22, 28], [1]], ![[31, 5, 14, 75], [89, 50, 77, 73], [34, 100, 40, 94], [84, 8], [92, 81], [12, 78, 37, 42]], ![[16, 35, 98, 30], [39, 98, 55, 15], [48, 98, 23, 46], [93, 79], [1, 82], [33, 60, 13, 61]]]
 h' := ![![[83, 101, 84], [55, 93, 47], [49, 32, 15], [41, 45, 72], [45, 71, 37], [17, 13, 50], [0, 1]], ![[70, 1, 19], [50, 22, 31], [58, 101, 25], [52, 84, 41], [13, 59, 27], [32, 9, 9], [83, 101, 84]], ![[0, 1], [38, 91, 25], [81, 73, 63], [91, 77, 93], [63, 76, 39], [56, 81, 44], [70, 1, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13, 98], []]
 b := ![[], [61, 33, 16], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [86, 90, 53, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1576, -1502, 2124, 258, 3622]
  a := ![1, 2, -4, -1, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-816, -1642, -1820, 258, 3622]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 1092727 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-23, 10, -2, 6, 2]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![-23, 10, -2, 6, 2]] 
 ![![103, 0, 0, 0, 0], ![22, 1, 0, 0, 0], ![31, 0, 1, 0, 0], ![47, 0, 0, 1, 0], ![26, 0, 0, 0, 1]] where
  M :=![![![-23, 10, -2, 6, 2], ![6, -23, 10, -10, 10], ![30, 66, -23, 30, -30], ![-18, -10, 6, -3, 10], ![24, 20, -8, 8, -13]]]
  hmulB := by decide  
  f := ![![![-149, -102, 14, 166, -6]], ![![-32, -23, 2, 38, 2]], ![![-35, -24, 3, 40, 0]], ![![-67, -44, 8, 71, -8]], ![![-46, -32, 4, 52, -1]]]
  g := ![![![-5, 10, -2, 6, 2], ![4, -23, 10, -10, 10], ![-13, 66, -23, 30, -30], ![-1, -10, 6, -3, 10], ![-2, 20, -8, 8, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1

def I103N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 2, 0, 0, -2]] i)))

def SI103N2: IdealEqSpanCertificate' Table ![![1, 2, 0, 0, -2]] 
 ![![103, 0, 0, 0, 0], ![43, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![80, 0, 0, 1, 0], ![94, 0, 0, 0, 1]] where
  M :=![![![1, 2, 0, 0, -2], ![-6, -5, 2, 4, 2], ![6, 6, -5, 12, 6], ![6, 4, 0, -7, 2], ![0, 4, 2, -2, -9]]]
  hmulB := by decide  
  f := ![![![-2429, -154, 200, 68, 654]], ![![-995, -63, 82, 28, 268]], ![![-133, -8, 11, 4, 36]], ![![-1894, -120, 156, 53, 510]], ![![-2210, -140, 182, 62, 595]]]
  g := ![![![1, 2, 0, 0, -2], ![-3, -5, 2, 4, 2], ![-17, 6, -5, 12, 6], ![2, 4, 0, -7, 2], ![8, 4, 2, -2, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N2 : Nat.card (O ⧸ I103N2) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N2)

lemma isPrimeI103N2 : Ideal.IsPrime I103N2 := prime_ideal_of_norm_prime hp103.out _ NI103N2
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![-49, -79, 33, -34, 44]] ![![-23, 10, -2, 6, 2]]
  ![![3311, 4725, -2007, 1940, -2790]] where
 M := ![![![3311, 4725, -2007, 1940, -2790]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI103N1 : IdealMulLeCertificate' Table 
  ![![3311, 4725, -2007, 1940, -2790]] ![![1, 2, 0, 0, -2]]
  ![![103, 0, 0, 0, 0]] where
 M := ![![![-25441, -32445, 13905, -13184, 19776]]]
 hmul := by decide  
 g := ![![![![-247, -315, 135, -128, 192]]]]
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


lemma PB140I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 103 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 103 (by omega)

def PB140I2 : PrimesBelowBoundCertificateInterval O 61 103 140 where
  m := 9
  g := ![2, 2, 2, 2, 2, 1, 2, 4, 3]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103]
  hP := PB140I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1]
    · exact ![I79N0, I79N1]
    · exact ![I83N0, I83N1]
    · exact ![I89N0]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1, I101N2, I101N3]
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
    · exact ![300763, 4489]
    · exact ![25411681, 71]
    · exact ![389017, 5329]
    · exact ![493039, 6241]
    · exact ![47458321, 83]
    · exact ![5584059449]
    · exact ![912673, 9409]
    · exact ![10201, 101, 101, 101]
    · exact ![1092727, 103, 103]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
      exact NI83N1
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
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
      exact NI103N2
  β := ![I71N1, I83N1, I101N1, I101N2, I101N3, I103N1, I103N2]
  Il := ![[], [I71N1], [], [], [I83N1], [], [], [I101N1, I101N2, I101N3], [I103N1, I103N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
