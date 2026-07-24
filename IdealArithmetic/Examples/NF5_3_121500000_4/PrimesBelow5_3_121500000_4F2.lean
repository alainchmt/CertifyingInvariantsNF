
import IdealArithmetic.Examples.NF5_3_121500000_4.RI5_3_121500000_4
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9133, -4716, 2202, 2228, -3672]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![-9133, -4716, 2202, 2228, -3672]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![0, 0, 67, 0, 0], ![0, 0, 0, 67, 0], ![19, 65, 56, 58, 1]] where
  M :=![![![-9133, -4716, 2202, 2228, -3672], ![37380, 20217, -9172, -9624, 15720], ![-159768, -87928, 39465, 41968, -68328], ![328326, 182068, -81346, -87003, 141456], ![-63420, -35104, 15700, 16768, -27271]]]
  hmulB := by decide  
  f := ![![![89, 76, 14, -4, -24]], ![![300, 299, 84, -8, -120]], ![![1464, 1352, 315, -48, -456]], ![![2658, 2588, 682, -65, -912]], ![![3869, 3709, 946, -106, -1303]]]
  g := ![![![905, 3492, 3102, 3212, -3672], ![-3900, -14949, -13276, -13752, 15720], ![16992, 64976, 57699, 59776, -68328], ![-35214, -134516, -119446, -123753, 141456], ![6787, 25933, 23028, 23858, -27271]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 4 2 6 [27, 47, 6, 39, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [55, 50, 22, 50], [14, 66], [26, 17, 45, 17], [0, 1]]
 g := ![![[60, 0, 23, 10], [44, 14, 65, 10], [55, 34, 54], [40, 42, 47], [1], []], ![[66, 2, 57, 4, 61, 3], [12, 28, 36, 0, 6, 30], [65, 64, 10], [32, 49, 22], [51, 3, 29], [7, 41, 21]], ![[49, 42, 41, 57], [19, 58, 16, 57], [60, 62, 54], [58, 49, 47], [1], []], ![[27, 25, 47, 13, 3, 64], [20, 43, 28, 25, 29, 37], [40, 58, 10], [5, 5, 22], [15, 56, 29], [7, 41, 21]]]
 h' := ![![[55, 50, 22, 50], [18, 26, 20, 12], [44, 4, 62, 55], [51, 60, 55, 56], [40, 20, 61, 28], [0, 0, 1], [0, 1]], ![[14, 66], [30, 53, 62, 16], [2, 30, 44, 58], [22, 50, 58, 12], [45, 61, 10, 42], [22, 44, 39, 30], [55, 50, 22, 50]], ![[26, 17, 45, 17], [45, 63, 55, 55], [27, 23, 27, 12], [46, 44, 62, 11], [65, 32, 31, 39], [62, 39, 1], [14, 66]], ![[0, 1], [12, 59, 64, 51], [28, 10, 1, 9], [61, 47, 26, 55], [53, 21, 32, 25], [18, 51, 26, 37], [26, 17, 45, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [31], []]
 b := ![[], [], [36, 59, 43, 49], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 4
  hpos := by decide
  P := [27, 47, 6, 39, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-200199052496, -232994768284, -96875959844, -18208660580, 133390817072]
  a := ![17, 4, 8, 14, -68]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-40815292192, -132886535492, -112936742028, -115744418668, 133390817072]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 20151121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 76, 14, -4, -24]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![89, 76, 14, -4, -24]] 
 ![![67, 0, 0, 0, 0], ![38, 1, 0, 0, 0], ![30, 0, 1, 0, 0], ![14, 0, 0, 1, 0], ![62, 0, 0, 0, 1]] where
  M :=![![![89, 76, 14, -4, -24], ![300, 299, 84, -8, -120], ![1464, 1352, 315, -48, -456], ![2658, 2588, 682, -65, -912], ![1884, 1808, 460, -48, -613]]]
  hmulB := by decide  
  f := ![![![-9133, -4716, 2202, 2228, -3672]], ![![-4622, -2373, 1112, 1120, -1848]], ![![-6474, -3424, 1575, 1624, -2664]], ![![2992, 1732, -754, -833, 1344]], ![![-9398, -4888, 2272, 2312, -3805]]]
  g := ![![![-25, 76, 14, -4, -24], ![-90, 299, 84, -8, -120], ![-454, 1352, 315, -48, -456], ![-876, 2588, 682, -65, -912], ![-626, 1808, 460, -48, -613]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![-9133, -4716, 2202, 2228, -3672]] ![![89, 76, 14, -4, -24]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-254, -26, 40, 9, -35]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-254, -26, 40, 9, -35]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![0, 0, 0, 71, 0], ![60, 19, 9, 18, 1]] where
  M :=![![![-254, -26, 40, 9, -35], ![393, 57, -44, -17, 3], ![15, 342, 91, -31, -195], ![1020, 820, 224, -49, -480], ![719, 688, 154, -47, -330]]]
  hmulB := by decide  
  f := ![![![72, 40, -18, -19, 31]], ![![-315, -175, 78, 83, -135]], ![![1371, 760, -341, -363, 591]], ![![-2844, -1580, 704, 753, -1224]], ![![-563, -313, 139, 149, -242]]]
  g := ![![![26, 9, 5, 9, -35], ![3, 0, -1, -1, 3], ![165, 57, 26, 49, -195], ![420, 140, 64, 121, -480], ![289, 98, 44, 83, -330]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 4 2 6 [33, 37, 46, 29, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [48, 62, 50, 60], [28, 52, 3, 46], [37, 27, 18, 36], [0, 1]]
 g := ![![[5, 55, 61, 57], [68, 38, 47, 49], [11, 40, 36, 10], [8, 5, 60], [1], []], ![[44, 61, 4, 15, 55, 6], [26, 50, 20, 65, 35, 57], [26, 2, 30, 19, 56, 58], [27, 55, 2], [48, 7, 1], [11, 6, 50]], ![[54, 44, 10, 12, 42, 46], [40, 5, 53, 31, 2, 56], [56, 3, 68, 36, 9, 26], [34, 26, 48], [19, 1, 15], [1, 43, 57]], ![[47, 20, 7, 44, 58, 10], [0, 33, 15, 14, 5, 6], [59, 50, 53, 35, 31, 20], [41, 56, 27], [20, 61, 45], [10, 64, 18]]]
 h' := ![![[48, 62, 50, 60], [28, 57, 14, 46], [63, 67, 44, 7], [44, 64, 26, 9], [38, 34, 25, 42], [0, 0, 1], [0, 1]], ![[28, 52, 3, 46], [44, 11, 40, 63], [2, 12, 18, 18], [15, 29, 19, 13], [57, 43, 55, 12], [24, 22, 18, 1], [48, 62, 50, 60]], ![[37, 27, 18, 36], [23, 18, 9, 70], [21, 70, 16, 61], [64, 39, 16, 67], [60, 15, 26, 30], [41, 36, 64, 50], [28, 52, 3, 46]], ![[0, 1], [18, 56, 8, 34], [15, 64, 64, 56], [39, 10, 10, 53], [16, 50, 36, 58], [45, 13, 59, 20], [37, 27, 18, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [37, 63, 21], []]
 b := ![[], [], [68, 37, 38, 69], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 4
  hpos := by decide
  P := [33, 37, 46, 29, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1327689351839773, -1297574675403040, -349653548771661, 22310060383337, 463585872791338]
  a := ![113, -4, 57, 50, -449]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-410462559427043, -142333890963922, -63689104280193, -117214586617757, 463585872791338]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 25411681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-72, -40, 18, 19, -31]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![-72, -40, 18, 19, -31]] 
 ![![71, 0, 0, 0, 0], ![65, 1, 0, 0, 0], ![35, 0, 1, 0, 0], ![37, 0, 0, 1, 0], ![21, 0, 0, 0, 1]] where
  M :=![![![-72, -40, 18, 19, -31], ![315, 175, -78, -83, 135], ![-1371, -760, 341, 363, -591], ![2844, 1580, -704, -753, 1224], ![-545, -302, 136, 145, -236]]]
  hmulB := by decide  
  f := ![![![254, 26, -40, -9, 35]], ![![227, 23, -36, -8, 32]], ![![125, 8, -21, -4, 20]], ![![118, 2, -24, -4, 25]], ![![65, -2, -14, -2, 15]]]
  g := ![![![26, -40, 18, 19, -31], ![-114, 175, -78, -83, 135], ![494, -760, 341, 363, -591], ![-1029, 1580, -704, -753, 1224], ![196, -302, 136, 145, -236]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-254, -26, 40, 9, -35]] ![![-72, -40, 18, 19, -31]]
  ![![71, 0, 0, 0, 0]] where
 M := ![![![-71, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0, 0, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0, 0, 0]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![0, 0, 73, 0, 0], ![0, 0, 0, 73, 0], ![0, 0, 0, 0, 73]] where
  M :=![![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![0, 0, 73, 0, 0], ![0, 0, 0, 73, 0], ![0, 0, 0, 0, 73]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 5 2 6 [17, 30, 68, 24, 50, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 64, 47, 59, 8], [1, 23, 62, 16, 2], [21, 19, 7, 30, 39], [52, 39, 30, 41, 24], [0, 1]]
 g := ![![[3, 38, 44, 57, 9], [53, 72], [65, 0, 55, 19], [23, 45, 67, 23, 1], [], []], ![[48, 4, 50, 55, 24, 9, 61, 18], [58, 24, 63, 35], [43, 22, 34, 64], [65, 10, 70, 3, 63, 51, 36, 70], [10, 3, 39, 46], [40, 11, 7, 64]], ![[51, 71, 31, 57, 20, 13, 15, 61], [29, 43, 0, 41], [37, 61, 67, 70], [34, 50, 45, 64, 29, 13, 3, 3], [70, 45, 60, 71], [32, 54, 10, 4]], ![[4, 10, 60, 11, 12, 24, 26, 30], [3, 55, 58, 61], [52, 44, 16, 24], [11, 2, 19, 10, 23, 25, 2, 43], [22, 48, 27, 23], [67, 4, 20, 61]], ![[12, 53, 51, 16, 57, 47, 50, 65], [10, 57, 17, 38], [64, 63, 16, 19], [39, 19, 62, 48, 57, 22, 31, 50], [25, 26, 8, 18], [72, 34, 32, 65]]]
 h' := ![![[22, 64, 47, 59, 8], [56, 38, 37, 48, 3], [9, 53, 4, 46], [47, 5, 35, 46, 26], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[1, 23, 62, 16, 2], [40, 66, 63, 52, 38], [2, 6, 17, 7, 20], [52, 68, 61, 47, 8], [67, 48, 58, 2, 63], [23, 42, 2, 58, 51], [22, 64, 47, 59, 8]], ![[21, 19, 7, 30, 39], [42, 33, 30, 61, 33], [30, 54, 16, 32, 48], [41, 58, 59, 69, 56], [53, 65, 40, 3, 29], [41, 66, 45, 47, 12], [1, 23, 62, 16, 2]], ![[52, 39, 30, 41, 24], [57, 59, 21, 57, 42], [53, 24, 25, 50, 34], [39, 43, 33, 30, 30], [66, 43, 72, 56, 34], [32, 34, 19, 53, 60], [21, 19, 7, 30, 39]], ![[0, 1], [55, 23, 68, 1, 30], [15, 9, 11, 11, 44], [9, 45, 31, 27, 26], [48, 63, 49, 12, 19], [20, 4, 6, 61, 23], [52, 39, 30, 41, 24]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39, 34, 9, 5], [], [], []]
 b := ![[], [23, 4, 31, 19, 45], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 5
  hpos := by decide
  P := [17, 30, 68, 24, 50, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![18634516130323, 19850594237507, 6303570293197, 411348273342, -6574598847357]
  a := ![10, 1, 5, 6, -39]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![255267344251, 271925948459, 86350277989, 5634907854, -90062997909]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 2073071593 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def PBC73 : ContainsPrimesAboveP 73 ![I73N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![73, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 73 (by decide) 𝕀

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


def P79P0 : CertificateIrreducibleZModOfList' 79 5 2 6 [21, 4, 45, 70, 59, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 63, 63, 37], [47, 0, 9, 8, 67], [75, 43, 43, 62, 65], [49, 51, 43, 51, 26], [0, 1]]
 g := ![![[26, 23, 44, 29, 67], [69, 72, 21, 52, 23], [72, 50, 8, 10, 44], [17, 20, 14, 20, 1], [], []], ![[24, 55, 68, 47, 54, 1, 7], [5, 41, 61, 64, 49, 74, 53], [35, 30, 0, 54, 37, 13, 69], [12, 61, 67, 24, 8, 44, 17], [55, 36, 78, 2], [47, 26]], ![[43, 61, 45, 40, 51, 32, 8, 72], [61, 28, 29, 13, 76, 43, 41, 36], [43, 40, 45, 52, 76, 42, 34, 40], [70, 68, 19, 37, 64, 58, 66, 52], [28, 1, 49, 73], [61, 78, 2, 65]], ![[15, 40, 29, 10, 72, 40, 33, 62], [18, 49, 71, 44, 14, 66, 72, 76], [27, 43, 75, 17, 74, 54, 60, 42], [41, 16, 29, 35, 70, 12, 39, 45], [54, 52, 67, 49], [46, 52, 51, 38]], ![[19, 30, 77, 39, 72, 1, 6, 23], [4, 73, 14, 19, 44, 14, 37, 1], [44, 51, 36, 25, 55, 22, 62, 42], [71, 35, 65, 57, 24, 3, 5, 1], [6, 73, 22, 44], [60, 33, 56, 44]]]
 h' := ![![[7, 63, 63, 37], [52, 71, 75, 20, 64], [68, 27, 68, 31, 24], [38, 65, 46, 41, 26], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[47, 0, 9, 8, 67], [13, 43, 18, 56, 48], [46, 28, 67, 33, 11], [22, 58, 68, 75, 2], [51, 9, 56, 47, 3], [10, 69, 25, 46, 9], [7, 63, 63, 37]], ![[75, 43, 43, 62, 65], [77, 66, 34, 76, 51], [9, 64, 13, 19, 47], [66, 67, 7, 48, 55], [49, 18, 17, 69, 38], [59, 14, 38, 52, 51], [47, 0, 9, 8, 67]], ![[49, 51, 43, 51, 26], [15, 49, 37, 43, 17], [44, 29, 75, 30, 29], [74, 9, 67, 22, 32], [55, 37, 33, 46, 5], [77, 39, 52, 37, 72], [75, 43, 43, 62, 65]], ![[0, 1], [68, 8, 73, 42, 57], [75, 10, 14, 45, 47], [41, 38, 49, 51, 43], [72, 15, 52, 75, 32], [35, 36, 42, 23, 26], [49, 51, 43, 51, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [64, 56, 68], [], [], []]
 b := ![[], [0, 55, 73, 9, 43], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 5
  hpos := by decide
  P := [21, 4, 45, 70, 59, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-151654088805913997, -168553181568685674, -59763174837886362, -7467910208137198, 66327345714527488]
  a := ![-61, -8, -30, -43, 245]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1919672010201443, -2133584576818806, -756495884023878, -94530508963762, 839586654614272]
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

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0, 0, 0]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0, 0, 0]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![0, 0, 83, 0, 0], ![0, 0, 0, 83, 0], ![0, 0, 0, 0, 83]] where
  M :=![![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![0, 0, 83, 0, 0], ![0, 0, 0, 83, 0], ![0, 0, 0, 0, 83]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 5 2 6 [24, 59, 41, 28, 9, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [82, 15, 11, 4, 5], [11, 20, 82, 50, 77], [33, 62, 29, 12, 29], [31, 68, 44, 17, 55], [0, 1]]
 g := ![![[45, 5, 79, 37, 29], [40, 46, 71, 22, 68], [64, 59, 71, 10], [55, 34, 24, 81], [1], []], ![[1, 13, 62, 59, 76, 31, 33, 45], [20, 73, 66, 39, 17, 67, 81, 67], [10, 2, 53, 28], [50, 52, 63, 17], [11, 4, 63, 77, 58, 24, 54, 58], [52, 12, 64, 25]], ![[52, 67, 71, 26, 81, 3, 3, 59], [27, 52, 80, 11, 79, 26, 52, 81], [27, 19, 30, 48], [67, 43, 23, 21], [17, 47, 12, 14, 10, 47, 68, 28], [1, 26, 72, 36]], ![[22, 70, 21, 49, 58, 37, 38, 16], [2, 71, 21, 66, 65, 31, 67, 26], [52, 65, 57, 16], [45, 42, 17, 12], [68, 57, 78, 28, 21, 42, 79, 26], [74, 46, 16, 11]], ![[74, 54, 55, 15, 82, 47, 13, 35], [67, 65, 59, 45, 20, 48, 77, 79], [17, 19, 74, 12], [61, 28, 2, 16], [12, 65, 49, 58, 41, 57, 57, 50], [42, 54, 43, 37]]]
 h' := ![![[82, 15, 11, 4, 5], [36, 32, 21, 14, 64], [50, 50, 20, 63, 63], [3, 16, 31, 54, 33], [59, 24, 42, 55, 74], [0, 0, 1], [0, 1]], ![[11, 20, 82, 50, 77], [52, 71, 61, 30, 3], [7, 4, 82, 23, 14], [74, 75, 65, 51, 51], [64, 47, 13, 39, 73], [81, 17, 60, 57, 59], [82, 15, 11, 4, 5]], ![[33, 62, 29, 12, 29], [46, 27, 39, 76, 2], [52, 60, 38, 28, 51], [77, 11, 31, 22, 52], [5, 68, 33, 37, 41], [14, 6, 63, 0, 40], [11, 20, 82, 50, 77]], ![[31, 68, 44, 17, 55], [39, 44, 33, 62, 26], [48, 44, 35, 41, 12], [36, 28, 20, 77, 4], [55, 66, 30, 79, 57], [60, 33, 41, 52, 71], [33, 62, 29, 12, 29]], ![[0, 1], [63, 75, 12, 67, 71], [24, 8, 74, 11, 26], [10, 36, 19, 45, 26], [48, 44, 48, 39, 4], [36, 27, 1, 57, 79], [31, 68, 44, 17, 55]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66, 46, 82, 19], [], [], []]
 b := ![[], [6, 19, 1, 62, 46], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 5
  hpos := by decide
  P := [24, 59, 41, 28, 9, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2404552412659949, -913335659121400, 1070524442033574, 872432701237647, -1627734982929891]
  a := ![29, 11, 15, 32, -117]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-28970510995903, -11004044085800, 12897884843778, 10511237364309, -19611264854577]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![772, 302, -190, -87, 183]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![772, 302, -190, -87, 183]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![0, 0, 89, 0, 0], ![0, 0, 0, 89, 0], ![12, 7, 51, 36, 1]] where
  M :=![![![772, 302, -190, -87, 183], ![-1935, -795, 476, 247, -495], ![5199, 2254, -1289, -779, 1479], ![-6738, -3174, 1668, 1235, -2208], ![1113, 538, -276, -221, 382]]]
  hmulB := by decide  
  f := ![![![14, 0, -4, -1, 3]], ![![-33, -13, 2, 1, -3]], ![![33, -8, -15, -5, 3]], ![![6, 6, 0, -5, -24]], ![![21, -3, -9, -5, -8]]]
  g := ![![![-16, -11, -107, -75, 183], ![45, 30, 289, 203, -495], ![-141, -91, -862, -607, 1479], ![222, 138, 1284, 907, -2208], ![-39, -24, -222, -157, 382]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 4 2 6 [45, 79, 12, 82, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 46, 1], [70, 2, 22, 10], [22, 40, 66, 79], [0, 1]]
 g := ![![[81, 87, 42, 32], [41, 55, 81], [67, 34, 25], [76, 67, 13, 34], [7, 1], []], ![[80, 47, 5, 45, 16], [16, 43, 9], [72, 22, 32], [61, 0, 35, 44, 32], [1, 52, 39, 14, 11], [1]], ![[78, 73, 36, 86, 32, 80], [16, 71, 69], [67, 34, 25], [7, 38, 36, 64, 61, 32], [8, 82, 50, 62, 60, 20], [6, 72, 11]], ![[11, 35, 39, 31, 72, 84], [80, 25, 71], [72, 22, 32], [61, 61, 79, 29, 6, 64], [77, 5, 32, 74, 53, 64], [63, 3, 11]]]
 h' := ![![[4, 46, 1], [6, 40, 73, 78], [31, 44, 68, 80], [51, 49, 66, 5], [41, 25, 15, 37], [0, 0, 1], [0, 1]], ![[70, 2, 22, 10], [61, 84, 22, 4], [43, 33, 33, 86], [48, 56, 7, 11], [26, 13, 22, 11], [60, 22, 65, 10], [4, 46, 1]], ![[22, 40, 66, 79], [63, 4, 42, 39], [58, 73, 78, 43], [15, 40, 23, 84], [9, 83, 65, 56], [2, 37, 33, 64], [70, 2, 22, 10]], ![[0, 1], [45, 50, 41, 57], [21, 28, 88, 58], [18, 33, 82, 78], [42, 57, 76, 74], [52, 30, 79, 15], [22, 40, 66, 79]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [15, 53, 84], []]
 b := ![[], [], [87, 66, 88, 45], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 4
  hpos := by decide
  P := [45, 79, 12, 82, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2023485789231, 1125356741792, -501555481928, -538154896394, 874096518456]
  a := ![-18, -16, -8, -38, 72]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-95119914969, -56104706600, -506522223856, -359613815290, 874096518456]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 62742241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14, 0, -4, -1, 3]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![14, 0, -4, -1, 3]] 
 ![![89, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![78, 0, 1, 0, 0], ![50, 0, 0, 1, 0], ![66, 0, 0, 0, 1]] where
  M :=![![![14, 0, -4, -1, 3], ![-33, -13, 2, 1, -3], ![33, -8, -15, -5, 3], ![6, 6, 0, -5, -24], ![33, 16, -2, -5, -16]]]
  hmulB := by decide  
  f := ![![![772, 302, -190, -87, 183]], ![![65, 25, -16, -7, 15]], ![![735, 290, -181, -85, 177]], ![![358, 134, -88, -35, 78]], ![![585, 230, -144, -67, 140]]]
  g := ![![![2, 0, -4, -1, 3], ![1, -13, 2, 1, -3], ![15, -8, -15, -5, 3], ![20, 6, 0, -5, -24], ![15, 16, -2, -5, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![772, 302, -190, -87, 183]] ![![14, 0, -4, -1, 3]]
  ![![89, 0, 0, 0, 0]] where
 M := ![![![89, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0)
instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-470, -171, 123, 45, -107]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![-470, -171, 123, 45, -107]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![0, 0, 97, 0, 0], ![33, 60, 10, 1, 0], ![50, 64, 23, 0, 1]] where
  M :=![![![-470, -171, 123, 45, -107], ![1149, 464, -261, -103, 219], ![-2319, -761, 670, 225, -579], ![2562, 1147, -475, -195, 372], ![-91, 98, 130, 23, -114]]]
  hmulB := by decide  
  f := ![![![-2238, -389, 407, 121, -319]], ![![3465, 600, -631, -187, 495]], ![![-5379, -939, 974, 289, -759]], ![![852, 146, -156, -46, 123]], ![![-152, -29, 26, 8, -19]]]
  g := ![![![35, 41, 22, 45, -107], ![-66, -76, -44, -103, 219], ![198, 235, 121, 225, -579], ![-99, -113, -73, -195, 372], ![50, 62, 26, 23, -114]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [36, 3, 33, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [66, 21, 41], [95, 75, 56], [0, 1]]
 g := ![![[79, 17, 65], [42, 70], [45, 50], [80, 85], [54, 22], [1]], ![[43, 57, 43, 45], [57, 1], [76, 72], [56, 94], [78, 53], [47, 64, 42, 51]], ![[75, 52, 60, 67], [10, 12], [36, 2], [94, 70], [96, 47], [93, 79, 56, 46]]]
 h' := ![![[66, 21, 41], [71, 43, 68], [82, 30, 78], [21, 26, 27], [31, 38, 52], [61, 94, 64], [0, 1]], ![[95, 75, 56], [74, 31, 73], [34, 52, 96], [65, 40, 84], [23, 57, 26], [42, 92, 21], [66, 21, 41]], ![[0, 1], [28, 23, 53], [0, 15, 20], [36, 31, 83], [5, 2, 19], [39, 8, 12], [95, 75, 56]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26, 23], []]
 b := ![[], [2, 18, 16], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [36, 3, 33, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-304168952, -277944962, -64169679, 13482548, 108193566]
  a := ![-3, 8, -1, 11, 25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-63492488, -82590578, -27705641, 13482548, 108193566]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 912673 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-55, -15, 11, 6, -12]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![-55, -15, 11, 6, -12]] 
 ![![97, 0, 0, 0, 0], ![15, 1, 0, 0, 0], ![66, 0, 1, 0, 0], ![31, 0, 0, 1, 0], ![78, 0, 0, 0, 1]] where
  M :=![![![-55, -15, 11, 6, -12], ![126, 46, -27, -20, 36], ![-372, -169, 86, 78, -132], ![612, 323, -149, -153, 252], ![-126, -64, 30, 30, -49]]]
  hmulB := by decide  
  f := ![![![-769, -267, 209, 76, -180]], ![![-99, -33, 28, 10, -24]], ![![-564, -195, 154, 56, -132]], ![![-205, -68, 58, 21, -48]], ![![-624, -216, 170, 62, -145]]]
  g := ![![![2, -15, 11, 6, -12], ![-10, 46, -27, -20, 36], ![45, -169, 86, 78, -132], ![-96, 323, -149, -153, 252], ![18, -64, 30, 30, -49]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1

def I97N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-132, -22, 24, 7, -19]] i)))

def SI97N2: IdealEqSpanCertificate' Table ![![-132, -22, 24, 7, -19]] 
 ![![97, 0, 0, 0, 0], ![62, 1, 0, 0, 0], ![36, 0, 1, 0, 0], ![17, 0, 0, 1, 0], ![89, 0, 0, 0, 1]] where
  M :=![![![-132, -22, 24, 7, -19], ![207, 37, -36, -11, 27], ![-291, -34, 59, 15, -51], ![180, 62, -14, -9, 0], ![-17, 22, 16, 1, -20]]]
  hmulB := by decide  
  f := ![![![430, 220, -110, -99, 169]], ![![257, 131, -66, -59, 101]], ![![231, 120, -59, -55, 93]], ![![-70, -42, 16, 20, -31]], ![![421, 216, -108, -98, 167]]]
  g := ![![![20, -22, 24, 7, -19], ![-31, 37, -36, -11, 27], ![41, -34, 59, 15, -51], ![-31, 62, -14, -9, 0], ![-2, 22, 16, 1, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N2 : Nat.card (O ⧸ I97N2) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N2)

lemma isPrimeI97N2 : Ideal.IsPrime I97N2 := prime_ideal_of_norm_prime hp97.out _ NI97N2
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![-470, -171, 123, 45, -107]] ![![-55, -15, 11, 6, -12]]
  ![![-430, -220, 110, 99, -169]] where
 M := ![![![-430, -220, 110, 99, -169]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI97N1 : IdealMulLeCertificate' Table 
  ![![-430, -220, 110, 99, -169]] ![![-132, -22, 24, 7, -19]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-117, -50, 30, 12, -26]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![-117, -50, 30, 12, -26]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![38, 12, 1, 0, 0], ![75, 99, 0, 1, 0], ![48, 77, 0, 0, 1]] where
  M :=![![![-117, -50, 30, 12, -26], ![276, 109, -74, -28, 66], ![-708, -298, 165, 68, -138], ![588, 192, -180, -61, 168], ![-130, -78, 10, 10, -1]]]
  hmulB := by decide  
  f := ![![![-5, -10, 6, 8, -14]], ![![144, 105, -26, -40, 54]], ![![10, 6, 1, 0, -2]], ![![153, 105, -24, -37, 48]], ![![106, 75, -16, -26, 33]]]
  g := ![![![-9, 4, 30, 12, -26], ![20, -13, -74, -28, 66], ![-54, 16, 165, 68, -138], ![39, -45, -180, -61, 168], ![-12, -11, 10, 10, -1]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [80, 90, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 100], [0, 1]]
 g := ![![[39, 24], [16], [55, 52], [30], [65], [11, 1]], ![[0, 77], [16], [21, 49], [30], [65], [22, 100]]]
 h' := ![![[11, 100], [50, 23], [44, 4], [78, 31], [85, 63], [29, 41], [0, 1]], ![[0, 1], [0, 78], [88, 97], [15, 70], [71, 38], [76, 60], [11, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66]]
 b := ![[], [71, 33]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [80, 90, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5136, 1550, -3278, -3440, 7530]
  a := ![-1, -4, 0, -7, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![260, -1964, -3278, -3440, 7530]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-105, -104, -28, 2, 34]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![-105, -104, -28, 2, 34]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![4, 54, 1, 0, 0], ![94, 9, 0, 1, 0], ![63, 29, 0, 0, 1]] where
  M :=![![![-105, -104, -28, 2, 34], ![-414, -407, -108, 6, 126], ![-1530, -1536, -419, 18, 450], ![-2520, -2580, -732, 1, 720], ![-1666, -1712, -484, 2, 455]]]
  hmulB := by decide  
  f := ![![![20959, 3664, -3820, -1138, 2998]], ![![-32562, -5707, 5940, 1770, -4662]], ![![-16078, -2818, 2933, 874, -2302]], ![![16376, 2861, -2984, -889, 2342]], ![![3805, 661, -692, -206, 543]]]
  g := ![![![-23, 4, -28, 2, 34], ![-84, 17, -108, 6, 126], ![-296, 78, -419, 18, 450], ![-446, 159, -732, 1, 720], ![-283, 111, -484, 2, 455]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P1 : CertificateIrreducibleZModOfList' 101 2 2 6 [11, 42, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [59, 100], [0, 1]]
 g := ![![[13, 81], [20], [52, 71], [47], [84], [59, 1]], ![[45, 20], [20], [100, 30], [47], [84], [17, 100]]]
 h' := ![![[59, 100], [27, 9], [34, 11], [42, 77], [16, 42], [58, 36], [0, 1]], ![[0, 1], [53, 92], [77, 90], [40, 24], [70, 59], [61, 65], [59, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66]]
 b := ![[], [87, 33]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N1 : CertifiedPrimeIdeal' SI101N1 101 where
  n := 2
  hpos := by decide
  P := [11, 42, 1]
  hirr := P101P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11009, -134289, -198882, -106575, 376020]
  a := ![-27, -11, -10, -32, 111]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-127373, 6534, -198882, -106575, 376020]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N1 B_one_repr
lemma NI101N1 : Nat.card (O ⧸ I101N1) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2229, -390, 406, 122, -320]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![-2229, -390, 406, 122, -320]] 
 ![![101, 0, 0, 0, 0], ![35, 1, 0, 0, 0], ![88, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![97, 0, 0, 0, 1]] where
  M :=![![![-2229, -390, 406, 122, -320], ![3474, 615, -634, -194, 504], ![-5466, -998, 1003, 322, -816], ![2676, 564, -504, -199, 456], ![-916, -178, 170, 60, -145]]]
  hmulB := by decide  
  f := ![![![-161, 10, 94, 34, -32]], ![![-53, 5, 32, 12, -8]], ![![-178, -14, 83, 34, -16]], ![![-92, -68, -8, 9, 40]], ![![-225, -48, 80, 38, -1]]]
  g := ![![![57, -390, 406, 122, -320], ![-95, 615, -634, -194, 504], ![176, -998, 1003, 322, -816], ![-152, 564, -504, -199, 456], ![39, -178, 170, 60, -145]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![-117, -50, 30, 12, -26]] ![![-105, -104, -28, 2, 34]]
  ![![161, -10, -94, -34, 32]] where
 M := ![![![161, -10, -94, -34, 32]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![161, -10, -94, -34, 32]] ![![-2229, -390, 406, 122, -320]]
  ![![101, 0, 0, 0, 0]] where
 M := ![![![-101, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC101 : ContainsPrimesAboveP 101 ![I101N0, I101N1, I101N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
    exact isPrimeI101N1
    exact isPrimeI101N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 101 (by decide) (𝕀 ⊙ MulI101N0 ⊙ MulI101N1)
instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-16283, -4334, 3446, 1178, -2850]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![-16283, -4334, 3446, 1178, -2850]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![2, 65, 11, 1, 0], ![91, 44, 5, 0, 1]] where
  M :=![![![-16283, -4334, 3446, 1178, -2850], ![30666, 8785, -6690, -2342, 5586], ![-60006, -18370, 13469, 4818, -11346], ![45516, 15314, -10658, -3933, 9096], ![-8250, -2416, 1816, 642, -1523]]]
  hmulB := by decide  
  f := ![![![-161, -182, -58, -6, 30]], ![![-342, -453, -170, -38, 18]], ![![-102, -618, -377, -190, -402]], ![![-202, -339, -149, -49, -48]], ![![-269, -368, -141, -34, 1]]]
  g := ![![![2337, 432, 46, 1178, -2850], ![-4592, -823, -86, -2342, 5586], ![9348, 1628, 167, 4818, -11346], ![-7518, -1255, -125, -3933, 9096], ![1253, 222, 23, 642, -1523]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [33, 23, 52, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [91, 22, 26], [63, 80, 77], [0, 1]]
 g := ![![[94, 22, 32], [64, 65, 34], [22, 95, 4], [1, 33], [10, 26], [1]], ![[102, 84, 4, 23], [28, 1, 70, 72], [1, 97, 2, 81], [22, 34], [80, 91], [17, 61, 87, 66]], ![[58, 1, 67, 90], [69, 25, 30, 35], [0, 31, 31, 3], [30, 34], [80, 34], [76, 34, 48, 37]]]
 h' := ![![[91, 22, 26], [51, 13, 49], [98, 101, 31], [72, 50, 2], [38, 18, 62], [70, 80, 51], [0, 1]], ![[63, 80, 77], [7, 0, 35], [31, 21, 59], [21, 31, 18], [52, 11, 72], [80, 96, 83], [91, 22, 26]], ![[0, 1], [87, 90, 19], [61, 84, 13], [58, 22, 83], [11, 74, 72], [30, 30, 72], [63, 80, 77]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [82, 73], []]
 b := ![[], [28, 55, 17], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [33, 23, 52, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-124918030, -198384974, -130420214, -45287027, 209148029]
  a := ![-19, -6, -10, -19, 77]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-185114705, -62691665, -6582554, -45287027, 209148029]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 1092727 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-428, -89, 83, 25, -65]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![-428, -89, 83, 25, -65]] 
 ![![103, 0, 0, 0, 0], ![27, 1, 0, 0, 0], ![95, 0, 1, 0, 0], ![43, 0, 0, 1, 0], ![52, 0, 0, 0, 1]] where
  M :=![![![-428, -89, 83, 25, -65], ![705, 150, -139, -39, 105], ![-1143, -235, 228, 49, -153], ![492, 55, -97, 21, 12], ![-133, -12, 24, -3, -6]]]
  hmulB := by decide  
  f := ![![![-1752, -1761, -483, 15, 509]], ![![-519, -523, -144, 4, 150]], ![![-1815, -1834, -507, 12, 520]], ![![-1002, -1036, -296, -2, 269]], ![![-1049, -1076, -304, 1, 288]]]
  g := ![![![-35, -89, 83, 25, -65], ![59, 150, -139, -39, 105], ![-103, -235, 228, 49, -153], ![65, 55, -97, 21, 12], ![-16, -12, 24, -3, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1

def I103N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-179, -33, 33, 10, -26]] i)))

def SI103N2: IdealEqSpanCertificate' Table ![![-179, -33, 33, 10, -26]] 
 ![![103, 0, 0, 0, 0], ![54, 1, 0, 0, 0], ![71, 0, 1, 0, 0], ![13, 0, 0, 1, 0], ![81, 0, 0, 0, 1]] where
  M :=![![![-179, -33, 33, 10, -26], ![282, 52, -53, -16, 42], ![-456, -91, 84, 26, -66], ![216, 39, -45, -13, 36], ![-76, -18, 12, 4, -9]]]
  hmulB := by decide  
  f := ![![![9, 21, 9, -4, -10]], ![![6, 12, 5, -2, -6]], ![![15, 22, 7, -4, -8]], ![![9, 12, 6, 1, -10]], ![![19, 27, 9, -4, -11]]]
  g := ![![![12, -33, 33, 10, -26], ![-19, 52, -53, -16, 42], ![34, -91, 84, 26, -66], ![-14, 39, -45, -13, 36], ![7, -18, 12, 4, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N2 : Nat.card (O ⧸ I103N2) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N2)

lemma isPrimeI103N2 : Ideal.IsPrime I103N2 := prime_ideal_of_norm_prime hp103.out _ NI103N2
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![-16283, -4334, 3446, 1178, -2850]] ![![-428, -89, 83, 25, -65]]
  ![![933502, 88267, -146041, -35907, 107323]] where
 M := ![![![933502, 88267, -146041, -35907, 107323]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI103N1 : IdealMulLeCertificate' Table 
  ![![933502, 88267, -146041, -35907, 107323]] ![![-179, -33, 33, 10, -26]]
  ![![103, 0, 0, 0, 0]] where
 M := ![![![-91523328, -16258138, 16763662, 5021765, -13183691]]]
 hmul := by decide  
 g := ![![![![-888576, -157846, 162754, 48755, -127997]]]]
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


lemma PB539I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 103 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 103 (by omega)

def PB539I2 : PrimesBelowBoundCertificateInterval O 61 103 539 where
  m := 9
  g := ![2, 2, 1, 1, 1, 2, 3, 3, 3]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103]
  hP := PB539I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1]
    · exact ![I73N0]
    · exact ![I79N0]
    · exact ![I83N0]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1, I97N2]
    · exact ![I101N0, I101N1, I101N2]
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
    · exact ![20151121, 67]
    · exact ![25411681, 71]
    · exact ![2073071593]
    · exact ![3077056399]
    · exact ![3939040643]
    · exact ![62742241, 89]
    · exact ![912673, 97, 97]
    · exact ![10201, 10201, 101]
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
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
      exact NI103N2
  β := ![I67N1, I71N1, I89N1, I97N1, I97N2, I101N2, I103N1, I103N2]
  Il := ![[I67N1], [I71N1], [], [], [], [I89N1], [I97N1, I97N2], [I101N2], [I103N1, I103N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
