
import IdealArithmetic.Examples.NF5_1_40500000_1.RI5_1_40500000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![18, -33, -20, -14, 109]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![18, -33, -20, -14, 109]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![0, 0, 67, 0, 0], ![24, 25, 22, 1, 0], ![18, 57, 26, 0, 1]] where
  M :=![![![18, -33, -20, -14, 109], ![299, -96, 118, -24, -439], ![-1365, 865, -463, 230, 1125], ![234, -297, 71, -157, 66], ![-656, 510, -180, 198, 243]]]
  hmulB := by decide  
  f := ![![![-46692, -13383, 6276, -18858, -27167]], ![![-119217, -34170, 16024, -48148, -69363]], ![![-304385, -87245, 40911, -122930, -177095]], ![![-161427, -46269, 21697, -65195, -93921]], ![![-233379, -66892, 31368, -94254, -135784]]]
  g := ![![![-24, -88, -38, -14, 109], ![131, 381, 180, -24, -439], ![-405, -1030, -519, 230, 1125], ![42, -2, 27, -157, 66], ![-146, -273, -162, 198, 243]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [42, 58, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [51, 44, 33], [15, 22, 34], [0, 1]]
 g := ![![[61, 63, 6], [3, 27, 59], [45, 17], [19, 33], [66, 1], []], ![[38, 7, 16, 26], [11, 53, 11, 6], [46, 65], [61, 54], [46, 15], [6, 17]], ![[32, 9, 50, 8], [39, 10, 44, 27], [62, 62], [12, 39], [19, 60], [5, 17]]]
 h' := ![![[51, 44, 33], [8, 49, 26], [33, 14, 27], [28, 62, 34], [42, 16, 10], [0, 0, 1], [0, 1]], ![[15, 22, 34], [65, 45, 45], [51, 55, 51], [43, 19, 47], [27, 57, 11], [4, 9, 22], [51, 44, 33]], ![[0, 1], [61, 40, 63], [45, 65, 56], [61, 53, 53], [30, 61, 46], [15, 58, 44], [15, 22, 34]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44, 64], []]
 b := ![[], [61, 35, 61], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [42, 58, 1, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-74116, 28304, 19350, 25078, -92212]
  a := ![-11, -7, 13, -19, -44]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![14684, 69514, 27838, 25078, -92212]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 300763 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![46692, 13383, -6276, 18858, 27167]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![46692, 13383, -6276, 18858, 27167]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![49, 48, 1, 0, 0], ![6, 43, 0, 1, 0], ![21, 63, 0, 0, 1]] where
  M :=![![![46692, 13383, -6276, 18858, 27167], ![119217, 34170, -16024, 48148, 69363], ![304385, 87245, -40911, 122930, 177095], ![18106, 5191, -2433, 7313, 10534], ![86558, 24810, -11634, 34958, 50361]]]
  hmulB := by decide  
  f := ![![![-18, 33, 20, 14, -109]], ![![-299, 96, -118, 24, 439]], ![![-207, 80, -63, 24, 218]], ![![-197, 69, -75, 19, 271]], ![![-277, 93, -102, 24, 375]]]
  g := ![![![-4917, -32952, -6276, 18858, 27167], ![-12554, -84133, -16024, 48148, 69363], ![-32053, -214806, -40911, 122930, 177095], ![-1907, -12778, -2433, 7313, 10534], ![-9115, -61085, -11634, 34958, 50361]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P1 : CertificateIrreducibleZModOfList' 67 2 2 6 [34, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [43, 66], [0, 1]]
 g := ![![[48, 55], [52, 26], [6], [4], [40], [1]], ![[1, 12], [31, 41], [6], [4], [40], [1]]]
 h' := ![![[43, 66], [41, 51], [46, 19], [7, 26], [64, 2], [33, 43], [0, 1]], ![[0, 1], [23, 16], [59, 48], [53, 41], [16, 65], [6, 24], [43, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [17, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N1 : CertifiedPrimeIdeal' SI67N1 67 where
  n := 2
  hpos := by decide
  P := [34, 24, 1]
  hirr := P67P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![45214, 14222, 4261, 3556, -18348]
  a := ![-49, -56, 48, -106, -199]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2991, 12130, 4261, 3556, -18348]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N1 B_one_repr
lemma NI67N1 : Nat.card (O ⧸ I67N1) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![18, -33, -20, -14, 109]] ![![46692, 13383, -6276, 18858, 27167]]
  ![![67, 0, 0, 0, 0]] where
 M := ![![![-67, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 166, -54, 150, 138]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![173, 166, -54, 150, 138]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![57, 16, 23, 1, 0], ![53, 26, 24, 0, 1]] where
  M :=![![![173, 166, -54, 150, 138], ![714, 53, -146, 186, 786], ![2730, 170, 281, 670, -870], ![-484, 454, -198, 215, 404], ![1278, -312, 238, 44, -547]]]
  hmulB := by decide  
  f := ![![![903, -122, -186, -14, 338]], ![![986, -41, 258, -1226, -1126]], ![![-5830, 1050, 2511, -3350, -6430]], ![![-985, 238, 727, -1361, -2068]], ![![-953, 252, 812, -1602, -2353]]]
  g := ![![![-221, -82, -96, 150, 138], ![-726, -329, -328, 186, 786], ![150, 170, 81, 670, -870], ![-481, -190, -209, 215, 404], ![391, 186, 174, 44, -547]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [20, 56, 11, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 22, 21], [46, 48, 50], [0, 1]]
 g := ![![[49, 55, 6], [45, 63, 19], [20, 19, 10], [49, 36], [60, 1], []], ![[50, 56, 34, 34], [62, 46, 27, 65], [67, 60, 33, 31], [59, 43], [8, 32], [49, 15]], ![[13, 66, 14, 58], [4, 61, 34, 36], [49, 27, 37, 29], [41, 29], [49, 58], [20, 15]]]
 h' := ![![[14, 22, 21], [23, 20, 19], [26, 55, 27], [63, 52, 62], [7, 28, 65], [0, 0, 1], [0, 1]], ![[46, 48, 50], [33, 32, 54], [5, 51, 37], [37, 63, 21], [62, 61, 16], [68, 57, 48], [14, 22, 21]], ![[0, 1], [35, 19, 69], [40, 36, 7], [4, 27, 59], [16, 53, 61], [12, 14, 22], [46, 48, 50]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55, 1], []]
 b := ![[], [28, 51, 27], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [20, 56, 11, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4729, -538, 3829, -1986, -11087]
  a := ![-4, -4, 5, -9, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![9804, 4500, 4445, -1986, -11087]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 357911 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9553, 2738, -1284, 3858, 5558]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![9553, 2738, -1284, 3858, 5558]] 
 ![![71, 0, 0, 0, 0], ![14, 1, 0, 0, 0], ![17, 0, 1, 0, 0], ![26, 0, 0, 1, 0], ![65, 0, 0, 0, 1]] where
  M :=![![![9553, 2738, -1284, 3858, 5558], ![24390, 6991, -3278, 9850, 14190], ![62270, 17850, -8369, 25150, 36230], ![3704, 1062, -498, 1497, 2156], ![17708, 5076, -2380, 7152, 10303]]]
  hmulB := by decide  
  f := ![![![139, -38, 68, -18, -258]], ![![16, -1, 10, -2, -42]], ![![63, -36, 27, -16, -76]], ![![50, -10, 26, -3, -104]], ![![137, -46, 64, -22, -231]]]
  g := ![![![-6599, 2738, -1284, 3858, 5558], ![-16848, 6991, -3278, 9850, 14190], ![-43017, 17850, -8369, 25150, 36230], ![-2560, 1062, -498, 1497, 2156], ![-12233, 5076, -2380, 7152, 10303]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-939, 116, 138, 160, -172]] i)))

def SI71N2: IdealEqSpanCertificate' Table ![![-939, 116, 138, 160, -172]] 
 ![![71, 0, 0, 0, 0], ![40, 1, 0, 0, 0], ![33, 0, 1, 0, 0], ![61, 0, 0, 1, 0], ![17, 0, 0, 0, 1]] where
  M :=![![![-939, 116, 138, 160, -172], ![-196, -89, -536, 1516, 1796], ![8420, -1360, -2841, 2780, 6740], ![2676, -256, -28, -1417, -696], ![1798, -292, -610, 604, 1451]]]
  hmulB := by decide  
  f := ![![![-5338133, -1530068, 717494, -2155960, -3105868]], ![![-3199364, -917033, 430024, -1292156, -1861476]], ![![-2971239, -851644, 399361, -1200020, -1728744]], ![![-4615443, -1322924, 620358, -1864081, -2685388]], ![![-1417525, -406304, 190528, -572508, -824753]]]
  g := ![![![-239, 116, 138, 160, -172], ![-1436, -89, -536, 1516, 1796], ![-1797, -1360, -2841, 2780, 6740], ![1579, -256, -28, -1417, -696], ![-393, -292, -610, 604, 1451]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![173, 166, -54, 150, 138]] ![![9553, 2738, -1284, 3858, 5558]]
  ![![5338133, 1530068, -717494, 2155960, 3105868]] where
 M := ![![![5338133, 1530068, -717494, 2155960, 3105868]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![5338133, 1530068, -717494, 2155960, 3105868]] ![![-939, 116, 138, 160, -172]]
  ![![71, 0, 0, 0, 0]] where
 M := ![![![-71, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![39, -41, 5, -20, 22]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![39, -41, 5, -20, 22]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![49, 52, 1, 0, 0], ![8, 27, 0, 1, 0], ![51, 54, 0, 0, 1]] where
  M :=![![![39, -41, 5, -20, 22], ![26, 44, 41, 34, -226], ![-610, 265, -284, 60, 950], ![284, -219, 83, -93, -124], ![-418, 262, -152, 96, 379]]]
  hmulB := by decide  
  f := ![![![-601, -161, 89, -250, -366]], ![![-1598, -406, 223, -592, -902]], ![![-1595, -412, 225, -608, -916]], ![![-658, -169, 92, -247, -374]], ![![-1617, -417, 229, -618, -931]]]
  g := ![![![-16, -13, 5, -20, 22], ![127, 126, 41, 34, -226], ![-488, -519, -284, 60, 950], ![45, 64, 83, -93, -124], ![-179, -204, -152, 96, 379]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [72, 62, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 72], [0, 1]]
 g := ![![[11, 72], [49], [32], [40, 61], [48], [1]], ![[0, 1], [49], [32], [54, 12], [48], [1]]]
 h' := ![![[11, 72], [68, 27], [26, 7], [40, 55], [49, 39], [1, 11], [0, 1]], ![[0, 1], [0, 46], [30, 66], [61, 18], [40, 34], [49, 62], [11, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [69, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [72, 62, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6495, 7920, 1883, 5806, -6984]
  a := ![36, 27, -39, 62, 143]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3068, 1786, 1883, 5806, -6984]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![549, 158, -74, 222, 320]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![549, 158, -74, 222, 320]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![9, 48, 1, 0, 0], ![59, 63, 0, 1, 0], ![11, 71, 0, 0, 1]] where
  M :=![![![549, 158, -74, 222, 320], ![1404, 401, -188, 566, 816], ![3580, 1030, -481, 1450, 2080], ![212, 62, -30, 87, 128], ![1020, 292, -136, 412, 589]]]
  hmulB := by decide  
  f := ![![![45, -6, -14, 6, 32]], ![![108, -19, 8, -58, -48]], ![![73, -12, 5, -40, -32]], ![![127, -21, -4, -45, -16]], ![![111, -19, 6, -56, -43]]]
  g := ![![![-211, -452, -74, 222, 320], ![-538, -1153, -188, 566, 816], ![-1377, -2944, -481, 1450, 2080], ![-83, -179, -30, 87, 128], ![-391, -835, -136, 412, 589]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P1 : CertificateIrreducibleZModOfList' 73 2 2 6 [71, 68, 1] where
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
 g := ![![[39, 36], [65], [36], [43, 1], [25], [1]], ![[0, 37], [65], [36], [48, 72], [25], [1]]]
 h' := ![![[5, 72], [30, 67], [22, 24], [13, 67], [54, 72], [2, 5], [0, 1]], ![[0, 1], [0, 6], [69, 49], [56, 6], [49, 1], [27, 68], [5, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22]]
 b := ![[], [9, 11]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N1 : CertifiedPrimeIdeal' SI73N1 73 where
  n := 2
  hpos := by decide
  P := [71, 68, 1]
  hirr := P73P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2835, 400, 3584, -600, -12070]
  a := ![-21, -9, 26, -28, -83]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1823, 9906, 3584, -600, -12070]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N1 B_one_repr
lemma NI73N1 : Nat.card (O ⧸ I73N1) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N1

def I73N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19, 1, -5, 24, 22]] i)))

def SI73N2: IdealEqSpanCertificate' Table ![![-19, 1, -5, 24, 22]] 
 ![![73, 0, 0, 0, 0], ![46, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![60, 0, 0, 1, 0], ![38, 0, 0, 0, 1]] where
  M :=![![![-19, 1, -5, 24, 22], ![114, -20, -49, 66, 126], ![510, -65, -92, -40, 150], ![-20, 11, 45, -107, -140], ![110, -14, -20, -8, 33]]]
  hmulB := by decide  
  f := ![![![53, -55, -25, -26, 178]], ![![40, -36, -13, -16, 102]], ![![-29, 20, -13, 8, 36]], ![![52, -53, -19, -25, 148]], ![![12, -16, -18, -8, 101]]]
  g := ![![![-32, 1, -5, 24, 22], ![-105, -20, -49, 66, 126], ![4, -65, -92, -40, 150], ![153, 11, 45, -107, -140], ![0, -14, -20, -8, 33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N2 : Nat.card (O ⧸ I73N2) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N2)

lemma isPrimeI73N2 : Ideal.IsPrime I73N2 := prime_ideal_of_norm_prime hp73.out _ NI73N2
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![39, -41, 5, -20, 22]] ![![549, 158, -74, 222, 320]]
  ![![-53, 55, 25, 26, -178]] where
 M := ![![![-53, 55, 25, 26, -178]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI73N1 : IdealMulLeCertificate' Table 
  ![![-53, 55, 25, 26, -178]] ![![-19, 1, -5, 24, 22]]
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


def P79P0 : CertificateIrreducibleZModOfList' 79 5 2 6 [66, 60, 12, 53, 22, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 65, 1, 76, 73], [60, 6, 49, 56, 71], [18, 56, 48, 68, 48], [36, 30, 60, 37, 45], [0, 1]]
 g := ![![[26, 15, 48, 62, 40], [29, 18, 61, 36, 64], [67, 61, 25, 27, 64], [49, 46, 36, 57, 1], [], []], ![[34, 2, 5, 30, 4, 46, 65, 10], [18, 67, 72, 40, 1, 75, 18, 65], [49, 49, 35, 33, 40, 22, 8, 11], [3, 67, 44, 75, 66, 33, 32, 52], [15, 74, 78, 32], [20, 27, 34, 36]], ![[51, 39, 6, 71, 13, 7, 63, 48], [38, 30, 1, 13, 46, 17, 41, 61], [76, 44, 52, 56, 72, 68, 61, 28], [56, 32, 34, 15, 45, 58, 69, 71], [35, 14, 48, 16], [18, 36, 66, 64]], ![[48, 16, 46, 16, 74, 45, 40, 59], [50, 74, 57, 65, 75, 58, 42, 48], [3, 55, 32, 71, 0, 27, 33, 6], [54, 30, 60, 13, 9, 38, 1, 39], [17, 72, 1, 50], [8, 68, 1, 13]], ![[70, 40, 39, 32, 59, 6, 8, 67], [55, 58, 5, 63, 19, 51, 76, 1], [12, 1, 56, 64, 23, 51, 43, 46], [19, 1, 56, 2, 20, 74, 56, 18], [1, 59, 39, 25], [73, 10, 18, 50]]]
 h' := ![![[22, 65, 1, 76, 73], [61, 78, 66, 27, 35], [2, 37, 12, 48, 71], [5, 28, 43, 14, 71], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[60, 6, 49, 56, 71], [47, 51, 72, 68, 50], [49, 13, 0, 66, 23], [70, 26, 25, 53, 8], [20, 68, 48, 68, 53], [33, 36, 7, 44, 43], [22, 65, 1, 76, 73]], ![[18, 56, 48, 68, 48], [76, 73, 3, 59, 28], [38, 64, 27, 3, 38], [34, 24, 64, 23, 6], [7, 44, 75, 25, 1], [42, 29, 53, 29, 75], [60, 6, 49, 56, 71]], ![[36, 30, 60, 37, 45], [40, 44, 71, 71, 25], [57, 29, 74, 42, 1], [1, 59, 45, 17, 22], [46, 56, 15, 7, 67], [33, 50, 69, 57, 45], [18, 56, 48, 68, 48]], ![[0, 1], [55, 70, 25, 12, 20], [18, 15, 45, 78, 25], [33, 21, 60, 51, 51], [75, 69, 20, 58, 36], [33, 43, 28, 28, 74], [36, 30, 60, 37, 45]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37, 47, 11, 76], [], [], []]
 b := ![[], [65, 43, 3, 24, 39], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 5
  hpos := by decide
  P := [66, 60, 12, 53, 22, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8665397346, 1014530640, 6776228160, 2354320080, -30393031680]
  a := ![12, -4, -14, -2, 48]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![109688574, 12842160, 85775040, 29801520, -384721920]
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

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![27793, 7982, -3748, 11236, 16214]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![27793, 7982, -3748, 11236, 16214]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![0, 0, 83, 0, 0], ![70, 77, 72, 1, 0], ![65, 67, 80, 0, 1]] where
  M :=![![![27793, 7982, -3748, 11236, 16214], ![71114, 20289, -9512, 28656, 41246], ![181050, 52210, -24433, 73340, 105510], ![10764, 3078, -1474, 4343, 6396], ![51504, 14860, -6928, 20868, 29903]]]
  hmulB := by decide  
  f := ![![![1087, -202, -500, 708, 1302]], ![![5322, -705, -1024, -272, 1758]], ![![4730, -70, 1869, -7540, -7450]], ![![9880, -873, 274, -6217, -3790]], ![![9719, -795, 588, -6952, -4761]]]
  g := ![![![-21839, -23416, -25420, 11236, 16214], ![-55612, -59635, -64728, 28656, 41246], ![-142300, -152580, -165611, 73340, 105510], ![-8542, -9155, -9950, 4343, 6396], ![-40397, -43319, -47008, 20868, 29903]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [73, 20, 23, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 22, 64], [39, 60, 19], [0, 1]]
 g := ![![[27, 68, 16], [28, 0, 10], [61, 36], [19, 28], [11, 60, 1], []], ![[21, 17, 52, 65], [7, 47, 48, 61], [60, 40], [62, 17], [15, 22, 35, 75], [74, 29]], ![[51, 81, 70, 5], [42, 35, 34, 74], [58, 38], [27, 21], [19, 44, 68, 66], [36, 29]]]
 h' := ![![[21, 22, 64], [31, 13, 4], [65, 77, 50], [6, 2, 77], [27, 48, 51], [0, 0, 1], [0, 1]], ![[39, 60, 19], [48, 52, 76], [59, 14, 43], [17, 63, 17], [12, 23, 73], [19, 66, 60], [21, 22, 64]], ![[0, 1], [11, 18, 3], [8, 75, 73], [3, 18, 72], [56, 12, 42], [55, 17, 22], [39, 60, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59, 56], []]
 b := ![[], [40, 53, 51], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [73, 20, 23, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1393422, -87159, -176104, 398520, 843801]
  a := ![24, 19, -20, 44, 83]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-980121, -1051902, -1161128, 398520, 843801]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 571787 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1087, 202, 500, -708, -1302]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-1087, 202, 500, -708, -1302]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![47, 27, 1, 0, 0], ![64, 7, 0, 1, 0], ![15, 75, 0, 0, 1]] where
  M :=![![![-1087, 202, 500, -708, -1302], ![-5322, 705, 1024, 272, -1758], ![-4730, 70, -1869, 7540, 7450], ![6404, -1006, -2022, 1747, 4676], ![-1048, 20, -392, 1612, 1579]]]
  hmulB := by decide  
  f := ![![![-27793, -7982, 3748, -11236, -16214]], ![![-71114, -20289, 9512, -28656, -41246]], ![![-41053, -11749, 5511, -16568, -23870]], ![![-27558, -7903, 3710, -11133, -16058]], ![![-69903, -19955, 9356, -28176, -40561]]]
  g := ![![![485, 1076, 500, -708, -1302], ![-536, 1241, 1024, 272, -1758], ![-6159, -6759, -1869, 7540, 7450], ![-970, -3727, -2022, 1747, 4676], ![-1319, -1435, -392, 1612, 1579]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P1 : CertificateIrreducibleZModOfList' 83 2 2 6 [56, 48, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [35, 82], [0, 1]]
 g := ![![[72, 77], [5, 11], [59], [49], [28, 63], [1]], ![[28, 6], [58, 72], [59], [49], [75, 20], [1]]]
 h' := ![![[35, 82], [52, 49], [65, 29], [76, 15], [9, 7], [27, 35], [0, 1]], ![[0, 1], [24, 34], [1, 54], [20, 68], [5, 76], [7, 48], [35, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49]]
 b := ![[], [7, 66]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N1 : CertifiedPrimeIdeal' SI83N1 83 where
  n := 2
  hpos := by decide
  P := [56, 48, 1]
  hirr := P83P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![255, -110, -95, -130, 150]
  a := ![0, -3, -1, -4, 1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![130, -95, -95, -130, 150]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N1 B_one_repr
lemma NI83N1 : Nat.card (O ⧸ I83N1) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![27793, 7982, -3748, 11236, 16214]] ![![-1087, 202, 500, -708, -1302]]
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


def P89P0 : CertificateIrreducibleZModOfList' 89 5 2 6 [72, 70, 54, 19, 63, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [32, 14, 4, 81, 82], [81, 11, 12, 28, 13], [88, 69, 4, 62, 82], [3, 83, 69, 7, 1], [0, 1]]
 g := ![![[49, 40, 66, 17, 81], [66, 74, 74, 49], [54, 4, 18, 78], [67, 85, 11, 34, 53], [1], []], ![[42, 32, 8, 23, 40, 68, 42, 41], [62, 78, 55, 69], [14, 52, 4, 16], [53, 29, 77, 47, 34, 33, 62, 7], [81, 32, 72, 46, 18, 46, 83, 13], [17, 47, 51, 49]], ![[60, 53, 23, 50, 41, 35, 65, 60], [88, 88, 81, 69], [29, 30, 23, 25], [25, 33, 71, 28, 3, 67, 54, 60], [18, 22, 30, 69, 43, 81, 36, 3], [7, 49, 49, 80]], ![[18, 66, 69, 26, 84, 70, 59, 33], [42, 62, 55, 16], [62, 75, 64, 72], [37, 46, 30, 3, 38, 17, 80, 83], [87, 13, 2, 7, 26, 66, 82, 52], [64, 63, 50, 49]], ![[86, 4, 72, 66, 66, 79, 26, 4], [32, 17, 82, 18], [86, 55, 78, 69], [36, 6, 67, 17, 77, 0, 31, 17], [5, 35, 75, 70, 24, 68, 34, 25], [42, 51, 40, 1]]]
 h' := ![![[32, 14, 4, 81, 82], [70, 36, 17, 32, 80], [85, 87, 75, 16, 7], [71, 70, 76, 35, 73], [17, 19, 35, 70, 26], [0, 0, 1], [0, 1]], ![[81, 11, 12, 28, 13], [28, 35, 39, 16, 57], [65, 57, 79, 73, 46], [19, 86, 8, 7, 85], [44, 29, 82, 7, 34], [67, 60, 48, 54, 7], [32, 14, 4, 81, 82]], ![[88, 69, 4, 62, 82], [61, 28, 9, 79, 78], [16, 2, 20, 52, 46], [71, 22, 48, 53, 5], [17, 2, 34, 14, 78], [5, 78, 69, 40, 12], [81, 11, 12, 28, 13]], ![[3, 83, 69, 7, 1], [6, 18, 52, 33, 50], [2, 31, 34, 55, 4], [85, 58, 56, 45, 61], [59, 73, 47, 64, 67], [21, 13, 51, 85, 75], [88, 69, 4, 62, 82]], ![[0, 1], [27, 61, 61, 18, 2], [27, 1, 59, 71, 75], [16, 31, 79, 38, 43], [3, 55, 69, 23, 62], [11, 27, 9, 88, 84], [3, 83, 69, 7, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53, 62, 64, 87], [], [], []]
 b := ![[], [56, 50, 82, 6, 76], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 5
  hpos := by decide
  P := [72, 70, 54, 19, 63, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![27746797352, -2045340684, 17188574005, 3979736638, -71479526572]
  a := ![23, 9, -23, 28, 89]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![311761768, -22981356, 193130045, 44716142, -803140748]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0, 0, 0]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0, 0, 0]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![0, 0, 97, 0, 0], ![0, 0, 0, 97, 0], ![0, 0, 0, 0, 97]] where
  M :=![![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![0, 0, 97, 0, 0], ![0, 0, 0, 97, 0], ![0, 0, 0, 0, 97]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 5 2 6 [32, 54, 9, 81, 11, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [76, 92, 24, 7, 90], [8, 46, 62, 94, 37], [79, 65, 59, 85, 56], [20, 87, 49, 8, 11], [0, 1]]
 g := ![![[34, 18, 32, 4, 88], [53, 19, 74, 64], [70, 4, 88, 2], [5, 9, 95, 48], [86, 1], []], ![[7, 80, 92, 4, 83, 82, 55, 41], [20, 5, 2, 25], [19, 14, 36, 27], [96, 90, 32, 72], [68, 63, 78, 66], [61, 66, 9, 19, 20, 61, 49, 45]], ![[8, 77, 65, 24, 22, 57, 4, 58], [33, 70, 15, 27], [0, 82, 14, 1], [14, 86, 10, 27], [67, 15, 20, 73], [63, 13, 26, 82, 12, 44, 80, 19]], ![[96, 9, 56, 90, 69, 82, 24, 23], [74, 20, 24, 61], [70, 25, 11, 3], [45, 84, 1, 85], [70, 64, 79, 85], [40, 31, 84, 92, 86, 39, 88, 46]], ![[82, 41, 72, 48, 73, 16, 57, 85], [59, 69, 50, 61], [17, 10, 83, 61], [83, 67, 23, 96], [90, 93, 37, 35], [50, 79, 28, 96, 47, 67, 0, 70]]]
 h' := ![![[76, 92, 24, 7, 90], [51, 19, 30, 25, 66], [96, 50, 27, 12, 89], [69, 9, 88, 3, 83], [61, 77, 45, 9, 40], [0, 0, 0, 1], [0, 1]], ![[8, 46, 62, 94, 37], [7, 23, 59, 33, 28], [68, 10, 37, 18, 5], [26, 36, 68, 9, 67], [24, 96, 47, 69, 13], [39, 7, 71, 70, 39], [76, 92, 24, 7, 90]], ![[79, 65, 59, 85, 56], [65, 47, 20, 88, 32], [65, 41, 76, 44, 30], [29, 61, 53, 36, 96], [63, 6, 49, 45, 67], [48, 67, 59, 47, 49], [8, 46, 62, 94, 37]], ![[20, 87, 49, 8, 11], [79, 87, 59, 52, 93], [64, 71, 8, 3, 35], [48, 5, 13, 41, 10], [79, 49, 71, 9, 52], [66, 82, 46, 63, 45], [79, 65, 59, 85, 56]], ![[0, 1], [49, 18, 26, 93, 72], [26, 22, 46, 20, 35], [52, 83, 69, 8, 35], [34, 63, 79, 62, 22], [95, 38, 18, 13, 61], [20, 87, 49, 8, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43, 55, 61, 34], [], [], []]
 b := ![[], [47, 47, 76, 67, 88], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 5
  hpos := by decide
  P := [32, 54, 9, 81, 11, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1897034626, -1809112080, 473313828, -703374160, -27453910]
  a := ![14, 7, -17, 20, 55]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![19557058, -18650640, 4879524, -7251280, -283030]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 8587340257 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def PBC97 : ContainsPrimesAboveP 97 ![I97N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![97, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 97 (by decide) 𝕀

instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![811326, -99989, -118892, -139246, 147283]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![811326, -99989, -118892, -139246, 147283]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![0, 0, 101, 0, 0], ![0, 0, 0, 101, 0], ![28, 97, 60, 70, 1]] where
  M :=![![![811326, -99989, -118892, -139246, 147283], ![163357, 77620, 465032, -1312092, -1555817], ![-7291635, 1176425, 2458079, -2397590, -5829285], ![-2309982, 221307, 21475, 1228991, 608622], ![-1555890, 251762, 528190, -521274, -1255801]]]
  hmulB := by decide  
  f := ![![![-540192, -154861, 72612, -218190, -314299]], ![![-1379277, -395322, 185410, -557048, -802623]], ![![-3521965, -1009275, 473199, -1422290, -2048515]], ![![-209374, -60165, 28203, -84667, -121966]], ![![-3721693, -1066706, 500184, -1503084, -2165206]]]
  g := ![![![-32798, -142440, -88672, -103456, 147283], ![432933, 1494969, 928852, 1065298, -1555817], ![1543845, 5610070, 3487279, 4016360, -5829285], ![-191598, -582327, -361345, -409649, 608622], ![332738, 1208559, 751250, 865196, -1255801]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 4 2 6 [31, 0, 91, 75, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [61, 0, 78, 22], [82, 17, 1, 1], [85, 83, 22, 78], [0, 1]]
 g := ![![[86, 76, 17, 1], [49, 63, 5], [74, 5], [30, 27, 87], [80, 26, 1], []], ![[6, 3, 87, 28, 64, 58], [4, 9, 5], [72, 56, 78, 24, 22, 54], [48, 77, 68], [52, 43, 17], [51, 11, 21, 76, 42, 43]], ![[14, 55, 90, 69, 37, 4], [56, 84, 78], [37, 15, 26, 24, 92, 9], [75, 40, 14], [28, 77, 20], [75, 7, 91, 10, 29, 1]], ![[1, 37, 42, 42, 72, 58], [54, 62, 78], [87, 69, 35, 75, 67, 4], [70, 59, 4], [37, 48, 5], [8, 42, 22, 5, 59, 54]]]
 h' := ![![[61, 0, 78, 22], [29, 67, 46, 1], [29, 0, 49, 56], [85, 50, 56], [45, 2, 62, 17], [0, 0, 0, 1], [0, 1]], ![[82, 17, 1, 1], [8, 74, 79, 18], [43, 64, 11, 45], [48, 9, 67, 38], [18, 89, 1, 13], [69, 63, 54, 44], [61, 0, 78, 22]], ![[85, 83, 22, 78], [33, 88, 58, 2], [70, 25, 59, 52], [18, 98, 42, 98], [90, 31, 24, 69], [7, 14, 12, 11], [82, 17, 1, 1]], ![[0, 1], [44, 74, 19, 80], [100, 12, 83, 49], [65, 45, 37, 66], [66, 80, 14, 2], [100, 24, 35, 45], [85, 83, 22, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [20, 27, 22], []]
 b := ![[], [], [6, 81, 62, 79], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 4
  hpos := by decide
  P := [31, 0, 91, 75, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4261253, 948280, -1375384, 2266143, 4589720]
  a := ![10, 8, -10, 19, 36]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1230207, -4398560, -2740184, -3158557, 4589720]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 104060401 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![540192, 154861, -72612, 218190, 314299]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![540192, 154861, -72612, 218190, 314299]] 
 ![![101, 0, 0, 0, 0], ![49, 1, 0, 0, 0], ![23, 0, 1, 0, 0], ![85, 0, 0, 1, 0], ![31, 0, 0, 0, 1]] where
  M :=![![![540192, 154861, -72612, 218190, 314299], ![1379277, 395322, -185410, 557048, 802623], ![3521965, 1009275, -473199, 1422290, 2048515], ![209374, 60165, -28203, 84667, 121966], ![1001668, 286914, -134528, 404418, 582483]]]
  hmulB := by decide  
  f := ![![![-811326, 99989, 118892, 139246, -147283]], ![![-395231, 47741, 53076, 80546, -56050]], ![![-112563, 11122, 2737, 55448, 24176]], ![![-659928, 81958, 99845, 105019, -129977]], ![![-233616, 28197, 31262, 47900, -32772]]]
  g := ![![![-333340, 154861, -72612, 218190, 314299], ![-851064, 395322, -185410, 557048, 802623], ![-2172748, 1009275, -473199, 1422290, 2048515], ![-129383, 60165, -28203, 84667, 121966], ![-617777, 286914, -134528, 404418, 582483]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![811326, -99989, -118892, -139246, 147283]] ![![540192, 154861, -72612, 218190, 314299]]
  ![![101, 0, 0, 0, 0]] where
 M := ![![![-101, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC101 : ContainsPrimesAboveP 101 ![I101N0, I101N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
    exact isPrimeI101N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 101 (by decide) (𝕀 ⊙ MulI101N0)
instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0, 0, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0, 0, 0]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![0, 0, 0, 103, 0], ![0, 0, 0, 0, 103]] where
  M :=![![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![0, 0, 0, 103, 0], ![0, 0, 0, 0, 103]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 5 2 6 [89, 79, 23, 84, 32, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [82, 43, 83, 49, 75], [45, 69, 37, 29, 68], [59, 46, 26, 43, 25], [91, 47, 60, 85, 38], [0, 1]]
 g := ![![[50, 86, 93, 16, 61], [79, 67, 39, 9, 15], [77, 7, 53, 83, 46], [76, 85, 22, 66], [71, 1], []], ![[22, 60, 26, 70, 62, 13, 46, 11], [3, 95, 90, 65, 100, 93, 22, 21], [102, 9, 20, 13, 16, 62, 102, 42], [62, 42, 27, 14], [14, 98, 26, 26], [13, 19, 98, 0, 6, 37, 98, 90]], ![[35, 61, 38, 30, 86, 5, 81, 82], [4, 43, 86, 63, 57, 100, 12, 49], [79, 86, 43, 36, 71, 69, 50, 7], [90, 33, 32, 29], [101, 23, 79, 17], [70, 78, 67, 29, 60, 75, 10, 76]], ![[63, 34, 83, 11, 21, 59, 15, 30], [89, 63, 54, 15, 47, 20, 9, 60], [26, 90, 24, 17, 10, 52, 51, 59], [14, 97, 1, 28], [42, 39, 21, 98], [13, 35, 61, 52, 42, 21, 41, 72]], ![[35, 48, 91, 30, 65, 52, 1, 92], [45, 62, 19, 38, 80, 11, 100, 76], [16, 15, 4, 62, 44, 10, 87, 76], [26, 42, 2, 16], [92, 101, 33, 91], [18, 48, 39, 84, 16, 25, 35, 76]]]
 h' := ![![[82, 43, 83, 49, 75], [76, 91, 53, 62, 79], [48, 70, 72, 5, 18], [94, 34, 14, 24, 56], [67, 70, 39, 90, 13], [0, 0, 0, 1], [0, 1]], ![[45, 69, 37, 29, 68], [83, 9, 53, 36, 92], [19, 7, 43, 100, 98], [22, 35, 7, 49, 87], [9, 64, 44, 26, 23], [88, 96, 1, 34, 52], [82, 43, 83, 49, 75]], ![[59, 46, 26, 43, 25], [43, 46, 19, 2, 17], [38, 85, 32, 99, 94], [14, 19, 41, 25, 12], [89, 1, 94, 67, 21], [23, 59, 8, 23, 74], [45, 69, 37, 29, 68]], ![[91, 47, 60, 85, 38], [5, 92, 48, 56, 28], [45, 51, 91, 26, 34], [62, 16, 49, 0, 89], [81, 99, 99, 10, 50], [76, 67, 90, 10, 60], [59, 46, 26, 43, 25]], ![[0, 1], [26, 71, 33, 50, 93], [99, 96, 71, 79, 65], [15, 102, 95, 5, 65], [75, 75, 33, 13, 99], [69, 87, 4, 35, 20], [91, 47, 60, 85, 38]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29, 102, 5, 27], [], [], []]
 b := ![[], [64, 71, 91, 41, 12], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 5
  hpos := by decide
  P := [89, 79, 23, 84, 32, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![34331334790, -100000568621, -25519233238, -60388138830, 219141235121]
  a := ![-23, -7, 22, -30, -99]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![333313930, -970879307, -247759546, -586292610, 2127584807]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 11592740743 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def PBC103 : ContainsPrimesAboveP 103 ![I103N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![103, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 103 (by decide) 𝕀



lemma PB397I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 103 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 103 (by omega)

def PB397I2 : PrimesBelowBoundCertificateInterval O 61 103 397 where
  m := 9
  g := ![2, 3, 3, 1, 2, 1, 1, 2, 1]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103]
  hP := PB397I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1, I71N2]
    · exact ![I73N0, I73N1, I73N2]
    · exact ![I79N0]
    · exact ![I83N0, I83N1]
    · exact ![I89N0]
    · exact ![I97N0]
    · exact ![I101N0, I101N1]
    · exact ![I103N0]
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
    · exact ![357911, 71, 71]
    · exact ![5329, 5329, 73]
    · exact ![3077056399]
    · exact ![571787, 6889]
    · exact ![5584059449]
    · exact ![8587340257]
    · exact ![104060401, 101]
    · exact ![11592740743]
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
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
  β := ![I71N1, I71N2, I73N2, I101N1]
  Il := ![[], [I71N1, I71N2], [I73N2], [], [], [], [], [I101N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
