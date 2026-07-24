
import IdealArithmetic.Examples.NF5_1_2700000_1.RI5_1_2700000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-279, -940, 478, 620, 1040]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![-279, -940, 478, 620, 1040]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![0, 0, 67, 0, 0], ![0, 0, 0, 67, 0], ![15, 21, 6, 56, 1]] where
  M :=![![![-279, -940, 478, 620, 1040], ![-1240, -2339, 978, 1356, 2240], ![-2712, -5780, 1823, 2900, 5072], ![-1544, -3180, 374, 1101, 2184], ![672, 1450, -294, -600, -1121]]]
  hmulB := by decide  
  f := ![![![-5, -20, 26, 20, 112]], ![![-40, 7, -26, -92, -320]], ![![184, 100, -67, 220, 496]], ![![-312, -260, 242, -233, -168]], ![![-257, -209, 192, -200, -177]]]
  g := ![![![-237, -340, -86, -860, 1040], ![-520, -737, -186, -1852, 2240], ![-1176, -1676, -427, -4196, 5072], ![-512, -732, -190, -1809, 2184], ![261, 373, 96, 928, -1121]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 4 2 6 [13, 6, 26, 48, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [62, 41, 52, 58], [65, 56, 6, 10], [26, 36, 9, 66], [0, 1]]
 g := ![![[21, 56, 22, 23], [4, 25, 32, 29], [8, 34, 65], [34, 42, 26], [1], []], ![[25, 47, 36, 15, 47, 42], [5, 24, 22, 66, 34, 34], [47, 63, 65], [19, 49, 21], [25, 60, 4], [61, 0, 14]], ![[5, 12, 14, 9, 49, 49], [26, 34, 20, 37, 57, 26], [52, 18, 10], [52, 61, 47], [56, 49, 1], [19, 10, 33]], ![[63, 57, 8, 19, 27, 46], [11, 20, 14, 46, 17, 18], [64, 14, 10], [60, 60, 64], [33, 50, 1], [2, 1, 1]]]
 h' := ![![[62, 41, 52, 58], [15, 63, 51, 36], [55, 23, 12, 37], [62, 9, 42, 20], [54, 61, 41, 19], [0, 0, 1], [0, 1]], ![[65, 56, 6, 10], [18, 54, 24, 43], [29, 54, 3, 19], [38, 39, 36, 47], [33, 14, 37, 17], [36, 28, 63, 2], [62, 41, 52, 58]], ![[26, 36, 9, 66], [16, 30, 54, 5], [15, 3, 26, 4], [17, 26, 4, 12], [31, 15, 34, 39], [25, 1, 52, 66], [65, 56, 6, 10]], ![[0, 1], [47, 54, 5, 50], [8, 54, 26, 7], [61, 60, 52, 55], [38, 44, 22, 59], [47, 38, 18, 66], [26, 36, 9, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [62, 63, 48], []]
 b := ![[], [], [34, 23, 65, 22], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 4
  hpos := by decide
  P := [13, 6, 26, 48, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![75157542, 149934657, -71495543, -64761025, -221292744]
  a := ![15, 37, -35, -39, -90]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![50664906, 71598243, 18750163, 183994517, -221292744]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 20151121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, -20, 26, 20, 112]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![-5, -20, 26, 20, 112]] 
 ![![67, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![58, 0, 1, 0, 0], ![18, 0, 0, 1, 0], ![55, 0, 0, 0, 1]] where
  M :=![![![-5, -20, 26, 20, 112], ![-40, 7, -26, -92, -320], ![184, 100, -67, 220, 496], ![-312, -260, 242, -233, -168], ![64, 110, -130, -40, -387]]]
  hmulB := by decide  
  f := ![![![-279, -940, 478, 620, 1040]], ![![-31, -77, 36, 48, 80]], ![![-282, -900, 441, 580, 976]], ![![-98, -300, 134, 183, 312]], ![![-219, -750, 388, 500, 837]]]
  g := ![![![-119, -20, 26, 20, 112], ![309, 7, -26, -92, -320], ![-410, 100, -67, 220, 496], ![-2, -260, 242, -233, -168], ![437, 110, -130, -40, -387]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![-279, -940, 478, 620, 1040]] ![![-5, -20, 26, 20, 112]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 1, -2, -2, -5]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![1, 1, -2, -2, -5]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![5, 1, 1, 0, 0], ![66, 37, 0, 1, 0], ![14, 13, 0, 0, 1]] where
  M :=![![![1, 1, -2, -2, -5], ![4, 6, -4, -2, 1], ![4, 15, -7, -18, -29], ![16, 25, -14, -5, -21], ![-4, -9, 6, 6, 20]]]
  hmulB := by decide  
  f := ![![![79, -51, 12, 26, 67]], ![![-52, 16, -2, -6, -23]], ![![5, -4, 1, 2, 5]], ![![46, -39, 10, 21, 50]], ![![6, -7, 2, 4, 9]]]
  g := ![![![3, 2, -2, -2, -5], ![2, 1, -4, -2, 1], ![23, 15, -7, -18, -29], ![10, 7, -14, -5, -21], ![-10, -7, 6, 6, 20]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [58, 65, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 70], [0, 1]]
 g := ![![[66, 60], [3, 24], [12, 24], [5], [36], [1]], ![[0, 11], [5, 47], [14, 47], [5], [36], [1]]]
 h' := ![![[6, 70], [39, 29], [14, 33], [69, 33], [69, 17], [13, 6], [0, 1]], ![[0, 1], [0, 42], [70, 38], [54, 38], [29, 54], [49, 65], [6, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [63, 50]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [58, 65, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-650762, -1208302, 161371, 385588, 49179]
  a := ![188, 438, -436, -500, -1125]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-388661, -229236, 161371, 385588, 49179]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 9, 0, 20, 61]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![3, 9, 0, 20, 61]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![52, 59, 1, 0, 0], ![2, 31, 0, 1, 0], ![25, 54, 0, 0, 1]] where
  M :=![![![3, 9, 0, 20, 61], ![-40, -36, 28, -42, -65], ![84, 105, -111, 18, -179], ![-60, -145, 178, 95, 645], ![-40, 9, -30, -98, -346]]]
  hmulB := by decide  
  f := ![![![181, 381, -198, -252, -407]], ![![504, 1034, -418, -590, -989]], ![![568, 1173, -503, -692, -1150]], ![![234, 481, -190, -271, -456]], ![![443, 912, -386, -534, -889]]]
  g := ![![![-22, -55, 0, 20, 61], ![3, 44, 28, -42, -65], ![145, 222, -111, 18, -179], ![-361, -682, 178, 95, 645], ![146, 331, -30, -98, -346]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P1 : CertificateIrreducibleZModOfList' 71 2 2 6 [13, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [60, 70], [0, 1]]
 g := ![![[50, 9], [70, 9], [57, 9], [45], [50], [1]], ![[22, 62], [42, 62], [29, 62], [45], [50], [1]]]
 h' := ![![[60, 70], [13, 3], [40, 3], [26, 3], [16, 20], [58, 60], [0, 1]], ![[0, 1], [51, 68], [7, 68], [64, 68], [9, 51], [37, 11], [60, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [41, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N1 : CertifiedPrimeIdeal' SI71N1 71 where
  n := 2
  hpos := by decide
  P := [13, 11, 1]
  hirr := P71P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3413, -6317, 318, 1696, -1087]
  a := ![15, 36, -34, -39, -89]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![54, -267, 318, 1696, -1087]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N1 B_one_repr
lemma NI71N1 : Nat.card (O ⧸ I71N1) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N1

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, 12, 12, 6, 2]] i)))

def SI71N2: IdealEqSpanCertificate' Table ![![-3, 12, 12, 6, 2]] 
 ![![71, 0, 0, 0, 0], ![11, 1, 0, 0, 0], ![21, 0, 1, 0, 0], ![16, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  M :=![![![-3, 12, 12, 6, 2], ![-12, -31, 46, 44, 62], ![-88, -170, 129, 144, 218], ![-100, -210, 94, 127, 210], ![36, 72, -38, -48, -77]]]
  hmulB := by decide  
  f := ![![![115, 8, 44, 242, 794]], ![![11, -3, 10, 30, 108]], ![![49, 18, -3, 78, 220]], ![![12, -22, 38, 63, 262]], ![![7, 4, -2, 10, 25]]]
  g := ![![![-7, 12, 12, 6, 2], ![-25, -31, 46, 44, 62], ![-67, -170, 129, 144, 218], ![-46, -210, 94, 127, 210], ![19, 72, -38, -48, -77]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![1, 1, -2, -2, -5]] ![![3, 9, 0, 20, 61]]
  ![![115, 8, 44, 242, 794]] where
 M := ![![![115, 8, 44, 242, 794]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![115, 8, 44, 242, 794]] ![![-3, 12, 12, 6, 2]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![21, -89, 83, 56, 320]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![21, -89, 83, 56, 320]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![0, 0, 73, 0, 0], ![0, 0, 0, 73, 0], ![19, 62, 16, 2, 1]] where
  M :=![![![21, -89, 83, 56, 320], ![-112, 61, -102, -250, -928], ![500, 210, -113, 652, 1640], ![-902, -665, 589, -775, -1008], ![220, 326, -368, -46, -899]]]
  hmulB := by decide  
  f := ![![![29, 57, -25, -34, -56]], ![![68, 143, -48, -74, -128]], ![![148, 310, -73, -136, -248]], ![![62, 135, 7, -29, -72]], ![![99, 207, -63, -102, -179]]]
  g := ![![![-83, -273, -69, -8, 320], ![240, 789, 202, 22, -928], ![-420, -1390, -361, -36, 1640], ![250, 847, 229, 17, -1008], ![237, 768, 192, 24, -899]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 4 2 6 [72, 29, 52, 32, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 54, 16, 13], [56, 20, 46, 62], [49, 71, 11, 71], [0, 1]]
 g := ![![[9, 31, 24, 27], [67, 64, 9], [34, 72, 48], [52, 18, 52, 2], [1], []], ![[58, 4, 27, 0, 3, 30], [37, 16, 8], [59, 34, 64], [46, 17, 50, 33, 44, 40], [3, 51, 57], [46, 45, 23]], ![[69, 37, 33, 53, 48, 14], [38, 68, 18], [47, 36, 50], [53, 52, 64, 53, 17, 68], [5, 72, 36], [51, 7, 48]], ![[72, 18, 14, 42, 31, 61], [17, 54, 57], [39, 37, 67], [44, 4, 11, 64, 55, 12], [46, 38, 2], [23, 47, 4]]]
 h' := ![![[9, 54, 16, 13], [49, 31, 59, 10], [37, 12, 63, 70], [52, 44, 53, 62], [1, 44, 21, 41], [0, 0, 1], [0, 1]], ![[56, 20, 46, 62], [69, 31, 46, 6], [18, 14, 66, 64], [55, 24, 25, 65], [72, 38, 44, 62], [54, 48, 41, 38], [9, 54, 16, 13]], ![[49, 71, 11, 71], [35, 29, 62, 42], [56, 31, 59, 50], [70, 17, 25, 59], [46, 71, 71, 10], [48, 38, 44, 67], [56, 20, 46, 62]], ![[0, 1], [52, 55, 52, 15], [20, 16, 31, 35], [45, 61, 43, 33], [52, 66, 10, 33], [15, 60, 60, 41], [49, 71, 11, 71]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [63, 12, 10], []]
 b := ![[], [], [22, 24, 37, 54], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 4
  hpos := by decide
  P := [72, 29, 52, 32, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![33263488048, 69907913991, -37187936780, -41018842528, -105130100077]
  a := ![-69, -163, 161, 182, 415]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![27818293007, 90246220805, 22532789924, 2318374762, -105130100077]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 28398241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-29, -57, 25, 34, 56]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-29, -57, 25, 34, 56]] 
 ![![73, 0, 0, 0, 0], ![54, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![36, 0, 0, 1, 0], ![66, 0, 0, 0, 1]] where
  M :=![![![-29, -57, 25, 34, 56], ![-68, -143, 48, 74, 128], ![-148, -310, 73, 136, 248], ![-62, -135, -7, 29, 72], ![32, 68, -6, -22, -45]]]
  hmulB := by decide  
  f := ![![![-21, 89, -83, -56, -320]], ![![-14, 65, -60, -38, -224]], ![![-8, 2, -3, -12, -40]], ![![2, 53, -49, -17, -144]], ![![-22, 76, -70, -50, -277]]]
  g := ![![![-27, -57, 25, 34, 56], ![-50, -143, 48, 74, 128], ![-68, -310, 73, 136, 248], ![20, -135, -7, 29, 72], ![2, 68, -6, -22, -45]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![21, -89, 83, 56, 320]] ![![-29, -57, 25, 34, 56]]
  ![![73, 0, 0, 0, 0]] where
 M := ![![![-73, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 471, -103, -200, -368]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![229, 471, -103, -200, -368]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![0, 0, 79, 0, 0], ![0, 0, 0, 79, 0], ![67, 35, 43, 16, 1]] where
  M :=![![![229, 471, -103, -200, -368], ![400, 861, -64, -270, -560], ![540, 1190, 277, -88, -440], ![-182, -325, 639, 585, 792], ![-12, -44, -194, -142, -157]]]
  hmulB := by decide  
  f := ![![![11, -9, 3, 2, 8]], ![![-4, 9, -6, -2, -16]], ![![4, -10, 11, 12, 56]], ![![-14, 5, -9, -27, -96]], ![![7, -8, 4, 2, 11]]]
  g := ![![![315, 169, 199, 72, -368], ![480, 259, 304, 110, -560], ![380, 210, 243, 88, -440], ![-674, -355, -423, -153, 792], ![133, 69, 83, 30, -157]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 4 2 6 [67, 10, 58, 15, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [47, 76, 37, 3], [18, 5, 57, 60], [78, 76, 64, 16], [0, 1]]
 g := ![![[50, 24, 9, 13], [70, 4, 59, 26], [32, 7, 74, 64], [42, 50, 24, 67], [1], []], ![[19, 26, 44, 6, 48, 39], [18, 6, 24, 38, 12, 56], [52, 43, 17, 74, 54, 56], [48, 52, 76, 18, 65, 53], [69, 20, 21], [77, 8, 9]], ![[47, 58, 26, 30, 39, 6], [18, 14, 23, 77, 23, 56], [14, 1, 60, 29, 27, 7], [22, 51, 78, 22, 9, 77], [24, 67, 16], [9, 3, 45]], ![[34, 59, 15, 10, 18, 49], [74, 23, 68, 28, 14, 11], [64, 16, 70, 23, 9, 23], [27, 22, 12, 0, 34, 11], [43, 42, 36], [74, 25, 19]]]
 h' := ![![[47, 76, 37, 3], [50, 22, 12, 48], [68, 32, 74, 42], [30, 8, 35, 8], [12, 69, 21, 64], [0, 0, 1], [0, 1]], ![[18, 5, 57, 60], [50, 7, 28, 31], [39, 3, 49, 19], [1, 27, 66, 19], [56, 61, 68, 26], [52, 71, 76, 10], [47, 76, 37, 3]], ![[78, 76, 64, 16], [17, 60, 56, 61], [21, 0, 72, 41], [20, 29, 40, 46], [77, 13, 47, 45], [37, 47, 11, 75], [18, 5, 57, 60]], ![[0, 1], [31, 69, 62, 18], [15, 44, 42, 56], [11, 15, 17, 6], [47, 15, 22, 23], [20, 40, 70, 73], [78, 76, 64, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [12, 29, 1], []]
 b := ![[], [], [30, 6, 69, 25], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 4
  hpos := by decide
  P := [67, 10, 58, 15, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![53589315, 82317825, -53886984, -12288530, -109410739]
  a := ![14, 35, -31, -34, -85]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![93469732, 49515110, 58870567, 22003586, -109410739]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 38950081 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11, 9, -3, -2, -8]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![-11, 9, -3, -2, -8]] 
 ![![79, 0, 0, 0, 0], ![50, 1, 0, 0, 0], ![28, 0, 1, 0, 0], ![76, 0, 0, 1, 0], ![38, 0, 0, 0, 1]] where
  M :=![![![-11, 9, -3, -2, -8], ![4, -9, 6, 2, 16], ![-4, 10, -11, -12, -56], ![14, -5, 9, 27, 96], ![-8, -6, 4, -10, -21]]]
  hmulB := by decide  
  f := ![![![-229, -471, 103, 200, 368]], ![![-150, -309, 66, 130, 240]], ![![-88, -182, 33, 72, 136]], ![![-218, -449, 91, 185, 344]], ![![-110, -226, 52, 98, 179]]]
  g := ![![![1, 9, -3, -2, -8], ![-6, -9, 6, 2, 16], ![36, 10, -11, -12, -56], ![-72, -5, 9, 27, 96], ![22, -6, 4, -10, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![229, 471, -103, -200, -368]] ![![-11, 9, -3, -2, -8]]
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

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, 1, -7, -18, -68]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-3, 1, -7, -18, -68]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![27, 23, 1, 0, 0], ![8, 28, 0, 1, 0], ![22, 61, 0, 0, 1]] where
  M :=![![![-3, 1, -7, -18, -68], ![36, 19, -10, 50, 124], ![-100, -90, 85, -68, -20], ![118, 155, -171, 3, -348], ![8, -34, 52, 70, 311]]]
  hmulB := by decide  
  f := ![![![39, 37, -81, -72, -92]], ![![144, 307, -240, -266, -404]], ![![59, 110, -100, -106, -156]], ![![58, 119, -93, -103, -156]], ![![114, 231, -196, -212, -317]]]
  g := ![![![22, 58, -7, -18, -68], ![-34, -105, -10, 50, 124], ![-17, 13, 85, -68, -20], ![149, 304, -171, 3, -348], ![-106, -267, 52, 70, 311]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [70, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [69, 82], [0, 1]]
 g := ![![[50, 51], [26, 51], [21], [4], [46, 30], [1]], ![[0, 32], [59, 32], [21], [4], [41, 53], [1]]]
 h' := ![![[69, 82], [6, 36], [22, 47], [9, 42], [17, 81], [13, 69], [0, 1]], ![[0, 1], [0, 47], [28, 36], [2, 41], [45, 2], [43, 14], [69, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [14, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [70, 14, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3562, -7300, 2316, 3200, 6192]
  a := ![8, 20, -22, -30, -48]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2746, -6360, 2316, 3200, 6192]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, 16, -12, -14, -24]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-5, 16, -12, -14, -24]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![80, 50, 1, 0, 0], ![35, 10, 0, 1, 0], ![47, 10, 0, 0, 1]] where
  M :=![![![-5, 16, -12, -14, -24], ![28, 41, -28, -32, -48], ![64, 140, -67, -88, -144], ![56, 110, -34, -55, -96], ![-20, -44, 16, 24, 41]]]
  hmulB := by decide  
  f := ![![![9, 12, -8, 14, 24]], ![![-28, -37, 36, -8, 48]], ![![-8, -10, 13, 8, 48]], ![![1, 0, 2, 7, 24]], ![![1, 2, 0, 6, 17]]]
  g := ![![![31, 12, -12, -14, -24], ![68, 27, -28, -32, -48], ![184, 70, -67, -88, -144], ![111, 40, -34, -55, -96], ![-49, -18, 16, 24, 41]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P1 : CertificateIrreducibleZModOfList' 83 2 2 6 [32, 64, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 82], [0, 1]]
 g := ![![[2, 75], [32, 81], [28], [36], [82, 29], [1]], ![[16, 8], [77, 2], [28], [36], [52, 54], [1]]]
 h' := ![![[19, 82], [55, 18], [50, 9], [38, 51], [32, 77], [51, 19], [0, 1]], ![[0, 1], [65, 65], [55, 74], [11, 32], [1, 6], [80, 64], [19, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [4, 52]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N1 : CertifiedPrimeIdeal' SI83N1 83 where
  n := 2
  hpos := by decide
  P := [32, 64, 1]
  hirr := P83P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2721, 5580, -4118, -3068, -12968]
  a := ![15, 37, -20, -24, -77]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![12639, 4480, -4118, -3068, -12968]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N1 B_one_repr
lemma NI83N1 : Nat.card (O ⧸ I83N1) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N1

def I83N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -5, 1, 2, 4]] i)))

def SI83N2: IdealEqSpanCertificate' Table ![![-1, -5, 1, 2, 4]] 
 ![![83, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![66, 0, 1, 0, 0], ![52, 0, 0, 1, 0], ![32, 0, 0, 0, 1]] where
  M :=![![![-1, -5, 1, 2, 4], ![-4, -7, 0, 2, 4], ![-4, -10, -3, 0, 4], ![2, 5, -7, -7, -12], ![0, 0, 2, 2, 3]]]
  hmulB := by decide  
  f := ![![![53, -25, -1, 16, 28]], ![![6, -3, 0, 2, 4]], ![![42, -20, -1, 12, 20]], ![![34, -15, -1, 11, 20]], ![![20, -10, 0, 6, 11]]]
  g := ![![![-3, -5, 1, 2, 4], ![-2, -7, 0, 2, 4], ![2, -10, -3, 0, 4], ![14, 5, -7, -7, -12], ![-4, 0, 2, 2, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N2 : Nat.card (O ⧸ I83N2) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N2)

lemma isPrimeI83N2 : Ideal.IsPrime I83N2 := prime_ideal_of_norm_prime hp83.out _ NI83N2
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-3, 1, -7, -18, -68]] ![![-5, 16, -12, -14, -24]]
  ![![-53, 25, 1, -16, -28]] where
 M := ![![![-53, 25, 1, -16, -28]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI83N1 : IdealMulLeCertificate' Table 
  ![![-53, 25, 1, -16, -28]] ![![-1, -5, 1, 2, 4]]
  ![![83, 0, 0, 0, 0]] where
 M := ![![![-83, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 13, -9, -6, -16]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![7, 13, -9, -6, -16]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![0, 0, 89, 0, 0], ![57, 15, 52, 1, 0], ![6, 77, 20, 0, 1]] where
  M :=![![![7, 13, -9, -6, -16], ![12, 21, -4, -10, 8], ![20, 70, -31, -64, -160], ![54, 55, -13, 33, 96], ![-24, -32, 18, -2, 15]]]
  hmulB := by decide  
  f := ![![![-113, 63, -13, -32, -88]], ![![64, -41, 10, 22, 56]], ![![-44, 10, 1, -4, -16]], ![![-87, 39, -6, -19, -56]], ![![38, -29, 8, 16, 39]]]
  g := ![![![5, 15, 7, -6, -16], ![6, -5, 4, -10, 8], ![52, 150, 73, -64, -160], ![-27, -88, -41, 33, 96], ![0, -13, -2, -2, 15]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [18, 54, 77, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 59, 46], [84, 29, 43], [0, 1]]
 g := ![![[4, 38, 57], [62, 1], [2, 84], [46, 59, 71], [1, 12, 1], []], ![[15, 81, 2, 31], [6, 39], [79, 22], [9, 11, 14, 62], [8, 76, 88, 60], [26, 69]], ![[18, 41, 52, 27], [73, 84], [43, 87], [79, 12], [5, 31, 38, 74], [29, 69]]]
 h' := ![![[17, 59, 46], [46, 76, 18], [70, 64, 88], [62, 71, 23], [71, 86, 58], [0, 0, 1], [0, 1]], ![[84, 29, 43], [74, 84, 13], [2, 55, 67], [0, 60, 17], [51, 83, 31], [88, 72, 29], [17, 59, 46]], ![[0, 1], [65, 18, 58], [69, 59, 23], [24, 47, 49], [7, 9], [37, 17, 59], [84, 29, 43]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 29], []]
 b := ![[], [46, 13, 40], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [18, 54, 77, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-69654, -118622, 65606, 58900, 67594]
  a := ![5, 11, -13, -16, -31]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-43062, -69740, -48866, 58900, 67594]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 704969 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-113, 63, -13, -32, -88]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![-113, 63, -13, -32, -88]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![72, 75, 1, 0, 0], ![23, 34, 0, 1, 0], ![46, 79, 0, 0, 1]] where
  M :=![![![-113, 63, -13, -32, -88], ![64, -41, 10, 22, 56], ![-44, 10, 1, -4, -16], ![26, -25, 5, 11, 24], ![12, -2, 0, 2, 7]]]
  hmulB := by decide  
  f := ![![![7, 13, -9, -6, -16]], ![![12, 21, -4, -10, 8]], ![![16, 29, -11, -14, -8]], ![![7, 12, -4, -5, 0]], ![![14, 25, -8, -12, -1]]]
  g := ![![![63, 102, -13, -32, -88], ![-42, -67, 10, 22, 56], ![8, 15, 1, -4, -16], ![-19, -30, 5, 11, 24], ![-4, -7, 0, 2, 7]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P1 : CertificateIrreducibleZModOfList' 89 2 2 6 [19, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [84, 88], [0, 1]]
 g := ![![[19, 47], [55], [21], [41, 36], [65, 25], [1]], ![[51, 42], [55], [21], [39, 53], [29, 64], [1]]]
 h' := ![![[84, 88], [39, 74], [85, 12], [22, 33], [11, 6], [70, 84], [0, 1]], ![[0, 1], [25, 15], [25, 77], [35, 56], [70, 83], [6, 5], [84, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [35, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N1 : CertifiedPrimeIdeal' SI89N1 89 where
  n := 2
  hpos := by decide
  P := [19, 5, 1]
  hirr := P89P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-247, -1205, 124, 1294, 1365]
  a := ![-6, -15, 18, 14, 39]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1143, -1824, 124, 1294, 1365]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N1 B_one_repr
lemma NI89N1 : Nat.card (O ⧸ I89N1) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![7, 13, -9, -6, -16]] ![![-113, 63, -13, -32, -88]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-89, 47, -8, -26, -65]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![-89, 47, -8, -26, -65]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![16, 3, 1, 0, 0], ![65, 2, 0, 1, 0], ![51, 19, 0, 0, 1]] where
  M :=![![![-89, 47, -8, -26, -65], ![52, -24, 0, 10, 13], ![-20, 15, 3, 14, 55], ![-4, -25, 8, -31, -81], ![20, 7, -10, 10, 6]]]
  hmulB := by decide  
  f := ![![![95, 201, -50, -90, -163]], ![![180, 382, -46, -134, -265]], ![![24, 51, -9, -20, -38]], ![![67, 142, -32, -61, -112]], ![![85, 180, -36, -74, -138]]]
  g := ![![![52, 14, -8, -26, -65], ![-13, -3, 0, 10, 13], ![-39, -11, 3, 14, 55], ![62, 16, 8, -31, -81], ![-8, -1, -10, 10, 6]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [32, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [78, 96], [0, 1]]
 g := ![![[40, 94], [62], [75], [79], [86], [78, 1]], ![[0, 3], [62], [75], [79], [86], [59, 96]]]
 h' := ![![[78, 96], [88, 71], [36, 16], [60, 50], [58, 51], [26, 38], [0, 1]], ![[0, 1], [0, 26], [23, 81], [80, 47], [59, 46], [80, 59], [78, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77]]
 b := ![[], [2, 87]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [32, 19, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1700, -3397, 448, 1406, 307]
  a := ![-11, -27, 25, 28, 67]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1195, -138, 448, 1406, 307]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-41, -9, 4, 4, -1]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![-41, -9, 4, 4, -1]] 
 ![![97, 0, 0, 0, 0], ![52, 1, 0, 0, 0], ![12, 0, 1, 0, 0], ![70, 0, 0, 1, 0], ![95, 0, 0, 0, 1]] where
  M :=![![![-41, -9, 4, 4, -1], ![-8, -62, 12, 26, 53], ![-52, -85, 1, 22, 47], ![4, -15, -22, -13, -9], ![8, 11, 6, 2, 0]]]
  hmulB := by decide  
  f := ![![![15, -103, 154, 196, 889]], ![![4, -56, 82, 98, 455]], ![![16, -3, 11, 38, 133]], ![![-10, -95, 132, 131, 655]], ![![17, -94, 142, 186, 835]]]
  g := ![![![2, -9, 4, 4, -1], ![-39, -62, 12, 26, 53], ![-17, -85, 1, 22, 47], ![29, -15, -22, -13, -9], ![-8, 11, 6, 2, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1

def I97N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 2, -1, 0, -1]] i)))

def SI97N2: IdealEqSpanCertificate' Table ![![-1, 2, -1, 0, -1]] 
 ![![97, 0, 0, 0, 0], ![63, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![35, 0, 0, 1, 0], ![22, 0, 0, 0, 1]] where
  M :=![![![-1, 2, -1, 0, -1], ![0, -2, 2, 0, 5], ![0, 5, -5, -6, -25], ![6, 0, 3, 11, 39], ![-4, -3, 2, -4, -8]]]
  hmulB := by decide  
  f := ![![![-65, -46, 37, 38, 49]], ![![-43, -32, 25, 26, 34]], ![![-8, -9, 5, 6, 9]], ![![-25, -20, 14, 15, 20]], ![![-14, -9, 8, 8, 10]]]
  g := ![![![-1, 2, -1, 0, -1], ![0, -2, 2, 0, 5], ![5, 5, -5, -6, -25], ![-13, 0, 3, 11, 39], ![5, -3, 2, -4, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N2 : Nat.card (O ⧸ I97N2) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N2)

lemma isPrimeI97N2 : Ideal.IsPrime I97N2 := prime_ideal_of_norm_prime hp97.out _ NI97N2

def I97N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-21, 18, -8, -12, -26]] i)))

def SI97N3: IdealEqSpanCertificate' Table ![![-21, 18, -8, -12, -26]] 
 ![![97, 0, 0, 0, 0], ![76, 1, 0, 0, 0], ![44, 0, 1, 0, 0], ![52, 0, 0, 1, 0], ![42, 0, 0, 0, 1]] where
  M :=![![![-21, 18, -8, -12, -26], ![24, 13, -12, -12, -14], ![24, 70, -33, -44, -74], ![32, 50, -16, -25, -42], ![-8, -22, 8, 12, 21]]]
  hmulB := by decide  
  f := ![![![99, 86, -80, 76, 50]], ![![76, 65, -60, 60, 46]], ![![44, 42, -41, 28, -6]], ![![60, 46, -40, 55, 74]], ![![38, 34, -32, 28, 13]]]
  g := ![![![7, 18, -8, -12, -26], ![8, 13, -12, -12, -14], ![16, 70, -33, -44, -74], ![0, 50, -16, -25, -42], ![-2, -22, 8, 12, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N3 : Nat.card (O ⧸ I97N3) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N3)

lemma isPrimeI97N3 : Ideal.IsPrime I97N3 := prime_ideal_of_norm_prime hp97.out _ NI97N3
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![-89, 47, -8, -26, -65]] ![![-41, -9, 4, 4, -1]]
  ![![3065, -1758, 382, 898, 2438]] where
 M := ![![![3065, -1758, 382, 898, 2438]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI97N1 : IdealMulLeCertificate' Table 
  ![![3065, -1758, 382, 898, 2438]] ![![-1, 2, -1, 0, -1]]
  ![![-7429, 4242, -921, -2166, -5887]] where
 M := ![![![-7429, 4242, -921, -2166, -5887]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI97N2 : IdealMulLeCertificate' Table 
  ![![-7429, 4242, -921, -2166, -5887]] ![![-21, 18, -8, -12, -26]]
  ![![97, 0, 0, 0, 0]] where
 M := ![![![213497, -121832, 26481, 62274, 169265]]]
 hmul := by decide  
 g := ![![![![2201, -1256, 273, 642, 1745]]]]
 hle2 := by decide  


def PBC97 : ContainsPrimesAboveP 97 ![I97N0, I97N1, I97N2, I97N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
    exact isPrimeI97N1
    exact isPrimeI97N2
    exact isPrimeI97N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 97 (by decide) (𝕀 ⊙ MulI97N0 ⊙ MulI97N1 ⊙ MulI97N2)
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


def P101P0 : CertificateIrreducibleZModOfList' 101 5 2 6 [26, 87, 54, 21, 51, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [95, 51, 53, 71, 97], [28, 5, 78, 52, 39], [72, 52, 89, 21, 29], [57, 93, 83, 58, 37], [0, 1]]
 g := ![![[8, 32, 44, 68, 14], [86, 12, 0, 13], [36, 64, 91, 50, 47], [50, 61, 15, 96], [50, 1], []], ![[70, 32, 9, 55, 94, 37, 80, 88], [61, 65, 41, 100], [81, 3, 37, 2, 44, 75, 85, 70], [7, 84, 45, 14], [90, 7, 46, 71], [60, 35, 38, 28, 44, 54, 6, 37]], ![[30, 3, 65, 75, 72, 85, 59, 32], [91, 51, 91, 30], [58, 76, 86, 85, 13, 50, 4, 39], [30, 52, 50, 78], [47, 97, 80, 71], [84, 60, 84, 30, 20, 5, 11, 32]], ![[8, 93, 67, 21, 100, 80, 45, 35], [38, 0, 82, 49], [58, 8, 76, 48, 49, 32, 11, 41], [93, 6, 79, 85], [29, 38, 10, 21], [39, 81, 77, 90, 36, 46, 35, 48]], ![[5, 7, 56, 77, 36, 62, 97, 85], [15, 78, 87, 97], [32, 77, 59, 63, 38, 41, 40, 33], [60, 62, 34, 13], [9, 35, 66, 13], [52, 90, 18, 63, 79, 21, 22, 52]]]
 h' := ![![[95, 51, 53, 71, 97], [8, 17, 38, 73, 69], [74, 48, 90, 34, 35], [81, 74, 20, 37, 59], [13, 68, 41, 7, 55], [0, 0, 0, 1], [0, 1]], ![[28, 5, 78, 52, 39], [46, 32, 71, 51, 33], [97, 43, 94, 51, 91], [11, 33, 36, 37, 72], [30, 37, 53, 56, 69], [42, 85, 12, 73, 77], [95, 51, 53, 71, 97]], ![[72, 52, 89, 21, 29], [4, 75, 77, 45, 62], [42, 46, 7, 81, 63], [73, 74, 70, 80, 100], [67, 6, 95, 97, 52], [73, 64, 98, 26, 77], [28, 5, 78, 52, 39]], ![[57, 93, 83, 58, 37], [8, 34, 17, 20, 89], [17, 21, 69, 97, 94], [58, 48, 89, 72, 61], [31, 67, 19, 13, 61], [49, 53, 61, 85, 83], [72, 52, 89, 21, 29]], ![[0, 1], [90, 44, 100, 13, 50], [51, 44, 43, 40, 20], [81, 74, 88, 77, 11], [5, 24, 95, 29, 66], [21, 0, 31, 17, 66], [57, 93, 83, 58, 37]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [99, 6, 33, 55], [], [], []]
 b := ![[], [8, 30, 95, 13, 39], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 5
  hpos := by decide
  P := [26, 87, 54, 21, 51, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6036770, 12152825, -16854173, -17285140, -24543808]
  a := ![0, 0, 4, 5, 4]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![59770, 120325, -166873, -171140, -243008]
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



lemma PB103I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 102 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 102 (by omega)

def PB103I2 : PrimesBelowBoundCertificateInterval O 61 102 103 where
  m := 8
  g := ![2, 3, 2, 2, 3, 2, 4, 1]
  P := ![67, 71, 73, 79, 83, 89, 97, 101]
  hP := PB103I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1, I71N2]
    · exact ![I73N0, I73N1]
    · exact ![I79N0, I79N1]
    · exact ![I83N0, I83N1, I83N2]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1, I97N2, I97N3]
    · exact ![I101N0]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![20151121, 67]
    · exact ![5041, 5041, 71]
    · exact ![28398241, 73]
    · exact ![38950081, 79]
    · exact ![6889, 6889, 83]
    · exact ![704969, 7921]
    · exact ![9409, 97, 97, 97]
    · exact ![10510100501]
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
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
      exact NI83N1
      exact NI83N2
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
      exact NI97N2
      exact NI97N3
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
  β := ![I67N1, I71N2, I73N1, I79N1, I83N2, I97N1, I97N2, I97N3]
  Il := ![[I67N1], [I71N2], [I73N1], [I79N1], [I83N2], [], [I97N1, I97N2, I97N3], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
