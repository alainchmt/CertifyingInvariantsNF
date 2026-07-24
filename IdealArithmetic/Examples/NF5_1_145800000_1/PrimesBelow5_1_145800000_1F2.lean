
import IdealArithmetic.Examples.NF5_1_145800000_1.RI5_1_145800000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4064, 1006, 45, 477, 303]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![-4064, 1006, 45, 477, 303]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![21, 15, 1, 0, 0], ![48, 0, 0, 1, 0], ![45, 42, 0, 0, 1]] where
  M :=![![![-4064, 1006, 45, 477, 303], ![3636, -4361, 1786, -1548, 1908], ![22896, 1722, -4001, -732, -6192], ![-14202, 6970, -1760, 2965, -1442], ![-10959, -2388, 2677, 93, 4036]]]
  hmulB := by decide  
  f := ![![![12378053386, 6129106712, 3920443531, 2084502477, 2932694037]], ![![35192328444, 17425804345, 11146303226, 5926496964, 8338009908]], ![![13251942786, 6561821067, 4197226474, 2231668155, 3139741959]], ![![9312871254, 4611353654, 2949622588, 1568316325, 2206469882]], ![![30186128211, 14946938364, 9560712608, 5083437360, 7151906317]]]
  g := ![![![-620, -185, 45, 477, 303], ![-678, -1661, 1786, -1548, 1908], ![6279, 4803, -4001, -732, -6192], ![-816, 1402, -1760, 2965, -1442], ![-3780, -3165, 2677, 93, 4036]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [8, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 66], [0, 1]]
 g := ![![[12, 16], [20, 36], [4], [36], [37], [1]], ![[17, 51], [48, 31], [4], [36], [37], [1]]]
 h' := ![![[38, 66], [41, 63], [44, 6], [3, 65], [36, 61], [59, 38], [0, 1]], ![[0, 1], [23, 4], [4, 61], [61, 2], [9, 6], [29, 29], [38, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [21, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [8, 29, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2705, -3259, 2440, -1641, 4805]
  a := ![0, -8, -9, -4, -23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2776, -3607, 2440, -1641, 4805]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 11, 7, 4, 6]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![11, 11, 7, 4, 6]] 
 ![![67, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![58, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![16, 0, 0, 0, 1]] where
  M :=![![![11, 11, 7, 4, 6], ![72, 18, 21, 6, 16], ![192, 93, 40, 30, 24], ![12, 36, 14, 13, 12], ![-30, -20, 0, -6, 3]]]
  hmulB := by decide  
  f := ![![![221, -87, 35, -80, 62]], ![![21, -3, 0, -6, -2]], ![![134, -57, 24, -50, 44]], ![![-15, -9, 7, 1, 18]], ![![110, -38, 14, -38, 23]]]
  g := ![![![-8, 11, 7, 4, 6], ![-22, 18, 21, 6, 16], ![-43, 93, 40, 30, 24], ![-17, 36, 14, 13, 12], ![0, -20, 0, -6, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1

def I67N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-961410785, -476051372, -304503186, -161904550, -227784094]] i)))

def SI67N2: IdealEqSpanCertificate' Table ![![-961410785, -476051372, -304503186, -161904550, -227784094]] 
 ![![67, 0, 0, 0, 0], ![55, 1, 0, 0, 0], ![57, 0, 1, 0, 0], ![53, 0, 0, 1, 0], ![64, 0, 0, 0, 1]] where
  M :=![![![-961410785, -476051372, -304503186, -161904550, -227784094], ![-2733409128, -1353472611, -865740016, -460314552, -647618200], ![-7771418400, -3848089128, -2461405363, -1308730896, -1841258208], ![-2315811852, -1146695488, -733476364, -389989879, -548678164], ![980172390, 485341352, 310445462, 165064062, 232229223]]]
  hmulB := by decide  
  f := ![![![30529, 4860, -5722, -6166, -16438]], ![![22117, 4833, -4962, -4102, -13862]], ![![21555, 2460, -3433, -4626, -10146]], ![![33299, 1588, -3930, -7761, -12406]], ![![32794, 6416, -6894, -6286, -19453]]]
  g := ![![![981152529, -476051372, -304503186, -161904550, -227784094], ![2789537335, -1353472611, -865740016, -460314552, -647618200], ![7930997793, -3848089128, -2461405363, -1308730896, -1841258208], ![2363365057, -1146695488, -733476364, -389989879, -548678164], ![-1000299386, 485341352, 310445462, 165064062, 232229223]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N2 : Nat.card (O ⧸ I67N2) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N2)

lemma isPrimeI67N2 : Ideal.IsPrime I67N2 := prime_ideal_of_norm_prime hp67.out _ NI67N2

def I67N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-404, -147, 132, -31, 171]] i)))

def SI67N3: IdealEqSpanCertificate' Table ![![-404, -147, 132, -31, 171]] 
 ![![67, 0, 0, 0, 0], ![61, 1, 0, 0, 0], ![31, 0, 1, 0, 0], ![34, 0, 0, 1, 0], ![28, 0, 0, 0, 1]] where
  M :=![![![-404, -147, 132, -31, 171], ![2052, -552, -7, -234, -124], ![-1488, 2169, -910, 702, -936], ![-2898, 158, 326, 143, 530], ![1449, -1246, 437, -423, 408]]]
  hmulB := by decide  
  f := ![![![-314, 1153, -694, 401, -1631]], ![![-578, 1093, -633, 449, -1461]], ![![142, 250, -170, 35, -419]], ![![658, 494, -368, -23, -940]], ![![-467, 762, -435, 329, -998]]]
  g := ![![![11, -147, 132, -31, 171], ![707, -552, -7, -234, -124], ![-1541, 2169, -910, 702, -936], ![-632, 158, 326, 143, 530], ![998, -1246, 437, -423, 408]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N3 : Nat.card (O ⧸ I67N3) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N3)

lemma isPrimeI67N3 : Ideal.IsPrime I67N3 := prime_ideal_of_norm_prime hp67.out _ NI67N3
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![-4064, 1006, 45, 477, 303]] ![![11, 11, 7, 4, 6]]
  ![![33002, -11299, 1156, -4487, -575]] where
 M := ![![![33002, -11299, 1156, -4487, -575]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![33002, -11299, 1156, -4487, -575]] ![![-961410785, -476051372, -304503186, -161904550, -227784094]]
  ![![-4024, -1767, 1402, -405, 1807]] where
 M := ![![![-4024, -1767, 1402, -405, 1807]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI67N2 : IdealMulLeCertificate' Table 
  ![![-4024, -1767, 1402, -405, 1807]] ![![-404, -147, 132, -31, 171]]
  ![![67, 0, 0, 0, 0]] where
 M := ![![![-294331, 2292338, -1136990, 700150, -1258662]]]
 hmul := by decide  
 g := ![![![![-4393, 34214, -16970, 10450, -18786]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1, I67N2, I67N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
    exact isPrimeI67N2
    exact isPrimeI67N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0 ⊙ MulI67N1 ⊙ MulI67N2)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0, 0, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0, 0, 0]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![0, 0, 0, 71, 0], ![0, 0, 0, 0, 71]] where
  M :=![![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![0, 0, 0, 71, 0], ![0, 0, 0, 0, 71]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 5 2 6 [41, 46, 69, 29, 8, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 61, 12, 7, 34], [16, 31, 47, 46, 16], [3, 28, 27, 18, 66], [44, 21, 56, 0, 26], [0, 1]]
 g := ![![[0, 37, 6, 10, 5], [38, 45, 35, 10, 64], [19, 45, 69, 46, 1], [25, 35, 63, 1], [], []], ![[10, 34, 53, 58, 48, 10, 57, 42], [44, 0, 37, 8, 6, 52, 55, 70], [38, 48, 10, 17, 60, 21, 27, 65], [56, 47, 23, 32], [61, 13, 33, 9], [1, 29, 32, 20]], ![[60, 64, 48, 54, 29, 46, 12, 45], [38, 1, 33, 50, 20, 33, 27, 36], [4, 58, 11, 53, 15, 9, 21, 18], [55, 23, 9, 15], [42, 60, 0, 25], [54, 23, 63, 43]], ![[38, 69, 28, 47, 41, 25, 44, 67], [1, 3, 13, 11, 6, 14, 19, 21], [19, 12, 13, 19, 15, 21, 22, 46], [29, 44, 50, 1], [53, 6, 51, 8], [52, 26, 46, 25]], ![[16, 40, 53, 23, 27, 16, 22, 52], [67, 62, 36, 53, 5, 61, 62, 11], [7, 36, 35, 19, 8, 51, 46, 69], [49, 27, 36, 4], [7, 9, 0, 37], [21, 18, 59, 37]]]
 h' := ![![[0, 61, 12, 7, 34], [4, 32, 47, 57, 54], [2, 17, 61, 65, 63], [40, 42, 46, 27, 1], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[16, 31, 47, 46, 16], [42, 17, 18, 67, 55], [4, 42, 19, 67, 41], [6, 29, 50, 20, 2], [32, 22, 30, 14, 48], [30, 43, 12, 53, 3], [0, 61, 12, 7, 34]], ![[3, 28, 27, 18, 66], [16, 40, 33, 59, 66], [57, 22, 67, 20, 34], [65, 53, 46, 15, 9], [30, 28, 70, 69, 21], [30, 50, 68, 51, 66], [16, 31, 47, 46, 16]], ![[44, 21, 56, 0, 26], [45, 60, 11, 15, 50], [17, 67, 61, 37, 9], [54, 27, 62, 40, 17], [6, 33, 42, 42, 70], [7, 47, 27, 5, 47], [3, 28, 27, 18, 66]], ![[0, 1], [12, 64, 33, 15, 59], [43, 65, 5, 24, 66], [16, 62, 9, 40, 42], [26, 59, 0, 17, 2], [10, 2, 34, 33, 26], [44, 21, 56, 0, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26, 67, 67, 39], [], [], []]
 b := ![[], [68, 12, 9, 19, 26], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 5
  hpos := by decide
  P := [41, 46, 69, 29, 8, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-36235388103664066, 14373962472843847, -6094009657310947, 12815280151292075, -11090891145872610]
  a := ![3, -126, -124, -65, -310]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-510357578924846, 202450175673857, -85831121933957, 180496903539325, -156209734448910]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 1804229351 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def PBC71 : ContainsPrimesAboveP 71 ![I71N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![71, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 71 (by decide) 𝕀

instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4606, 2819, -804, 1015, -633]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![-4606, 2819, -804, 1015, -633]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![0, 0, 73, 0, 0], ![0, 0, 0, 73, 0], ![21, 11, 3, 21, 1]] where
  M :=![![![-4606, 2819, -804, 1015, -633], ![-7596, -4104, 3201, -1026, 4060], ![48720, -11199, -1070, -5154, -4104], ![-4410, 10830, -5010, 3547, -5466], ![-26679, 3952, 1695, 2229, 3558]]]
  hmulB := by decide  
  f := ![![![825668, 408837, 261510, 139045, 195623]], ![![2347476, 1162374, 743505, 395322, 556180]], ![![6674160, 3304773, 2113876, 1123950, 1581288]], ![![1988838, 984792, 629916, 334927, 471210]], ![![1426131, 706162, 451692, 240165, 337889]]]
  g := ![![![119, 134, 15, 196, -633], ![-1272, -668, -123, -1182, 4060], ![1848, 465, 154, 1110, -4104], ![1512, 972, 156, 1621, -5466], ![-1389, -482, -123, -993, 3558]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 4 2 6 [2, 16, 53, 25, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 32, 66, 50], [70, 11, 33, 65], [38, 29, 47, 31], [0, 1]]
 g := ![![[30, 24, 23, 65], [17, 9, 48], [1, 42, 38], [52, 12, 19, 41], [1], []], ![[5, 72, 72, 7, 23, 23], [14, 52, 38], [59, 16, 54], [2, 9, 69, 60, 20, 61], [8, 56, 50], [20, 18, 18]], ![[45, 67, 2, 8, 42, 23], [68, 65, 50], [4, 49, 65], [63, 59, 44, 21, 13, 16], [58, 28, 19], [59, 62, 64]], ![[12, 57, 36, 68, 68, 53], [4, 31, 19], [25, 6, 64], [5, 41, 60, 54, 44, 20], [41, 17, 71], [71, 59, 12]]]
 h' := ![![[13, 32, 66, 50], [66, 70, 10, 24], [10, 18, 45, 11], [42, 24, 71, 44], [71, 57, 20, 48], [0, 0, 1], [0, 1]], ![[70, 11, 33, 65], [13, 51, 66, 27], [25, 47, 50, 29], [17, 58, 46, 45], [54, 1, 56, 65], [56, 38, 42, 59], [13, 32, 66, 50]], ![[38, 29, 47, 31], [58, 18, 13, 39], [11, 23, 13, 59], [26, 19, 29, 49], [12, 72, 61, 12], [37, 34, 56, 26], [70, 11, 33, 65]], ![[0, 1], [69, 7, 57, 56], [71, 58, 38, 47], [62, 45, 0, 8], [62, 16, 9, 21], [61, 1, 47, 61], [38, 29, 47, 31]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [38, 39, 8], []]
 b := ![[], [], [25, 20, 34, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 4
  hpos := by decide
  P := [2, 16, 53, 25, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![283552666, -148730391, 72868382, -108808318, 145720386]
  a := ![1, -9, -9, -5, -23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-38035280, -23995269, -4990312, -43410088, 145720386]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 28398241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-825668, -408837, -261510, -139045, -195623]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-825668, -408837, -261510, -139045, -195623]] 
 ![![73, 0, 0, 0, 0], ![62, 1, 0, 0, 0], ![25, 0, 1, 0, 0], ![27, 0, 0, 1, 0], ![16, 0, 0, 0, 1]] where
  M :=![![![-825668, -408837, -261510, -139045, -195623], ![-2347476, -1162374, -743505, -395322, -556180], ![-6674160, -3304773, -2113876, -1123950, -1581288], ![-1988838, -984792, -629916, -334927, -471210], ![841779, 416816, 266613, 141759, 199440]]]
  hmulB := by decide  
  f := ![![![4606, -2819, 804, -1015, 633]], ![![4016, -2338, 639, -848, 482]], ![![910, -812, 290, -277, 273]], ![![1764, -1191, 366, -424, 309]], ![![1375, -672, 153, -253, 90]]]
  g := ![![![519783, -408837, -261510, -139045, -195623], ![1477807, -1162374, -743505, -395322, -556180], ![4201588, -3304773, -2113876, -1123950, -1581288], ![1252035, -984792, -629916, -334927, -471210], ![-529927, 416816, 266613, 141759, 199440]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![-4606, 2819, -804, 1015, -633]] ![![-825668, -408837, -261510, -139045, -195623]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0, 0, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0, 0, 0]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![0, 0, 79, 0, 0], ![0, 0, 0, 79, 0], ![0, 0, 0, 0, 79]] where
  M :=![![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![0, 0, 79, 0, 0], ![0, 0, 0, 79, 0], ![0, 0, 0, 0, 79]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 5 2 6 [65, 22, 63, 15, 63, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [72, 7, 6, 75, 65], [64, 41, 7, 25, 56], [51, 53, 30, 1, 44], [66, 56, 36, 57, 72], [0, 1]]
 g := ![![[39, 60, 1, 33, 18], [6, 8, 36, 53, 16], [77, 3, 75, 38, 44], [63, 77, 4, 16, 1], [], []], ![[32, 13, 22, 19, 51, 5, 9, 18], [67, 1, 53, 58, 23, 70, 41, 11], [64, 74, 44, 19, 8, 53, 14, 4], [20, 42, 60, 20, 41, 56, 72, 13], [5, 48, 65, 62], [66, 54, 9, 38]], ![[8, 52, 73, 40, 12, 45, 52, 56], [2, 13, 62, 66, 8, 8, 56, 54], [6, 34, 24, 73, 47, 30, 15, 24], [7, 0, 15, 74, 67, 18, 76, 75], [49, 20, 58, 26], [24, 56, 46, 55]], ![[4, 59, 12, 30, 32, 19, 48, 38], [18, 4, 56, 49, 9, 36, 56, 20], [46, 0, 45, 38, 16, 12, 28, 64], [35, 59, 72, 19, 6, 30, 64, 55], [25, 69, 62, 23], [10, 22, 17, 40]], ![[74, 64, 16, 40, 6, 31, 63, 67], [43, 33, 26, 10, 27, 24, 41, 36], [9, 46, 22, 42, 74, 24, 2, 18], [23, 16, 32, 50, 19, 23, 34, 8], [26, 13, 74, 67], [26, 48, 65, 49]]]
 h' := ![![[72, 7, 6, 75, 65], [5, 53, 48, 53, 52], [51, 18, 54, 24, 4], [13, 8, 2, 28, 53], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[64, 41, 7, 25, 56], [10, 67, 56, 69, 22], [49, 5, 71, 36, 45], [68, 78, 6, 69, 66], [63, 46, 33, 5, 75], [25, 75, 38, 32, 46], [72, 7, 6, 75, 65]], ![[51, 53, 30, 1, 44], [33, 63, 1, 0, 78], [37, 68, 52, 17, 36], [35, 73, 14, 77, 55], [39, 50, 63, 10, 46], [8, 53, 3, 39, 42], [64, 41, 7, 25, 56]], ![[66, 56, 36, 57, 72], [28, 75, 67, 12, 37], [61, 67, 60, 68, 38], [52, 76, 1, 41, 24], [57, 11, 41, 46, 10], [55, 43, 16, 36, 55], [51, 53, 30, 1, 44]], ![[0, 1], [5, 58, 65, 24, 48], [62, 0, 0, 13, 35], [66, 2, 56, 22, 39], [53, 51, 21, 18, 26], [59, 66, 21, 51, 15], [66, 56, 36, 57, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 10, 7, 34], [], [], []]
 b := ![[], [15, 40, 19, 73, 25], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 5
  hpos := by decide
  P := [65, 22, 63, 15, 63, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![442726653400351, -133317332018094, 46346524881048, -145337572631382, 69236585569872]
  a := ![1, 44, 48, 18, 121]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![5604134853169, -1687561164786, 586664871912, -1839716109258, 876412475568]
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

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263894494, 130669780, 83582081, 44440649, 62523709]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![263894494, 130669780, 83582081, 44440649, 62523709]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![0, 0, 83, 0, 0], ![15, 58, 33, 1, 0], ![46, 42, 62, 0, 1]] where
  M :=![![![263894494, 130669780, 83582081, 44440649, 62523709], ![750284508, 371510259, 237634138, 126350232, 177762596], ![2133151152, 1056249366, 675623087, 359229252, 505400928], ![635659602, 314752684, 201329522, 107047043, 150604870], ![-269044305, -133219756, -85213157, -45307893, -63743838]]]
  hmulB := by decide  
  f := ![![![404, -102, 15, -71, 63]], ![![756, 189, -110, -288, -284]], ![![-3408, 990, -383, 1044, -1152]], ![![-786, 506, -224, 212, -635]], ![![-1901, 764, -327, 581, -954]]]
  g := ![![![-39503685, -61119080, -63366618, 44440649, 62523709], ![-112313836, -173769063, -180159090, 126350232, 177762596], ![-319322052, -494046822, -512214455, 359229252, 505400928], ![-95155061, -147221450, -152635239, 107047043, 150604870], ![40274586, 62311798, 64603196, -45307893, -63743838]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [24, 0, 77, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 81, 42], [6, 1, 41], [0, 1]]
 g := ![![[0, 25, 41], [48, 65, 27], [10, 51], [54, 12], [36, 6, 1], []], ![[62, 15, 33, 20], [71, 52, 0, 6], [68, 12], [54, 41], [23, 24, 78, 42], [41, 21]], ![[9, 33, 12, 36], [33, 77, 18, 40], [5, 17], [58, 68], [24, 54, 4, 81], [42, 21]]]
 h' := ![![[0, 81, 42], [10, 43, 37], [21, 47, 44], [26, 42, 36], [49, 22, 26], [0, 0, 1], [0, 1]], ![[6, 1, 41], [39, 24, 17], [51, 57, 26], [43, 32, 57], [29, 49, 37], [12, 77, 1], [0, 81, 42]], ![[0, 1], [77, 16, 29], [31, 62, 13], [63, 9, 73], [58, 12, 20], [24, 6, 81], [6, 1, 41]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45], []]
 b := ![[], [0, 76], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [24, 0, 77, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-15123608, 3031496, -490312, 4374880, 111384]
  a := ![-1, -7, -14, 5, -38]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1034584, -3076984, -1828520, 4374880, 111384]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 571787 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![404, -102, 15, -71, 63]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![404, -102, 15, -71, 63]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![30, 51, 1, 0, 0], ![77, 70, 0, 1, 0], ![7, 48, 0, 0, 1]] where
  M :=![![![404, -102, 15, -71, 63], ![756, 189, -110, -288, -284], ![-3408, 990, -383, 1044, -1152], ![-2682, -104, 202, 913, 838], ![3177, -1214, 535, -1143, 1272]]]
  hmulB := by decide  
  f := ![![![263894494, 130669780, 83582081, 44440649, 62523709]], ![![750284508, 371510259, 237634138, 126350232, 177762596]], ![![582102360, 288233325, 184366585, 98027838, 137915718]], ![![885246400, 438337878, 280379993, 149078232, 209738701]], ![![452914139, 224264592, 143449398, 76272142, 107307551]]]
  g := ![![![60, 13, 15, -71, 63], ![340, 477, -110, -288, -284], ![-774, 33, -383, 1044, -1152], ![-1023, -1380, 202, 913, 838], ![798, -115, 535, -1143, 1272]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P1 : CertificateIrreducibleZModOfList' 83 2 2 6 [31, 78, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 82], [0, 1]]
 g := ![![[40, 75], [27, 61], [10], [64], [64, 25], [1]], ![[0, 8], [0, 22], [10], [64], [23, 58], [1]]]
 h' := ![![[5, 82], [76, 18], [60, 71], [72, 33], [8, 8], [52, 5], [0, 1]], ![[0, 1], [0, 65], [0, 12], [71, 50], [48, 75], [77, 78], [5, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [36, 52]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N1 : CertifiedPrimeIdeal' SI83N1 83 where
  n := 2
  hpos := by decide
  P := [31, 78, 1]
  hirr := P83P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![26767, -4956, 700, -8664, -1824]
  a := ![0, -4, 8, -18, 20]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![8261, 7872, 700, -8664, -1824]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N1 B_one_repr
lemma NI83N1 : Nat.card (O ⧸ I83N1) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![263894494, 130669780, 83582081, 44440649, 62523709]] ![![404, -102, 15, -71, 63]]
  ![![83, 0, 0, 0, 0]] where
 M := ![![![83, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![26808489263057, 13274469446653, 8490928664599, 4514632513788, 6351652731706]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![26808489263057, 13274469446653, 8490928664599, 4514632513788, 6351652731706]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![0, 0, 89, 0, 0], ![48, 24, 1, 1, 0], ![17, 66, 27, 0, 1]] where
  M :=![![![26808489263057, 13274469446653, 8490928664599, 4514632513788, 6351652731706], ![76219832780472, 37740949575524, 24140754692147, 12835655597358, 18058530055152], ![216702360661824, 107302162288815, 68635135228034, 36493347821970, 51342622389432], ![64575328388628, 31975066378838, 20452644737296, 10874685039923, 15299633520404], ![-27331647799362, -13533516196278, -8656626245254, -4602734029494, -6475603071223]]]
  hmulB := by decide  
  f := ![![![1052509, -534899, 240329, -409248, 479254]], ![![5751048, -73514, -464893, -1433550, -1636992]], ![![-19643904, 7833795, -3144056, 7032594, -5734200]], ![![1736604, -228941, -11362, -491119, -185516]], ![![-1268873, 2135434, -1219929, 913260, -2804133]]]
  g := ![![![-3346876043121, -5778492035695, -1882228400059, 4514632513788, 6351652731706], ![-9515580301464, -16428963689900, -5351406880835, 12835655597358, 18058530055152], ![-27053965341720, -46709564754393, -15214708057400, 36493347821970, 51342622389432], ![-8061835094096, -13919024572202, -4533844329815, 10874685039923, 15299633520404], ![3412189189069, 5891257339464, 1918959446149, -4602734029494, -6475603071223]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [34, 83, 23, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [65, 65, 68], [1, 23, 21], [0, 1]]
 g := ![![[74, 20, 57], [35, 9], [38, 2], [81, 25, 22], [1, 66, 1], []], ![[41, 63, 19, 68], [72, 84], [51, 34], [71, 87, 57, 50], [80, 88, 35, 16], [32, 85]], ![[84, 15, 38, 16], [70, 53], [39, 55], [35, 32, 54, 25], [45, 49, 15, 81], [79, 85]]]
 h' := ![![[65, 65, 68], [52, 79, 18], [68, 70, 3], [5, 80, 25], [55, 76, 72], [0, 0, 1], [0, 1]], ![[1, 23, 21], [65, 2, 1], [56, 1, 23], [59, 14, 52], [82, 72, 60], [22, 56, 23], [65, 65, 68]], ![[0, 1], [39, 8, 70], [4, 18, 63], [66, 84, 12], [30, 30, 46], [74, 33, 65], [1, 23, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 33], []]
 b := ![[], [33, 0, 27], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [34, 83, 23, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10639251, 2683430, -731075, 3243612, -801031]
  a := ![13, -8, -13, 2, -35]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1715900, -250508, 198350, 3243612, -801031]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 704969 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![38, 1, -4, -9, -13]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![38, 1, -4, -9, -13]] 
 ![![89, 0, 0, 0, 0], ![27, 1, 0, 0, 0], ![72, 0, 1, 0, 0], ![63, 0, 0, 1, 0], ![84, 0, 0, 0, 1]] where
  M :=![![![38, 1, -4, -9, -13], ![-156, 56, -21, 54, -36], ![-432, -57, 74, 90, 216], ![510, -156, 52, -169, 78], ![381, 66, -75, -75, -214]]]
  hmulB := by decide  
  f := ![![![520, 91, 26, 21, -13]], ![![156, 35, 9, 9, -3]], ![![432, 75, 32, 18, 0]], ![![390, 63, 20, 14, -9]], ![![489, 90, 21, 21, -16]]]
  g := ![![![22, 1, -4, -9, -13], ![-6, 56, -21, 54, -36], ![-315, -57, 74, 90, 216], ![57, -156, 52, -169, 78], ![300, 66, -75, -75, -214]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1

def I89N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13870, 3904, -1201, 4491, -1629]] i)))

def SI89N2: IdealEqSpanCertificate' Table ![![-13870, 3904, -1201, 4491, -1629]] 
 ![![89, 0, 0, 0, 0], ![56, 1, 0, 0, 0], ![68, 0, 1, 0, 0], ![79, 0, 0, 1, 0], ![20, 0, 0, 0, 1]] where
  M :=![![![-13870, 3904, -1201, 4491, -1629], ![-19548, -8095, 6766, 2568, 17964], ![215568, -50574, 12437, -67188, 10272], ![30318, 29860, -21298, 881, -53774], ![-210327, 46824, -10559, 64869, -6178]]]
  hmulB := by decide  
  f := ![![![2266448023396, 1122252535150, 717841587411, 381676857537, 536982544515]], ![![1498481796004, 741987010989, 474607200362, 252348969432, 355030673292]], ![![1937516345536, 959378996662, 613660580237, 326283745560, 459049775916]], ![![2073131827418, 1026530246890, 656613443831, 349121812184, 491180734043]], ![![483351499813, 239335930246, 153089682323, 81397887633, 114518981060]]]
  g := ![![![-5315, 3904, -1201, 4491, -1629], ![-6612, -8095, 6766, 2568, 17964], ![82072, -50574, 12437, -67188, 10272], ![9127, 29860, -21298, 881, -53774], ![-79950, 46824, -10559, 64869, -6178]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N2 : Nat.card (O ⧸ I89N2) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N2)

lemma isPrimeI89N2 : Ideal.IsPrime I89N2 := prime_ideal_of_norm_prime hp89.out _ NI89N2
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![26808489263057, 13274469446653, 8490928664599, 4514632513788, 6351652731706]] ![![38, 1, -4, -9, -13]]
  ![![2266448023396, 1122252535150, 717841587411, 381676857537, 536982544515]] where
 M := ![![![2266448023396, 1122252535150, 717841587411, 381676857537, 536982544515]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI89N1 : IdealMulLeCertificate' Table 
  ![![2266448023396, 1122252535150, 717841587411, 381676857537, 536982544515]] ![![-13870, 3904, -1201, 4491, -1629]]
  ![![89, 0, 0, 0, 0]] where
 M := ![![![89, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![526, 355, 198, 123, 153]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![526, 355, 198, 123, 153]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![0, 0, 97, 0, 0], ![0, 0, 0, 97, 0], ![96, 15, 7, 94, 1]] where
  M :=![![![526, 355, 198, 123, 153], ![1836, 784, 631, 270, 492], ![5904, 2523, 1546, 834, 1080], ![1242, 964, 424, 331, 310], ![-1005, -348, -143, -105, -62]]]
  hmulB := by decide  
  f := ![![![4, -7, 4, -3, 9]], ![![108, -14, -1, -30, -12]], ![![-144, 111, -56, 66, -120]], ![![-294, 26, 10, 79, 50]], ![![-273, 23, 10, 73, 48]]]
  g := ![![![-146, -20, -9, -147, 153], ![-468, -68, -29, -474, 492], ![-1008, -141, -62, -1038, 1080], ![-294, -38, -18, -297, 310], ![51, 6, 3, 59, -62]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 4 2 6 [55, 72, 17, 81, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [88, 46, 28, 27], [53, 54, 70, 27], [69, 93, 96, 43], [0, 1]]
 g := ![![[76, 59, 17, 25], [38, 39, 65], [29, 82, 12], [41, 65, 47], [45, 16, 1], []], ![[18, 31, 79, 33, 83, 22], [74, 3, 44], [41, 89, 64], [43, 79, 79], [8, 83, 50], [13, 75, 93, 86, 95, 89]], ![[49, 79, 74, 72, 75, 32], [32, 2, 61], [66, 3, 44], [27, 11, 22], [24, 32, 93], [76, 19, 27, 49, 90, 89]], ![[81, 87, 15, 16, 47, 88], [27, 85, 3], [52, 76, 25], [33, 82, 27], [37, 84, 62], [14, 42, 55, 30, 36, 64]]]
 h' := ![![[88, 46, 28, 27], [79, 43, 49, 5], [36, 63, 58, 29], [51, 13, 70, 20], [47, 51, 65, 85], [0, 0, 0, 1], [0, 1]], ![[53, 54, 70, 27], [36, 56, 39, 28], [41, 31, 67, 23], [68, 8, 81, 8], [69, 35, 43, 46], [11, 6, 46, 27], [88, 46, 28, 27]], ![[69, 93, 96, 43], [72, 62, 67, 73], [38, 53, 72, 35], [51, 24, 30, 74], [88, 78, 11, 33], [70, 13, 43, 53], [53, 54, 70, 27]], ![[0, 1], [49, 33, 39, 88], [46, 47, 94, 10], [44, 52, 13, 92], [93, 30, 75, 30], [73, 78, 8, 16], [69, 93, 96, 43]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [76, 71, 47], []]
 b := ![[], [], [9, 52, 63, 27], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 4
  hpos := by decide
  P := [55, 72, 17, 81, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1073659, -119770, -270877, -372873, -624452]
  a := ![-1, -4, -2, -4, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![629083, 95330, 42271, 601295, -624452]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 88529281 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4, -7, 4, -3, 9]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![4, -7, 4, -3, 9]] 
 ![![97, 0, 0, 0, 0], ![12, 1, 0, 0, 0], ![50, 0, 1, 0, 0], ![88, 0, 0, 1, 0], ![60, 0, 0, 0, 1]] where
  M :=![![![4, -7, 4, -3, 9], ![108, -14, -1, -30, -12], ![-144, 111, -56, 66, -120], ![-294, 26, 10, 79, 50], ![159, -108, 53, -69, 112]]]
  hmulB := by decide  
  f := ![![![526, 355, 198, 123, 153]], ![![84, 52, 31, 18, 24]], ![![332, 209, 118, 72, 90]], ![![490, 332, 184, 115, 142]], ![![315, 216, 121, 75, 94]]]
  g := ![![![-4, -7, 4, -3, 9], ![38, -14, -1, -30, -12], ![28, 111, -56, 66, -120], ![-114, 26, 10, 79, 50], ![-19, -108, 53, -69, 112]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![526, 355, 198, 123, 153]] ![![4, -7, 4, -3, 9]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![316813, 14571, -37231, -73696, -117926]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![316813, 14571, -37231, -73696, -117926]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![0, 0, 101, 0, 0], ![8, 96, 7, 1, 0], ![17, 60, 77, 0, 1]] where
  M :=![![![316813, 14571, -37231, -73696, -117926], ![-1415112, 485202, -177051, 484170, -294784], ![-3537408, -577743, 674588, 706398, 1936680], ![4580916, -1345482, 432748, -1504177, 618324], ![3093102, 653138, -682218, -576006, -1914651]]]
  hmulB := by decide  
  f := ![![![1791968612525, 887309701151, 567561920735, 301773057124, 424565600142]], ![![5094787201704, 2522730631428, 1613648358417, 857977923558, 1207092228496]], ![![14485106741952, 7172433515025, 4587800783482, 2439336779526, 3431911694232]], ![![6031163339060, 2986385867795, 1910222436408, 1015666561413, 1428944940612]], ![![14353237419563, 7107137210044, 4546034423637, 2417129577748, 3400668302127]]]
  g := ![![![28823, 140247, 94643, -73696, -117926], ![-2744, -280278, 189427, 484170, -294784], ![-416952, -1827651, -1518758, 706398, 1936680], ![60424, 1049070, -362861, -1504177, 618324], ![398517, 1691374, 1492851, -576006, -1914651]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [1, 20, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [85, 37, 64], [14, 63, 37], [0, 1]]
 g := ![![[16, 52, 70], [66, 79], [18, 0, 16], [6, 80], [72, 4], [1]], ![[31, 68, 72, 6], [46, 68], [64, 87, 25, 71], [6, 6], [98, 64], [80, 100, 58, 49]], ![[20, 27, 90, 22], [45, 96], [35, 12, 35, 96], [91, 85], [9, 36], [74, 44, 77, 52]]]
 h' := ![![[85, 37, 64], [56, 27, 26], [83, 67, 68], [86, 97, 97], [30, 10, 79], [100, 81, 99], [0, 1]], ![[14, 63, 37], [85, 96, 33], [38, 94, 88], [48, 22, 98], [16, 93, 62], [66, 52, 8], [85, 37, 64]], ![[0, 1], [47, 79, 42], [71, 41, 46], [74, 83, 7], [8, 99, 61], [44, 69, 95], [14, 63, 37]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37, 44], []]
 b := ![[], [78, 73, 94], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [1, 20, 2, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![489106, -94753, 34763, -136913, 28014]
  a := ![3, 3, 7, -1, 14]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![10972, 112555, -11524, -136913, 28014]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 1030301 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![130014676, 64377950, 41178929, 21894869, 30803959]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![130014676, 64377950, 41178929, 21894869, 30803959]] 
 ![![101, 0, 0, 0, 0], ![68, 1, 0, 0, 0], ![22, 0, 1, 0, 0], ![87, 0, 0, 1, 0], ![64, 0, 0, 0, 1]] where
  M :=![![![130014676, 64377950, 41178929, 21894869, 30803959], ![369647508, 183034455, 117076778, 62249820, 87579476], ![1050953712, 520389234, 332863751, 176983812, 248999280], ![313174806, 155071262, 99190332, 52739561, 74199470], ![-132551895, -65634184, -41982559, -22322115, -31405128]]]
  hmulB := by decide  
  f := ![![![-710062, -929840, 643329, -87485, 1604499]], ![![-287428, -662477, 438946, -116000, 1076792]], ![![-196244, -41170, 43121, 36614, 121098]], ![![-1163748, -714686, 549355, 84578, 1420939]], ![![-370667, -751214, 501715, -120547, 1234614]]]
  g := ![![![-89405241, 64377950, 41178929, 21894869, 30803959], ![-254190152, 183034455, 117076778, 62249820, 87579476], ![-722693686, 520389234, 332863751, 176983812, 248999280], ![-215356101, 155071262, 99190332, 52739561, 74199470], ![91149912, -65634184, -41982559, -22322115, -31405128]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2684, 1331, 850, 453, 635]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![2684, 1331, 850, 453, 635]] 
 ![![101, 0, 0, 0, 0], ![92, 1, 0, 0, 0], ![20, 0, 1, 0, 0], ![85, 0, 0, 1, 0], ![37, 0, 0, 0, 1]] where
  M :=![![![2684, 1331, 850, 453, 635], ![7620, 3782, 2419, 1290, 1812], ![21744, 10731, 6884, 3642, 5160], ![6510, 3202, 2046, 1079, 1522], ![-2775, -1338, -875, -447, -664]]]
  hmulB := by decide  
  f := ![![![1978, 4133, -2404, 1179, -2809]], ![![1468, 3808, -2165, 1098, -2512]], ![![952, 443, -362, 102, -460]], ![![2024, 3537, -2104, 998, -2475]], ![![335, 1711, -927, 504, -1059]]]
  g := ![![![-1968, 1331, 850, 453, 635], ![-5598, 3782, 2419, 1290, 1812], ![-15878, 10731, 6884, 3642, 5160], ![-4723, 3202, 2046, 1079, 1522], ![1984, -1338, -875, -447, -664]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![316813, 14571, -37231, -73696, -117926]] ![![130014676, 64377950, 41178929, 21894869, 30803959]]
  ![![1978, 4133, -2404, 1179, -2809]] where
 M := ![![![1978, 4133, -2404, 1179, -2809]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![1978, 4133, -2404, 1179, -2809]] ![![2684, 1331, 850, 453, 635]]
  ![![101, 0, 0, 0, 0]] where
 M := ![![![101, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-12688, -6212, -4011, -2097, -3019]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![-12688, -6212, -4011, -2097, -3019]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![0, 0, 0, 103, 0], ![36, 1, 32, 43, 1]] where
  M :=![![![-12688, -6212, -4011, -2097, -3019], ![-36228, -17761, -11328, -5952, -8388], ![-100656, -51000, -32101, -17640, -23808], ![-29502, -14982, -9744, -5317, -7566], ![11523, 6852, 3891, 2631, 2732]]]
  hmulB := by decide  
  f := ![![![-442, -118, 123, -21, 163]], ![![1956, -583, 24, -240, -84]], ![![-1008, 2040, -907, 648, -960]], ![![-2898, 258, 276, 173, 474]], ![![-1647, 683, -119, 260, -40]]]
  g := ![![![932, -31, 899, 1240, -3019], ![2580, -91, 2496, 3444, -8388], ![7344, -264, 7085, 9768, -23808], ![2358, -72, 2256, 3107, -7566], ![-843, 40, -811, -1115, 2732]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 4 2 6 [95, 40, 99, 60, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [7, 29, 65, 20], [97, 21, 20, 7], [42, 52, 18, 76], [0, 1]]
 g := ![![[91, 30, 58, 9], [69, 25, 72, 49], [64, 85, 38, 63], [49, 32, 93], [102, 43, 1], []], ![[90, 86, 33, 71, 11, 69], [8, 60, 86, 98, 59, 53], [55, 30, 14, 80, 18, 99], [54, 71, 13], [59, 77, 79], [60, 99, 54, 48, 9, 69]], ![[76, 20, 19, 85, 100, 19], [47, 24, 69, 77, 47, 30], [40, 17, 51, 67, 32, 60], [26, 24, 60], [55, 32, 33], [37, 21, 77, 59, 76, 34]], ![[98, 51, 29, 40, 53, 66], [2, 45, 4, 78, 40, 2], [13, 97, 75, 55, 60, 30], [21, 15, 64], [32, 63, 9], [99, 9, 20, 79, 2, 93]]]
 h' := ![![[7, 29, 65, 20], [37, 24, 31, 3], [100, 56, 35, 96], [44, 83, 90, 75], [95, 75, 35, 89], [0, 0, 0, 1], [0, 1]], ![[97, 21, 20, 7], [80, 75, 81, 83], [29, 62, 23, 7], [33, 33, 56, 12], [61, 53, 4, 42], [102, 80, 32, 64], [7, 29, 65, 20]], ![[42, 52, 18, 76], [67, 63, 20, 20], [0, 28, 32, 15], [15, 46, 46, 55], [42, 18, 87, 67], [80, 29, 17, 41], [97, 21, 20, 7]], ![[0, 1], [87, 44, 74, 100], [75, 60, 13, 88], [91, 44, 14, 64], [51, 60, 80, 8], [102, 97, 54, 100], [42, 52, 18, 76]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [29, 99, 88], []]
 b := ![[], [], [47, 12, 102, 61], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 4
  hpos := by decide
  P := [95, 40, 99, 60, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1827428845, -334162532, 50381248, -537798058, -47623124]
  a := ![1, 6, 10, -2, 27]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![34387003, -2781936, 15284672, 14660158, -47623124]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 112550881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-442, -118, 123, -21, 163]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![-442, -118, 123, -21, 163]] 
 ![![103, 0, 0, 0, 0], ![34, 1, 0, 0, 0], ![80, 0, 1, 0, 0], ![79, 0, 0, 1, 0], ![21, 0, 0, 0, 1]] where
  M :=![![![-442, -118, 123, -21, 163], ![1956, -583, 24, -240, -84], ![-1008, 2040, -907, 648, -960], ![-2898, 258, 276, 173, 474], ![1185, -1194, 447, -399, 434]]]
  hmulB := by decide  
  f := ![![![-12688, -6212, -4011, -2097, -3019]], ![![-4540, -2223, -1434, -750, -1078]], ![![-10832, -5320, -3427, -1800, -2576]], ![![-10018, -4910, -3171, -1660, -2389]], ![![-2475, -1200, -780, -402, -589]]]
  g := ![![![-78, -118, 123, -21, 163], ![394, -583, 24, -240, -84], ![-280, 2040, -907, 648, -960], ![-557, 258, 276, 173, 474], ![276, -1194, 447, -399, 434]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![-12688, -6212, -4011, -2097, -3019]] ![![-442, -118, 123, -21, 163]]
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


lemma PB752I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 103 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 103 (by omega)

def PB752I2 : PrimesBelowBoundCertificateInterval O 61 103 752 where
  m := 9
  g := ![4, 1, 2, 1, 2, 3, 2, 3, 2]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103]
  hP := PB752I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0, I67N1, I67N2, I67N3]
    · exact ![I71N0]
    · exact ![I73N0, I73N1]
    · exact ![I79N0]
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1, I89N2]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1, I101N2]
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
    · exact ![4489, 67, 67, 67]
    · exact ![1804229351]
    · exact ![28398241, 73]
    · exact ![3077056399]
    · exact ![571787, 6889]
    · exact ![704969, 89, 89]
    · exact ![88529281, 97]
    · exact ![1030301, 101, 101]
    · exact ![112550881, 103]
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
      exact NI67N3
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
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
      exact NI89N1
      exact NI89N2
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
      exact NI101N2
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
  β := ![I67N1, I67N2, I67N3, I73N1, I89N1, I89N2, I97N1, I101N1, I101N2, I103N1]
  Il := ![[I67N1, I67N2, I67N3], [], [I73N1], [], [], [I89N1, I89N2], [I97N1], [I101N1, I101N2], [I103N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
