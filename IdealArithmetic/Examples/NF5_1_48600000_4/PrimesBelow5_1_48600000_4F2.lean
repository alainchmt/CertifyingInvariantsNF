
import IdealArithmetic.Examples.NF5_1_48600000_4.RI5_1_48600000_4
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


def P67P0 : CertificateIrreducibleZModOfList' 67 5 2 6 [39, 53, 60, 5, 66, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [49, 7, 24, 25, 4], [11, 52, 0, 43, 32], [16, 58, 65, 7, 46], [59, 16, 45, 59, 52], [0, 1]]
 g := ![![[52, 1, 31, 51, 24], [9, 45, 22, 30, 37], [31, 56, 43, 47], [65, 63, 1, 1], [], []], ![[52, 0, 22, 44, 62, 33], [31, 23, 9, 45, 32, 30, 60, 60], [39, 20, 31, 16], [35, 37, 24, 60], [66, 2, 20, 1], [35, 15, 15, 16]], ![[57, 54, 53, 24, 10, 65, 58, 3], [52, 15, 33, 17, 63, 25, 29, 45], [58, 42, 2, 40], [58, 19, 3, 39], [18, 37, 46, 29], [27, 36, 24, 19]], ![[47, 49, 30, 50, 60, 15, 56, 31], [9, 56, 53, 59, 12, 62, 36, 2], [39, 48, 4, 54], [49, 53, 38, 22], [51, 51, 3, 36], [40, 18, 13, 39]], ![[35, 55, 18, 45, 10, 37, 17, 12], [33, 57, 29, 36, 44, 31, 62, 50], [57, 42, 56, 64], [13, 35, 13, 9], [40, 31, 35, 60], [57, 64, 63, 24]]]
 h' := ![![[49, 7, 24, 25, 4], [51, 34, 27, 46, 52], [51, 61, 44, 38, 29], [11, 61, 25, 24, 39], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[11, 52, 0, 43, 32], [33, 34, 35, 62], [20, 34, 43, 15, 22], [0, 37, 18, 27, 4], [62, 35, 23, 40, 23], [31, 55, 60, 24, 66], [49, 7, 24, 25, 4]], ![[16, 58, 65, 7, 46], [57, 29, 40, 1, 20], [35, 60, 1, 57, 38], [32, 62, 23, 65, 43], [4, 24, 29, 47, 21], [6, 51, 49, 55, 30], [11, 52, 0, 43, 32]], ![[59, 16, 45, 59, 52], [1, 19, 4, 49, 43], [42, 16, 39, 1, 13], [25, 59, 40, 51, 56], [44, 59, 5, 3, 25], [36, 39, 42, 53, 61], [16, 58, 65, 7, 46]], ![[0, 1], [42, 18, 28, 43, 19], [23, 30, 7, 23, 32], [54, 49, 28, 34, 59], [5, 16, 10, 44, 64], [52, 56, 49, 2, 44], [59, 16, 45, 59, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40, 39, 8, 15], [], [], []]
 b := ![[], [1, 50, 49, 21, 13], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 5
  hpos := by decide
  P := [39, 53, 60, 5, 66, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-937301498937, 2107761566821, -561847899113, -1234602352863, -620444256747]
  a := ![0, -1, -3, -1, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-13989574611, 31459127863, -8385789539, -18426900789, -9260362041]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0, 0, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0, 0, 0]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![0, 0, 0, 71, 0], ![0, 0, 0, 0, 71]] where
  M :=![![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![0, 0, 0, 71, 0], ![0, 0, 0, 0, 71]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 5 2 6 [67, 69, 18, 22, 2, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [55, 6, 45, 64, 36], [46, 26, 4, 41, 7], [70, 44, 63, 7, 68], [40, 65, 30, 30, 31], [0, 1]]
 g := ![![[67, 21, 34, 23, 16], [53, 19, 39, 51, 48], [50, 33, 16, 19, 37], [62, 53, 69, 1], [], []], ![[3, 44, 63, 16, 15, 20, 19, 57], [70, 44, 8, 54, 7, 5, 43, 37], [19, 63, 59, 47, 31, 51, 34, 9], [62, 32, 36, 25], [21, 12, 59, 8], [4, 68, 28, 18]], ![[1, 39, 60, 52, 55, 31, 44, 39], [24, 13, 14, 13, 67, 6, 37, 35], [19, 5, 31, 50, 52, 37, 11, 17], [11, 12, 52, 48], [70, 58, 0, 57], [6, 62, 50, 49]], ![[18, 36, 19, 44, 31, 46, 48, 67], [17, 62, 15, 48, 45, 18, 60, 53], [27, 66, 46, 35, 22, 22, 41, 47], [47, 43, 53, 40], [62, 25, 58, 45], [34, 19, 11, 9]], ![[46, 56, 65, 35, 37, 1, 43, 44], [59, 37, 15, 43, 33, 19, 41, 52], [15, 5, 47, 10, 38, 39, 42, 33], [50, 37, 29, 6], [23, 21, 3, 6], [0, 60, 9, 38]]]
 h' := ![![[55, 6, 45, 64, 36], [70, 67, 53, 2, 67], [58, 37, 30, 6, 30], [35, 52, 47, 25, 26], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[46, 26, 4, 41, 7], [42, 53, 68, 35, 55], [19, 27, 27, 61, 43], [47, 13, 50, 70, 35], [15, 37, 36, 34, 66], [59, 17, 50, 6, 24], [55, 6, 45, 64, 36]], ![[70, 44, 63, 7, 68], [46, 57, 58, 16, 6], [12, 54, 67, 38, 54], [30, 5, 7, 31, 16], [25, 20, 44, 7, 41], [10, 25, 53, 46, 46], [46, 26, 4, 41, 7]], ![[40, 65, 30, 30, 31], [23, 47, 42, 31, 66], [51, 60, 38, 26, 52], [25, 61, 19, 4, 47], [60, 19, 10, 18, 53], [66, 56, 2, 25, 20], [70, 44, 63, 7, 68]], ![[0, 1], [31, 60, 63, 58, 19], [25, 35, 51, 11, 34], [24, 11, 19, 12, 18], [45, 66, 52, 12, 52], [38, 44, 36, 65, 52], [40, 65, 30, 30, 31]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17, 63, 60, 45], [], [], []]
 b := ![[], [9, 16, 31, 2, 52], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 5
  hpos := by decide
  P := [67, 69, 18, 22, 2, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-169231609445, 481041145968, -264285983232, -110838108804, 80332078404]
  a := ![3, -64, 2, -1, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2383543795, 6775227408, -3722337792, -1561100124, 1131437724]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![396059, -888063, 232963, 518092, 260926]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![396059, -888063, 232963, 518092, 260926]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![0, 0, 73, 0, 0], ![59, 37, 55, 1, 0], ![20, 34, 3, 0, 1]] where
  M :=![![![396059, -888063, 232963, 518092, 260926], ![1565556, -3517831, 934659, 2059445, 1036184], ![6217104, -13977204, 3722534, 8187947, 4118890], ![24713340, -55566246, 14805193, 32554764, 16375894], ![46019130, -103473933, 27572727, 60624252, 30495319]]]
  hmulB := by decide  
  f := ![![![-115225, 323289, -164299, -87702, 59288]], ![![355728, -1004545, 532027, 250717, -175404]], ![![-1052424, 2986788, -1630848, -695801, 501434]], ![![-664535, 1885004, -1026125, -442298, 317744]], ![![40882, -113431, 53417, 35059, -22537]]]
  g := ![![![-484793, -396287, -397875, 518092, 260926], ![-1926923, -1574624, -1581416, 2059445, 1036184], ![-7660953, -6259911, -6287277, 8187947, 4118890], ![-30459392, -24888670, -24997733, 32554764, 16375894], ![-56722166, -46348111, -46551330, 60624252, 30495319]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [65, 15, 19, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [60, 69, 36], [67, 3, 37], [0, 1]]
 g := ![![[44, 21, 18], [30, 72], [50, 3], [5, 38, 69], [54, 1], []], ![[69, 65, 65, 64], [26, 8], [20, 67], [68, 22, 34, 35], [58, 9], [54, 55]], ![[38, 5, 36, 36], [41, 32], [28, 71], [58, 30, 63, 70], [50, 16], [53, 55]]]
 h' := ![![[60, 69, 36], [59, 54, 50], [29, 34, 27], [40, 46, 21], [67, 1, 54], [0, 0, 1], [0, 1]], ![[67, 3, 37], [61, 62, 50], [46, 55, 64], [18, 70, 40], [23, 13, 52], [17, 26, 3], [60, 69, 36]], ![[0, 1], [32, 30, 46], [54, 57, 55], [7, 30, 12], [8, 59, 40], [22, 47, 69], [67, 3, 37]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 13], []]
 b := ![[], [38, 19, 26], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [65, 15, 19, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-197312, 443670, -117845, -260190, -130518]
  a := ![1, -3, -1, -1, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![243346, 198744, 199783, -260190, -130518]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 389017 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-115225, 323289, -164299, -87702, 59288]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-115225, 323289, -164299, -87702, 59288]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![53, 18, 1, 0, 0], ![68, 21, 0, 1, 0], ![1, 55, 0, 0, 1]] where
  M :=![![![-115225, 323289, -164299, -87702, 59288], ![355728, -1004545, 532027, 250717, -175404], ![-1052424, 2986788, -1630848, -695801, 501434], ![3008604, -8573934, 4798157, 1879190, -1391602], ![-3648594, 10447923, -6010953, -2123628, 1628473]]]
  hmulB := by decide  
  f := ![![![396059, -888063, 232963, 518092, 260926]], ![![1565556, -3517831, 934659, 2059445, 1036184]], ![![758743, -1703637, 450595, 996121, 501360]], ![![1157836, -2600397, 688692, 1521005, 765462]], ![![1815353, -4080037, 1085095, 2389203, 1202005]]]
  g := ![![![198590, 25501, -164299, -87702, 59288], ![-612535, -84916, 532027, 250717, -175404], ![1810898, 265411, -1630848, -695801, 501434], ![-5173795, -792680, 4798157, 1879190, -1391602], ![6270002, 1009250, -6010953, -2123628, 1628473]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P1 : CertificateIrreducibleZModOfList' 73 2 2 6 [8, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [52, 72], [0, 1]]
 g := ![![[30, 64], [27], [67], [24, 69], [3], [1]], ![[0, 9], [27], [67], [35, 4], [3], [1]]]
 h' := ![![[52, 72], [22, 8], [47, 10], [27, 33], [40, 54], [65, 52], [0, 1]], ![[0, 1], [0, 65], [56, 63], [64, 40], [1, 19], [68, 21], [52, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53]]
 b := ![[], [41, 63]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N1 : CertifiedPrimeIdeal' SI73N1 73 where
  n := 2
  hpos := by decide
  P := [8, 21, 1]
  hirr := P73P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1824, -1789, -1435, 4478, 4858]
  a := ![1, 19, 4, -1, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3171, -4619, -1435, 4478, 4858]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N1 B_one_repr
lemma NI73N1 : Nat.card (O ⧸ I73N1) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![396059, -888063, 232963, 518092, 260926]] ![![-115225, 323289, -164299, -87702, 59288]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![269, -312, -75, 101, 66]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![269, -312, -75, 101, 66]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![0, 0, 79, 0, 0], ![16, 54, 3, 1, 0], ![55, 6, 23, 0, 1]] where
  M :=![![![269, -312, -75, 101, 66], ![396, -721, 119, 387, 202], ![1212, -2634, 676, 1533, 774], ![4644, -10398, 2769, 6094, 3066], ![8592, -19356, 5175, 11349, 5707]]]
  hmulB := by decide  
  f := ![![![-61, 180, -123, -13, 18]], ![![108, -331, 257, 3, -26]], ![![-156, 498, -458, 75, 6]], ![![56, -174, 141, -3, -12]], ![![-73, 228, -196, 23, 7]]]
  g := ![![![-63, -78, -24, 101, 66], ![-214, -289, -72, 387, 202], ![-834, -1140, -275, 1533, 774], ![-3310, -4530, -1089, 6094, 3066], ![-6163, -8436, -2027, 11349, 5707]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [53, 31, 22, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [48, 38, 57], [9, 40, 22], [0, 1]]
 g := ![![[14, 39, 64], [39, 26, 10], [47, 42, 22], [71, 62, 46], [57, 1], []], ![[49, 28, 62, 37], [75, 35, 55, 58], [67, 47, 32, 15], [56, 25, 26, 56], [26, 20], [4, 10]], ![[6, 13, 42, 1], [43, 72, 28, 55], [77, 66, 60, 38], [67, 1, 37, 76], [45, 22], [39, 10]]]
 h' := ![![[48, 38, 57], [66, 46, 8], [37, 2, 22], [29, 9, 38], [60, 76, 58], [0, 0, 1], [0, 1]], ![[9, 40, 22], [50, 25, 19], [21, 58, 46], [9, 38, 58], [66, 54, 16], [38, 71, 40], [48, 38, 57]], ![[0, 1], [76, 8, 52], [50, 19, 11], [8, 32, 62], [27, 28, 5], [68, 8, 38], [9, 40, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 60], []]
 b := ![[], [45, 63, 53], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [53, 31, 22, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3511553, 6430176, 392875, -6377109, -4971244]
  a := ![-1, 0, -4, 2, -9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![4708109, 4817994, 1694466, -6377109, -4971244]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 493039 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-61, 180, -123, -13, 18]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![-61, 180, -123, -13, 18]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![19, 76, 1, 0, 0], ![57, 10, 0, 1, 0], ![14, 45, 0, 0, 1]] where
  M :=![![![-61, 180, -123, -13, 18], ![108, -331, 257, 3, -26], ![-156, 498, -458, 75, 6], ![36, -246, 603, -416, 150], ![528, -1356, 273, 789, -419]]]
  hmulB := by decide  
  f := ![![![269, -312, -75, 101, 66]], ![![396, -721, 119, 387, 202]], ![![461, -802, 105, 416, 220]], ![![303, -448, -4, 199, 112]], ![![382, -711, 120, 382, 199]]]
  g := ![![![35, 112, -123, -13, 18], ![-58, -237, 257, 3, -26], ![53, 434, -458, 75, 6], ![129, -616, 603, -416, 150], ![-554, -141, 273, 789, -419]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P1 : CertificateIrreducibleZModOfList' 79 2 2 6 [40, 78, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 78], [0, 1]]
 g := ![![[77, 2], [61, 18], [25, 25], [], [1], [1]], ![[0, 77], [0, 61], [50, 54], [], [1], [1]]]
 h' := ![![[1, 78], [9, 70], [27, 52], [0, 5], [59], [39, 1], [0, 1]], ![[0, 1], [0, 9], [0, 27], [5, 74], [59], [40, 78], [1, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [78, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N1 : CertifiedPrimeIdeal' SI79N1 79 where
  n := 2
  hpos := by decide
  P := [40, 78, 1]
  hirr := P79P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1529, 1306, -3298, 2655, 3831]
  a := ![13, -1, -3, 1, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1782, 671, -3298, 2655, 3831]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N1 B_one_repr
lemma NI79N1 : Nat.card (O ⧸ I79N1) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![269, -312, -75, 101, 66]] ![![-61, 180, -123, -13, 18]]
  ![![79, 0, 0, 0, 0]] where
 M := ![![![79, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3755, -4237, -2935, 142, 432]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![3755, -4237, -2935, 142, 432]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![44, 13, 1, 0, 0], ![9, 41, 0, 1, 0], ![72, 22, 0, 0, 1]] where
  M :=![![![3755, -4237, -2935, 142, 432], ![2592, -2725, -1935, 89, 284], ![1704, -1668, -1216, 53, 178], ![1068, -966, -725, 30, 106], ![-534, 573, 405, -18, -59]]]
  hmulB := by decide  
  f := ![![![-11, 41, -55, 24, -6]], ![![-36, 79, 35, -97, 48]], ![![-8, 25, -21, 2, 2]], ![![-33, 82, -5, -59, 32]], ![![6, -13, -5, 16, -5]]]
  g := ![![![1211, 224, -2935, 142, 432], ![801, 151, -1935, 89, 284], ![505, 97, -1216, 53, 178], ![302, 59, -725, 30, 106], ![-168, -32, 405, -18, -59]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [77, 56, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 82], [0, 1]]
 g := ![![[46, 69], [16, 11], [77], [51], [4, 65], [1]], ![[0, 14], [64, 72], [77], [51], [16, 18], [1]]]
 h' := ![![[27, 82], [13, 61], [12, 54], [52, 34], [24, 36], [6, 27], [0, 1]], ![[0, 1], [0, 22], [59, 29], [57, 49], [0, 47], [71, 56], [27, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [46, 55]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [77, 56, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-368, 1248, -879, -65, 1067]
  a := ![-1, -3, 2, -1, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-457, -98, -879, -65, 1067]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-67, 180, -107, -43, 32]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-67, 180, -107, -43, 32]] 
 ![![83, 0, 0, 0, 0], ![20, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![32, 0, 0, 1, 0], ![46, 0, 0, 0, 1]] where
  M :=![![![-67, 180, -107, -43, 32], ![192, -547, 297, 117, -86], ![-516, 1482, -860, -305, 234], ![1404, -4026, 2347, 778, -610], ![-1572, 4536, -2719, -809, 661]]]
  hmulB := by decide  
  f := ![![![92815, -208728, 55629, 122295, 61516]], ![![26812, -60295, 16069, 35327, 17770]], ![![34455, -77478, 20647, 45394, 22834]], ![![106084, -238542, 63567, 139760, 70302]], ![![182354, -410040, 109267, 240239, 120845]]]
  g := ![![![-26, 180, -107, -43, 32], ![83, -547, 297, 117, -86], ![-220, 1482, -860, -305, 234], ![601, -4026, 2347, 778, -610], ![-675, 4536, -2719, -809, 661]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1

def I83N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![203, -576, 318, 132, -96]] i)))

def SI83N2: IdealEqSpanCertificate' Table ![![203, -576, 318, 132, -96]] 
 ![![83, 0, 0, 0, 0], ![66, 1, 0, 0, 0], ![43, 0, 1, 0, 0], ![67, 0, 0, 1, 0], ![50, 0, 0, 0, 1]] where
  M :=![![![203, -576, 318, 132, -96], ![-576, 1643, -924, -354, 264], ![1584, -4536, 2609, 924, -708], ![-4248, 12204, -7152, -2347, 1848], ![4752, -13716, 8244, 2430, -1993]]]
  hmulB := by decide  
  f := ![![![10777, -23904, 6258, 13956, 7032]], ![![9078, -20149, 5280, 11766, 5928]], ![![7601, -16920, 4451, 9888, 4980]], ![![16721, -37332, 9858, 21833, 10992]], ![![21430, -47988, 12720, 28086, 14135]]]
  g := ![![![247, -576, 318, 132, -96], ![-708, 1643, -924, -354, 264], ![1955, -4536, 2609, 924, -708], ![-5269, 12204, -7152, -2347, 1848], ![5932, -13716, 8244, 2430, -1993]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N2 : Nat.card (O ⧸ I83N2) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N2)

lemma isPrimeI83N2 : Ideal.IsPrime I83N2 := prime_ideal_of_norm_prime hp83.out _ NI83N2

def I83N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![21833, -49300, 13161, 28885, 14526]] i)))

def SI83N3: IdealEqSpanCertificate' Table ![![21833, -49300, 13161, 28885, 14526]] 
 ![![83, 0, 0, 0, 0], ![67, 1, 0, 0, 0], ![76, 0, 1, 0, 0], ![54, 0, 0, 1, 0], ![62, 0, 0, 0, 1]] where
  M :=![![![21833, -49300, 13161, 28885, 14526], ![87156, -196057, 52215, 114843, 57770], ![346620, -779394, 207636, 456605, 229686], ![1378116, -3098670, 825641, 1815438, 913210], ![2566320, -5770320, 1537591, 3380753, 1700595]]]
  hmulB := by decide  
  f := ![![![201715, -582280, 350165, 102983, -84538]], ![![156719, -452325, 271796, 80220, -65760]], ![![199592, -576506, 347838, 100801, -83230]], ![![96306, -276618, 161879, 53454, -41994]], ![![182254, -528304, 324817, 86229, -73785]]]
  g := ![![![-1635, -49300, 13161, 28885, 14526], ![-6369, -196057, 52215, 114843, 57770], ![-25440, -779394, 207636, 456605, 229686], ![-101354, -3098670, 825641, 1815438, 913210], ![-188876, -5770320, 1537591, 3380753, 1700595]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N3 : Nat.card (O ⧸ I83N3) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N3)

lemma isPrimeI83N3 : Ideal.IsPrime I83N3 := prime_ideal_of_norm_prime hp83.out _ NI83N3
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![3755, -4237, -2935, 142, 432]] ![![-67, 180, -107, -43, 32]]
  ![![-30365, 31729, 22592, -1031, -3316]] where
 M := ![![![-30365, 31729, 22592, -1031, -3316]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI83N1 : IdealMulLeCertificate' Table 
  ![![-30365, 31729, 22592, -1031, -3316]] ![![203, -576, 318, 132, -96]]
  ![![-32215, 43607, 5470, -3361, -140]] where
 M := ![![![-32215, 43607, 5470, -3361, -140]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI83N2 : IdealMulLeCertificate' Table 
  ![![-32215, 43607, 5470, -3361, -140]] ![![21833, -49300, 13161, 28885, 14526]]
  ![![83, 0, 0, 0, 0]] where
 M := ![![![2140321, -2068609, -1515331, 65238, 221610]]]
 hmul := by decide  
 g := ![![![![25787, -24923, -18257, 786, 2670]]]]
 hle2 := by decide  


def PBC83 : ContainsPrimesAboveP 83 ![I83N0, I83N1, I83N2, I83N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
    exact isPrimeI83N1
    exact isPrimeI83N2
    exact isPrimeI83N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 83 (by decide) (𝕀 ⊙ MulI83N0 ⊙ MulI83N1 ⊙ MulI83N2)
instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![305, -681, 178, 397, 200]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![305, -681, 178, 397, 200]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![61, 74, 1, 0, 0], ![25, 14, 0, 1, 0], ![32, 36, 0, 0, 1]] where
  M :=![![![305, -681, 178, 397, 200], ![1200, -2695, 716, 1578, 794], ![4764, -10710, 2853, 6274, 3156], ![18936, -42576, 11344, 24945, 12548], ![35262, -79287, 21128, 46453, 23367]]]
  hmulB := by decide  
  f := ![![![-227, 279, 218, -13, -30]], ![![-180, 223, 116, 8, -26]], ![![-307, 379, 247, -3, -42]], ![![-91, 109, 82, 0, -14]], ![![-158, 201, 120, -5, -19]]]
  g := ![![![-302, -299, 178, 397, 200], ![-1206, -1195, 716, 1578, 794], ![-4799, -4756, 2853, 6274, 3156], ![-19081, -18910, 11344, 24945, 12548], ![-35535, -35217, 21128, 46453, 23367]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [59, 58, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 88], [0, 1]]
 g := ![![[4, 11], [8], [68], [17, 87], [56, 71], [1]], ![[78, 78], [8], [68], [44, 2], [32, 18], [1]]]
 h' := ![![[31, 88], [41, 10], [35, 50], [65, 54], [78, 49], [30, 31], [0, 1]], ![[0, 1], [84, 79], [72, 39], [48, 35], [84, 40], [12, 58], [31, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [75]]
 b := ![[], [64, 82]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [59, 58, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3664, 12456, -7142, -1909, 5905]
  a := ![3, 0, 7, -4, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3267, 3990, -7142, -1909, 5905]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-55, 145, 122, 21, -2]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![-55, 145, 122, 21, -2]] 
 ![![89, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![73, 0, 1, 0, 0], ![64, 0, 0, 1, 0], ![58, 0, 0, 0, 1]] where
  M :=![![![-55, 145, 122, 21, -2], ![-12, -25, 156, 108, 42], ![252, -642, 293, 450, 216], ![1296, -2988, 888, 1805, 900], ![2574, -5781, 1512, 3369, 1697]]]
  hmulB := by decide  
  f := ![![![-803, 2809, -3262, 1095, -236]], ![![-52, 157, -116, -6, 14]], ![![-511, 1919, -2577, 1101, -304]], ![![-1240, 3824, -3080, 113, 236]], ![![620, -1351, -596, 1665, -773]]]
  g := ![![![-121, 145, 122, 21, -2], ![-232, -25, 156, 108, 42], ![-673, -642, 293, 450, 216], ![-2464, -2988, 888, 1805, 900], ![-4480, -5781, 1512, 3369, 1697]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1

def I89N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-83, -1007, -180, 213, 132]] i)))

def SI89N2: IdealEqSpanCertificate' Table ![![-83, -1007, -180, 213, 132]] 
 ![![89, 0, 0, 0, 0], ![41, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![35, 0, 0, 1, 0], ![34, 0, 0, 0, 1]] where
  M :=![![![-83, -1007, -180, 213, 132], ![792, -2063, -134, 744, 426], ![2556, -5598, 811, 2848, 1488], ![8928, -19764, 4690, 11227, 5696], ![15810, -35457, 9566, 20857, 10483]]]
  hmulB := by decide  
  f := ![![![-45943, 122665, -41608, -54289, 30998]], ![![-19075, 50768, -16658, -23039, 13060]], ![![-12482, 34172, -14545, -12130, 7424]], ![![5579, -18197, 17702, -3632, 130]], ![![-50072, 138941, -65470, -42903, 27589]]]
  g := ![![![349, -1007, -180, 213, 132], ![519, -2063, -134, 744, 426], ![828, -5598, 811, 2848, 1488], ![2087, -19764, 4690, 11227, 5696], ![3230, -35457, 9566, 20857, 10483]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N2 : Nat.card (O ⧸ I89N2) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N2)

lemma isPrimeI89N2 : Ideal.IsPrime I89N2 := prime_ideal_of_norm_prime hp89.out _ NI89N2

def I89N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, -25, 19, 22, 10]] i)))

def SI89N3: IdealEqSpanCertificate' Table ![![7, -25, 19, 22, 10]] 
 ![![89, 0, 0, 0, 0], ![59, 1, 0, 0, 0], ![79, 0, 1, 0, 0], ![56, 0, 0, 1, 0], ![44, 0, 0, 0, 1]] where
  M :=![![![7, -25, 19, 22, 10], ![60, -143, 47, 89, 44], ![264, -600, 166, 355, 178], ![1068, -2406, 645, 1412, 710], ![1998, -4491, 1195, 2630, 1323]]]
  hmulB := by decide  
  f := ![![![-205, 743, -531, -156, 132]], ![![-127, 468, -338, -99, 84]], ![![-203, 721, -509, -149, 126]], ![![-76, 314, -239, -74, 62]], ![![-154, 521, -361, -98, 85]]]
  g := ![![![-19, -25, 19, 22, 10], ![-24, -143, 47, 89, 44], ![-58, -600, 166, 355, 178], ![-205, -2406, 645, 1412, 710], ![-370, -4491, 1195, 2630, 1323]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N3 : Nat.card (O ⧸ I89N3) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N3)

lemma isPrimeI89N3 : Ideal.IsPrime I89N3 := prime_ideal_of_norm_prime hp89.out _ NI89N3
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![305, -681, 178, 397, 200]] ![![-55, 145, 122, 21, -2]]
  ![![1065565, -2395462, 638064, 1403342, 705936]] where
 M := ![![![1065565, -2395462, 638064, 1403342, 705936]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI89N1 : IdealMulLeCertificate' Table 
  ![![1065565, -2395462, 638064, 1403342, 705936]] ![![-83, -1007, -180, 213, 132]]
  ![![23335129321, -52469092161, 13981317868, 30740975675, 15463390120]] where
 M := ![![![23335129321, -52469092161, 13981317868, 30740975675, 15463390120]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI89N2 : IdealMulLeCertificate' Table 
  ![![23335129321, -52469092161, 13981317868, 30740975675, 15463390120]] ![![7, -25, 19, 22, 10]]
  ![![89, 0, 0, 0, 0]] where
 M := ![![![64433483773399, -144877961277772, 38604899395395, 84881965154573, 42697543676640]]]
 hmul := by decide  
 g := ![![![![723971727791, -1627842261548, 433762914555, 953729945557, 479747681760]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N1, I89N2, I89N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N1
    exact isPrimeI89N2
    exact isPrimeI89N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0 ⊙ MulI89N1 ⊙ MulI89N2)
instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, 3, 10, -3, 0]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![-5, 3, 10, -3, 0]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![0, 0, 97, 0, 0], ![34, 96, 29, 1, 0], ![89, 80, 16, 0, 1]] where
  M :=![![![-5, 3, 10, -3, 0], ![0, -5, 0, 10, -6], ![-36, 90, -25, -42, 20], ![120, -336, 148, 115, -84], ![-234, 645, -308, -199, 105]]]
  hmulB := by decide  
  f := ![![![199, -213, -150, 7, 22]], ![![132, -131, -96, 4, 14]], ![![84, -78, -57, 2, 8]], ![![226, -228, -165, 7, 24]], ![![305, -316, -226, 10, 33]]]
  g := ![![![1, 3, 1, -3, 0], ![2, -5, -2, 10, -6], ![-4, 26, 9, -42, 20], ![38, -48, -19, 115, -84], ![-29, 117, 39, -199, 105]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [9, 58, 91, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [90, 26, 78], [13, 70, 19], [0, 1]]
 g := ![![[87, 36, 18], [35, 12], [4, 3], [92, 89], [5, 36], [1]], ![[5, 12, 57, 37], [59, 61], [69, 93], [27, 27], [13, 27], [23, 96, 2, 28]], ![[17, 33, 26, 69], [51, 31], [86, 6], [79, 22], [68, 91], [83, 15, 79, 69]]]
 h' := ![![[90, 26, 78], [62, 13, 42], [59, 47, 77], [80, 88, 87], [36, 42, 34], [88, 39, 6], [0, 1]], ![[13, 70, 19], [35, 49, 74], [9, 94, 35], [40, 75, 53], [34, 22, 30], [32, 72, 67], [90, 26, 78]], ![[0, 1], [8, 35, 78], [51, 53, 82], [90, 31, 54], [92, 33, 33], [92, 83, 24], [13, 70, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [81, 55], []]
 b := ![[], [7, 74, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [9, 58, 91, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![683415, -1195092, -150256, 1288816, 1098324]
  a := ![1, 1, 2, -1, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1452445, -2193684, -568032, 1288816, 1098324]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 912673 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-199, 213, 150, -7, -22]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![-199, 213, 150, -7, -22]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![51, 68, 1, 0, 0], ![24, 83, 0, 1, 0], ![89, 66, 0, 0, 1]] where
  M :=![![![-199, 213, 150, -7, -22], ![-132, 131, 96, -4, -14], ![-84, 78, 57, -2, -8], ![-48, 36, 36, 1, -4], ![30, -33, -20, 5, 5]]]
  hmulB := by decide  
  f := ![![![5, -3, -10, 3, 0]], ![![0, 5, 0, -10, 6]], ![![3, 1, -5, -5, 4]], ![![0, 7, -4, -9, 6]], ![![7, -6, -6, -2, 3]]]
  g := ![![![-59, -82, 150, -7, -22], ![-38, -53, 96, -4, -14], ![-23, -32, 57, -2, -8], ![-16, -23, 36, 1, -4], ![5, 6, -20, 5, 5]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P1 : CertificateIrreducibleZModOfList' 97 2 2 6 [66, 27, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [70, 96], [0, 1]]
 g := ![![[93, 25], [95], [66], [72], [62], [70, 1]], ![[0, 72], [95], [66], [72], [62], [43, 96]]]
 h' := ![![[70, 96], [38, 5], [10, 80], [96, 39], [17, 84], [36, 81], [0, 1]], ![[0, 1], [0, 92], [81, 17], [13, 58], [77, 13], [80, 16], [70, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39]]
 b := ![[], [45, 68]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N1 : CertifiedPrimeIdeal' SI97N1 97 where
  n := 2
  hpos := by decide
  P := [66, 27, 1]
  hirr := P97P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![28, 468, -278, -82, 88]
  a := ![4, 0, -1, 1, -1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![86, 210, -278, -82, 88]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N1 B_one_repr
lemma NI97N1 : Nat.card (O ⧸ I97N1) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![-5, 3, 10, -3, 0]] ![![-199, 213, 150, -7, -22]]
  ![![97, 0, 0, 0, 0]] where
 M := ![![![-97, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1435, 2242, 1281, -163, -240]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![-1435, 2242, 1281, -163, -240]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![0, 0, 101, 0, 0], ![0, 0, 0, 101, 0], ![67, 42, 54, 92, 1]] where
  M :=![![![-1435, 2242, 1281, -163, -240], ![-1440, 2165, 879, -399, -326], ![-1956, 3450, 136, -1403, -798], ![-4788, 10014, -1943, -5450, -2806], ![-7440, 16926, -4801, -10091, -5051]]]
  hmulB := by decide  
  f := ![![![49, -134, 59, 45, -28]], ![![-168, 469, -229, -137, 90]], ![![540, -1518, 782, 401, -274]], ![![-1644, 4650, -2487, -1136, 802]], ![![-1225, 3470, -1870, -834, 593]]]
  g := ![![![145, 122, 141, 217, -240], ![202, 157, 183, 293, -326], ![510, 366, 428, 713, -798], ![1814, 1266, 1481, 2502, -2806], ![3277, 2268, 2653, 4501, -5051]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 4 2 6 [93, 13, 28, 85, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [65, 46, 34, 94], [65, 95, 73, 29], [88, 60, 95, 79], [0, 1]]
 g := ![![[46, 57, 14, 52], [90, 74, 56], [98, 1, 95, 43], [89, 73, 5], [26, 16, 1], []], ![[56, 83, 95, 26, 2, 46], [100, 18, 14], [70, 61, 15, 65, 47, 2], [3, 47, 85], [44, 65, 13], [16, 83, 32, 6, 15, 61]], ![[39, 81, 26, 54, 66, 86], [70, 8, 87], [93, 34, 33, 51, 68, 27], [34, 73, 81], [59, 7, 92], [80, 95, 96, 68, 16, 48]], ![[74, 71, 34, 89, 67, 82], [2, 79, 43], [43, 45, 9, 79, 80, 84], [49, 8, 19], [48, 57, 13], [87, 69, 73, 87, 94, 58]]]
 h' := ![![[65, 46, 34, 94], [84, 5, 36, 70], [77, 11, 8, 37], [41, 38, 71, 89], [6, 93, 82, 56], [0, 0, 0, 1], [0, 1]], ![[65, 95, 73, 29], [71, 38, 4, 22], [33, 64, 19, 69], [46, 87, 2, 12], [27, 44, 0, 61], [33, 29, 60, 35], [65, 46, 34, 94]], ![[88, 60, 95, 79], [55, 63, 62, 81], [0, 97, 11, 84], [47, 7, 80, 54], [52, 56, 5, 9], [40, 26, 85, 30], [65, 95, 73, 29]], ![[0, 1], [63, 96, 100, 29], [42, 30, 63, 12], [58, 70, 49, 47], [75, 9, 14, 76], [14, 46, 57, 35], [88, 60, 95, 79]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [19, 88, 58], []]
 b := ![[], [], [21, 73, 34, 99], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 4
  hpos := by decide
  P := [93, 13, 28, 85, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![501803827774, -1113742135546, 274074755988, 680037149460, 356301097003]
  a := ![7, 2, -24, 0, -23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-231389798727, -159191962472, -187784004774, -317818453216, 356301097003]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 104060401 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-49, 134, -59, -45, 28]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![-49, 134, -59, -45, 28]] 
 ![![101, 0, 0, 0, 0], ![18, 1, 0, 0, 0], ![80, 0, 1, 0, 0], ![75, 0, 0, 1, 0], ![93, 0, 0, 0, 1]] where
  M :=![![![-49, 134, -59, -45, 28], ![168, -469, 229, 137, -90], ![-540, 1518, -782, -401, 274], ![1644, -4650, 2487, 1136, -802], ![-2136, 6078, -3371, -1363, 999]]]
  hmulB := by decide  
  f := ![![![1435, -2242, -1281, 163, 240]], ![![270, -421, -237, 33, 46]], ![![1156, -1810, -1016, 143, 198]], ![![1113, -1764, -932, 175, 206]], ![![1395, -2232, -1132, 250, 271]]]
  g := ![![![30, 134, -59, -45, 28], ![-115, -469, 229, 137, -90], ![389, 1518, -782, -401, 274], ![-1230, -4650, 2487, 1136, -802], ![1658, 6078, -3371, -1363, 999]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![-1435, 2242, 1281, -163, -240]] ![![-49, 134, -59, -45, 28]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![291761, -832070, 467634, 180352, -134234]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![291761, -832070, 467634, 180352, -134234]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![19, 71, 1, 0, 0], ![93, 25, 0, 1, 0], ![62, 102, 0, 0, 1]] where
  M :=![![![291761, -832070, 467634, 180352, -134234], ![-805404, 2305271, -1322888, -472004, 360704], ![2164224, -6215964, 3636787, 1202040, -944008], ![-5664048, 16324344, -9733964, -2971269, 2404080], ![6130128, -17754642, 10868344, 2946278, -2499265]]]
  hmulB := by decide  
  f := ![![![146063, -131878, -96298, 5908, 15178]], ![![91068, -81607, -50080, 9948, 11816]], ![![90407, -81417, -52407, 8264, 11138]], ![![155145, -141091, -98658, 8979, 17206]], ![![179662, -163952, -106404, 15690, 21971]]]
  g := ![![![-165471, -241272, 467634, 180352, -134234], ![445264, 691637, -1322888, -472004, 360704], ![-1166951, -1924175, 3636787, 1202040, -944008], ![2976275, 5208751, -9733964, -2971269, 2404080], ![-3101144, -5904262, 10868344, 2946278, -2499265]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [2, 35, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [68, 102], [0, 1]]
 g := ![![[69, 52], [75, 61], [95, 91], [100], [66], [68, 1]], ![[0, 51], [0, 42], [0, 12], [100], [66], [33, 102]]]
 h' := ![![[68, 102], [56, 84], [16, 24], [82, 20], [30, 93], [70, 90], [0, 1]], ![[0, 1], [0, 19], [0, 79], [0, 83], [71, 10], [10, 13], [68, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49]]
 b := ![[], [94, 76]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [2, 35, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3182, -4569, -1906, 6477, 6860]
  a := ![1, 3, -7, -1, -8]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-9595, -7096, -1906, 6477, 6860]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19091, 54381, -30351, -12002, 8860]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![-19091, 54381, -30351, -12002, 8860]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![63, 0, 1, 0, 0], ![0, 63, 0, 1, 0], ![44, 0, 0, 0, 1]] where
  M :=![![![-19091, 54381, -30351, -12002, 8860], ![53160, -151991, 86679, 31669, -24004], ![-144024, 413220, -240342, -81349, 63338], ![380028, -1094094, 648561, 203024, -162698], ![-416082, 1203639, -732109, -204488, 171355]]]
  hmulB := by decide  
  f := ![![![-8681, 20235, -3755, -10740, -5526]], ![![-33156, 74209, -18135, -42437, -21480]], ![![-6561, 15183, -3031, -8205, -4204]], ![![-25224, 56499, -14042, -32459, -16410]], ![![-12898, 29307, -7113, -16696, -8451]]]
  g := ![![![14594, 7869, -30351, -12002, 8860], ![-42247, -20846, 86679, 31669, -24004], ![118550, 53769, -240342, -81349, 63338], ![-323501, -134802, 648561, 203024, -162698], ![370555, 136761, -732109, -204488, 171355]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P1 : CertificateIrreducibleZModOfList' 103 2 2 6 [34, 98, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 102], [0, 1]]
 g := ![![[15, 100], [56, 30], [40, 25], [30], [81], [5, 1]], ![[0, 3], [0, 73], [62, 78], [30], [81], [10, 102]]]
 h' := ![![[5, 102], [53, 10], [82, 66], [60, 98], [87, 66], [36, 94], [0, 1]], ![[0, 1], [0, 93], [0, 37], [35, 5], [5, 37], [94, 9], [5, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52]]
 b := ![[], [38, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N1 : CertifiedPrimeIdeal' SI103N1 103 where
  n := 2
  hpos := by decide
  P := [34, 98, 1]
  hirr := P103P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3367, -6852, 2092, 4487, 2285]
  a := ![3, 0, 2, 5, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2223, -2811, 2092, 4487, 2285]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N1 B_one_repr
lemma NI103N1 : Nat.card (O ⧸ I103N1) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N1

def I103N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, -108, 69, 15, -14]] i)))

def SI103N2: IdealEqSpanCertificate' Table ![![37, -108, 69, 15, -14]] 
 ![![103, 0, 0, 0, 0], ![32, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![14, 0, 0, 1, 0], ![82, 0, 0, 0, 1]] where
  M :=![![![37, -108, 69, 15, -14], ![-84, 247, -163, -29, 30], ![180, -534, 368, 47, -58], ![-348, 1050, -777, -38, 94], ![192, -612, 557, -83, -9]]]
  hmulB := by decide  
  f := ![![![5443, 504, -1231, -95, 154]], ![![1700, 187, -371, -31, 46]], ![![306, 66, -52, -7, 6]], ![![722, 102, -147, -14, 18]], ![![4330, 396, -981, -75, 123]]]
  g := ![![![39, -108, 69, 15, -14], ![-88, 247, -163, -29, 30], ![186, -534, 368, 47, -58], ![-354, 1050, -777, -38, 94], ![178, -612, 557, -83, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N2 : Nat.card (O ⧸ I103N2) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N2)

lemma isPrimeI103N2 : Ideal.IsPrime I103N2 := prime_ideal_of_norm_prime hp103.out _ NI103N2
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![291761, -832070, 467634, 180352, -134234]] ![![-19091, 54381, -30351, -12002, 8860]]
  ![![7237791377, -23322190823, 21872868509, -3829071978, -167563734]] where
 M := ![![![7237791377, -23322190823, 21872868509, -3829071978, -167563734]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI103N1 : IdealMulLeCertificate' Table 
  ![![7237791377, -23322190823, 21872868509, -3829071978, -167563734]] ![![37, -108, 69, 15, -14]]
  ![![103, 0, 0, 0, 0]] where
 M := ![![![7464323453117, -22140350957495, 15231996247542, 1972347749531, -2428045869816]]]
 hmul := by decide  
 g := ![![![![72469159739, -214954863665, 147883458714, 19149007277, -23573260872]]]]
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


lemma PB434I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 103 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 103 (by omega)

def PB434I2 : PrimesBelowBoundCertificateInterval O 61 103 434 where
  m := 9
  g := ![1, 1, 2, 2, 4, 4, 2, 2, 3]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103]
  hP := PB434I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0]
    · exact ![I71N0]
    · exact ![I73N0, I73N1]
    · exact ![I79N0, I79N1]
    · exact ![I83N0, I83N1, I83N2, I83N3]
    · exact ![I89N0, I89N1, I89N2, I89N3]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
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
    · exact ![1804229351]
    · exact ![389017, 5329]
    · exact ![493039, 6241]
    · exact ![6889, 83, 83, 83]
    · exact ![7921, 89, 89, 89]
    · exact ![912673, 9409]
    · exact ![104060401, 101]
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
      exact NI83N3
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
      exact NI89N2
      exact NI89N3
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
      exact NI103N2
  β := ![I83N1, I83N2, I83N3, I89N1, I89N2, I89N3, I101N1, I103N2]
  Il := ![[], [], [], [], [I83N1, I83N2, I83N3], [I89N1, I89N2, I89N3], [], [I101N1], [I103N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
