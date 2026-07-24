
import IdealArithmetic.Examples.NF5_3_112500000_1.RI5_3_112500000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10294, 278, -628, -1500, 1161]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![-10294, 278, -628, -1500, 1161]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![27, 0, 1, 0, 0], ![36, 49, 0, 1, 0], ![53, 34, 0, 0, 1]] where
  M :=![![![-10294, 278, -628, -1500, 1161], ![26608, -717, 1622, 3876, -3000], ![-34378, 931, -2095, -5010, 3876], ![34131, -924, 2082, 4975, -3849], ![-23279, 626, -1420, -3390, 2626]]]
  hmulB := by decide  
  f := ![![![-640, -10, -28, -150, 93]], ![![2176, 75, 110, 504, -300]], ![![-310, -5, -13, -72, 45]], ![![1303, 51, 68, 301, -177]], ![![549, 30, 32, 126, -71]]]
  g := ![![![-13, 512, -628, -1500, 1161], ![34, -1323, 1622, 3876, -3000], ![-43, 1711, -2095, -5010, 3876], ![42, -1699, 2082, 4975, -3849], ![-31, 1156, -1420, -3390, 2626]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [52, 66, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 66], [0, 1]]
 g := ![![[9, 35], [58, 49], [37], [23], [1], [1]], ![[44, 32], [40, 18], [37], [23], [1], [1]]]
 h' := ![![[1, 66], [66, 13], [52, 60], [57, 29], [39, 31], [15, 1], [0, 1]], ![[0, 1], [12, 54], [45, 7], [19, 38], [3, 36], [16, 66], [1, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [11, 45]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [52, 66, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![17146, 9101, 9229, 10262, 3858]
  a := ![-9, -7, -7, -10, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-12029, -9327, 9229, 10262, 3858]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14, 16, 12, 12, 7]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![14, 16, 12, 12, 7]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![34, 10, 1, 0, 0], ![32, 47, 0, 1, 0], ![42, 29, 0, 0, 1]] where
  M :=![![![14, 16, 12, 12, 7], ![192, 77, 70, 76, 24], ![358, 207, 171, 182, 76], ![269, 114, 102, 109, 37], ![719, 380, 320, 342, 134]]]
  hmulB := by decide  
  f := ![![![-40, -20, 12, 14, -5]], ![![-96, -83, -26, 24, 28]], ![![-30, -21, 1, 10, 2]], ![![-87, -67, -12, 23, 17]], ![![-69, -49, -2, 20, 8]]]
  g := ![![![-16, -13, 12, 12, 7], ![-84, -73, 70, 76, 24], ![-216, -183, 171, 182, 76], ![-123, -106, 102, 109, 37], ![-399, -340, 320, 342, 134]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P1 : CertificateIrreducibleZModOfList' 67 2 2 6 [3, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [47, 66], [0, 1]]
 g := ![![[29, 16], [62, 40], [33], [6], [65], [1]], ![[44, 51], [66, 27], [33], [6], [65], [1]]]
 h' := ![![[47, 66], [15, 63], [4, 24], [6, 57], [15, 26], [64, 47], [0, 1]], ![[0, 1], [28, 4], [60, 43], [5, 10], [31, 41], [62, 20], [47, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [11, 48]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N1 : CertifiedPrimeIdeal' SI67N1 67 where
  n := 2
  hpos := by decide
  P := [3, 20, 1]
  hirr := P67P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![748402, 427943, 407057, 434588, 202754]
  a := ![-53, -53, -57, -58, -104]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-530060, -446987, 407057, 434588, 202754]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N1 B_one_repr
lemma NI67N1 : Nat.card (O ⧸ I67N1) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N1

def I67N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![104, 24, -48, -20, 23]] i)))

def SI67N2: IdealEqSpanCertificate' Table ![![104, 24, -48, -20, 23]] 
 ![![67, 0, 0, 0, 0], ![47, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![10, 0, 0, 0, 1]] where
  M :=![![![104, 24, -48, -20, 23], ![456, 339, -2, -156, -40], ![-482, -29, 297, 70, -156], ![-323, -294, -46, 127, 61], ![135, -264, -324, 62, 208]]]
  hmulB := by decide  
  f := ![![![-14734, 588, -960, -1830, 1559]], ![![-9806, 389, -638, -1222, 1039]], ![![-840, 41, -57, -92, 85]], ![![601, -32, 42, 61, -59]], ![![-2529, 112, -168, -296, 262]]]
  g := ![![![-18, 24, -48, -20, 23], ![-225, 339, -2, -156, -40], ![32, -29, 297, 70, -156], ![193, -294, -46, 127, 61], ![161, -264, -324, 62, 208]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N2 : Nat.card (O ⧸ I67N2) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N2)

lemma isPrimeI67N2 : Ideal.IsPrime I67N2 := prime_ideal_of_norm_prime hp67.out _ NI67N2
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![-10294, 278, -628, -1500, 1161]] ![![14, 16, 12, 12, 7]]
  ![![115695, -3114, 7064, 16866, -13040]] where
 M := ![![![115695, -3114, 7064, 16866, -13040]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![115695, -3114, 7064, 16866, -13040]] ![![104, 24, -48, -20, 23]]
  ![![67, 0, 0, 0, 0]] where
 M := ![![![-670, 134, 0, -134, 67]]]
 hmul := by decide  
 g := ![![![![-10, 2, 0, -2, 1]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1450, -1069, 14, 494, 123]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-1450, -1069, 14, 494, 123]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![0, 0, 0, 71, 0], ![24, 60, 3, 45, 1]] where
  M :=![![![-1450, -1069, 14, 494, 123], ![2980, 137, -1864, -412, 988], ![9992, 6662, -739, -3204, -412], ![-4245, -1205, 1768, 889, -807], ![-13651, -7467, 2456, 3896, -412]]]
  hmulB := by decide  
  f := ![![![-428, 9, -24, -68, 51]], ![![1176, -13, 72, 196, -136]], ![![-1560, 38, -77, -252, 196]], ![![1617, -13, 98, 277, -189]], ![![1792, -14, 111, 305, -207]]]
  g := ![![![-62, -119, -5, -71, 123], ![-292, -833, -68, -632, 988], ![280, 442, 7, 216, -412], ![213, 665, 59, 524, -807], ![-53, 243, 52, 316, -412]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 4 2 6 [57, 23, 26, 0, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [26, 34, 45, 53], [13, 7, 31, 70], [32, 29, 66, 19], [0, 1]]
 g := ![![[12, 17, 15, 10], [5, 4, 7, 16], [69, 52, 53, 50], [37], [1], []], ![[28, 31, 45, 31, 45, 34], [2, 12, 34, 8, 51, 59], [60, 53, 49, 64, 59, 21], [29, 3, 15], [43, 16, 54], [45, 13, 40]], ![[3, 16, 21, 14, 13, 56], [49, 63, 20, 6, 60, 44], [34, 22, 65, 37, 69, 31], [13, 69, 4], [22, 1, 10], [69, 9, 1]], ![[49, 69, 25, 52, 33, 37], [6, 56, 31, 68, 69, 10], [21, 17, 57, 60, 70, 8], [24, 36, 6], [50, 23, 32], [48, 23, 6]]]
 h' := ![![[26, 34, 45, 53], [70, 15, 11, 62], [43, 9, 63, 4], [4, 67, 46, 60], [14, 48, 45], [0, 0, 1], [0, 1]], ![[13, 7, 31, 70], [9, 63, 66, 52], [59, 1, 27, 30], [0, 67, 6, 22], [37, 65, 5, 50], [28, 63, 31, 14], [26, 34, 45, 53]], ![[32, 29, 66, 19], [23, 12, 67, 50], [34, 68, 49, 13], [26, 23, 1, 53], [25, 7, 35, 2], [70, 70, 4, 9], [13, 7, 31, 70]], ![[0, 1], [14, 52, 69, 49], [34, 64, 3, 24], [57, 56, 18, 7], [54, 22, 57, 19], [63, 9, 35, 48], [32, 29, 66, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [4, 5, 35], []]
 b := ![[], [], [59, 53, 25, 35], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 4
  hpos := by decide
  P := [57, 23, 26, 0, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![414202420, 211974139, 180830760, 192420770, 74188163]
  a := ![-4, -3, -4, -6, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-19243852, -59708671, -587799, -44310515, 74188163]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 25411681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![428, -9, 24, 68, -51]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![428, -9, 24, 68, -51]] 
 ![![71, 0, 0, 0, 0], ![52, 1, 0, 0, 0], ![68, 0, 1, 0, 0], ![36, 0, 0, 1, 0], ![68, 0, 0, 0, 1]] where
  M :=![![![428, -9, 24, 68, -51], ![-1176, 13, -72, -196, 136], ![1560, -38, 77, 252, -196], ![-1617, 13, -98, -277, 189], ![1141, -41, 42, 182, -156]]]
  hmulB := by decide  
  f := ![![![1450, 1069, -14, -494, -123]], ![![1020, 781, 16, -356, -104]], ![![1248, 930, -3, -428, -112]], ![![795, 559, -32, -263, -51]], ![![1581, 1129, -48, -528, -112]]]
  g := ![![![4, -9, 24, 68, -51], ![12, 13, -72, -196, 136], ![36, -38, 77, 252, -196], ![21, 13, -98, -277, 189], ![63, -41, 42, 182, -156]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-1450, -1069, 14, 494, 123]] ![![428, -9, 24, 68, -51]]
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


def P73P0 : CertificateIrreducibleZModOfList' 73 5 2 6 [64, 72, 13, 1, 25, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [32, 8, 59, 72, 30], [21, 64, 50, 41, 49], [55, 12, 49, 44, 58], [13, 61, 61, 62, 9], [0, 1]]
 g := ![![[36, 46, 12, 37, 67], [19, 69, 4, 3], [22, 28, 59, 41], [20, 34, 40, 48, 1], [], []], ![[47, 14, 3, 55, 69, 51, 54, 43], [69, 8, 17, 41], [26, 17, 66, 12], [56, 60, 71, 21, 61, 39, 35, 5], [67, 33, 66, 46], [43, 15, 70, 24]], ![[50, 22, 57, 6, 36, 19, 40, 35], [48, 53, 15, 49], [43, 14, 43, 48], [17, 37, 50, 49, 28, 57, 32, 70], [42, 51, 27, 55], [17, 54, 57, 65]], ![[60, 27, 46, 9, 29, 70, 26, 68], [56, 44, 50, 19], [35, 40, 67, 19], [70, 24, 46, 33, 28, 68, 18, 31], [7, 54, 3, 57], [4, 53, 63, 6]], ![[21, 50, 49, 41, 63, 30, 53, 2], [0, 67, 43, 23], [53, 3, 4, 12], [42, 58, 31, 42, 35, 55, 37, 3], [60, 41, 35, 35], [31, 65, 40, 8]]]
 h' := ![![[32, 8, 59, 72, 30], [19, 54, 0, 36, 40], [40, 31, 29, 52, 52], [34, 34, 61, 10, 25], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[21, 64, 50, 41, 49], [49, 15, 43, 55, 46], [31, 38, 14, 58, 48], [69, 45, 30, 20, 42], [11, 50, 4, 37, 39], [24, 33, 57, 52, 51], [32, 8, 59, 72, 30]], ![[55, 12, 49, 44, 58], [70, 47, 25, 46, 18], [21, 6, 64, 26, 7], [27, 47, 70, 20, 11], [40, 8, 67, 52, 8], [10, 52, 45, 15, 37], [21, 64, 50, 41, 49]], ![[13, 61, 61, 62, 9], [70, 63, 13, 9, 7], [71, 6, 2, 48, 26], [11, 52, 8, 2, 26], [15, 3, 63, 64, 18], [68, 49, 43, 38, 38], [55, 12, 49, 44, 58]], ![[0, 1], [6, 40, 65, 0, 35], [58, 65, 37, 35, 13], [47, 41, 50, 21, 42], [56, 12, 12, 66, 7], [10, 12, 0, 41, 20], [13, 61, 61, 62, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35, 9, 10, 72], [], [], []]
 b := ![[], [19, 20, 43, 34, 56], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 5
  hpos := by decide
  P := [64, 72, 13, 1, 25, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3266684970966944, 1670004826213732, 1423257978928488, 1517006431330352, 586543332138440]
  a := ![28, 32, 24, 19, 64]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![44749109191328, 22876778441284, 19496684642856, 20780910018224, 8034840166280]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![247, 147, -76, -96, 30]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![247, 147, -76, -96, 30]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![0, 0, 79, 0, 0], ![0, 0, 0, 79, 0], ![53, 76, 8, 60, 1]] where
  M :=![![![247, 147, -76, -96, 30], ![568, 497, 202, -144, -192], ![-2102, -753, 507, 366, -144], ![306, -305, -240, 175, 128], ![1318, 383, -758, -392, 399]]]
  hmulB := by decide  
  f := ![![![-255, 9, -14, -36, 30]], ![![692, -7, 50, 108, -72]], ![![-814, 51, -29, -102, 108]], ![![894, -7, 66, 141, -92]], ![![1085, 0, 86, 176, -107]]]
  g := ![![![-17, -27, -4, -24, 30], ![136, 191, 22, 144, -192], ![70, 129, 21, 114, -144], ![-82, -127, -16, -95, 128], ![-251, -379, -50, -308, 399]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 4 2 6 [72, 43, 67, 7, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 8, 17, 10], [15, 11, 46, 57], [46, 59, 16, 12], [0, 1]]
 g := ![![[58, 73, 52, 22], [22, 50, 73, 1], [49, 42, 43, 52], [20, 13, 42, 49], [1], []], ![[12, 70, 75, 10, 65, 49], [65, 15, 66, 34, 46, 8], [50, 78, 54, 69, 43, 44], [77, 34, 2, 74, 10, 32], [60, 47, 55], [61, 35, 21]], ![[31, 3, 21, 45, 28, 57], [37, 39, 24, 78, 16, 75], [75, 6, 20, 17, 49, 70], [65, 52, 69, 3, 48, 35], [31, 10, 2], [57, 39, 10]], ![[22, 18, 69, 76, 50, 63], [49, 51, 69, 38, 43, 47], [76, 31, 26, 65, 43, 24], [50, 46, 46, 53], [17, 40, 76], [26, 8, 65]]]
 h' := ![![[11, 8, 17, 10], [75, 54, 63, 38], [27, 12, 39, 78], [61, 70, 5, 17], [7, 36, 12, 72], [0, 0, 1], [0, 1]], ![[15, 11, 46, 57], [26, 25, 71, 47], [35, 58, 19, 71], [73, 65, 16, 73], [50, 19, 37, 16], [74, 10, 49, 56], [11, 8, 17, 10]], ![[46, 59, 16, 12], [6, 12, 32, 78], [40, 74, 1, 54], [28, 8, 57, 77], [44, 23, 43, 70], [71, 48, 25, 70], [15, 11, 46, 57]], ![[0, 1], [49, 67, 71, 74], [17, 14, 20, 34], [52, 15, 1, 70], [10, 1, 66], [7, 21, 4, 32], [46, 59, 16, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [57, 70, 35], []]
 b := ![[], [], [53, 13, 64, 77], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 4
  hpos := by decide
  P := [72, 43, 67, 7, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![23435424384, 12483880427, 10599110182, 11226119030, 4725586032]
  a := ![-7, -18, -1, 12, -32]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2873678928, -4388109595, -344374406, -3446949910, 4725586032]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 38950081 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![255, -9, 14, 36, -30]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![255, -9, 14, 36, -30]] 
 ![![79, 0, 0, 0, 0], ![38, 1, 0, 0, 0], ![68, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![42, 0, 0, 0, 1]] where
  M :=![![![255, -9, 14, 36, -30], ![-692, 7, -50, -108, 72], ![814, -51, 29, 102, -108], ![-894, 7, -66, -141, 92], ![490, -67, -8, 40, -85]]]
  hmulB := by decide  
  f := ![![![-247, -147, 76, 96, -30]], ![![-126, -77, 34, 48, -12]], ![![-186, -117, 59, 78, -24]], ![![-7, 2, 4, -1, -2]], ![![-148, -83, 50, 56, -21]]]
  g := ![![![11, -9, 14, 36, -30], ![-6, 7, -50, -108, 72], ![66, -51, 29, 102, -108], ![-5, 7, -66, -141, 92], ![90, -67, -8, 40, -85]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![247, 147, -76, -96, 30]] ![![255, -9, 14, 36, -30]]
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

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![35, 18, 18, 16, 2]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![35, 18, 18, 16, 2]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![0, 0, 83, 0, 0], ![24, 81, 63, 1, 0], ![33, 25, 3, 0, 1]] where
  M :=![![![35, 18, 18, 16, 2], ![84, 51, 76, 84, 32], ![460, 190, 159, 208, 84], ![238, 150, 98, 85, 46], ![846, 444, 354, 344, 115]]]
  hmulB := by decide  
  f := ![![![2461, -66, 150, 360, -278]], ![![-6372, 169, -388, -932, 720]], ![![8252, -218, 501, 1208, -932]], ![![658, -17, 39, 97, -74]], ![![-575, 15, -35, -84, 65]]]
  g := ![![![-5, -16, -12, 16, 2], ![-36, -91, -64, 84, 32], ![-88, -226, -159, 208, 84], ![-40, -95, -65, 85, 46], ![-135, -365, -261, 344, 115]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [77, 58, 67, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 14, 16], [2, 68, 67], [0, 1]]
 g := ![![[30, 18, 41], [24, 64, 11], [11, 23], [64, 25], [32, 16, 1], []], ![[73, 11, 20, 27], [68, 61, 34, 11], [52, 78], [71, 59], [16, 31, 16, 31], [62, 7]], ![[57, 34, 55, 57], [81, 35, 6, 67], [14, 7], [30, 17], [56, 31, 72, 18], [11, 7]]]
 h' := ![![[14, 14, 16], [61, 49, 46], [12, 41, 29], [64, 36, 40], [26, 66, 5], [0, 0, 1], [0, 1]], ![[2, 68, 67], [66, 69, 11], [43, 10, 55], [48, 18, 59], [55, 54, 68], [70, 75, 68], [14, 14, 16]], ![[0, 1], [59, 48, 26], [49, 32, 82], [31, 29, 67], [10, 46, 10], [70, 8, 14], [2, 68, 67]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49, 23], []]
 b := ![[], [27, 13, 66], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [77, 58, 67, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-17358483, 937188, -144616, -5315928, 2221056]
  a := ![-12, 18, -14, -54, 18]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![444927, 4530132, 3952960, -5315928, 2221056]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 571787 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![328, -9, 20, 48, -37]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![328, -9, 20, 48, -37]] 
 ![![83, 0, 0, 0, 0], ![47, 1, 0, 0, 0], ![16, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![56, 0, 0, 0, 1]] where
  M :=![![![328, -9, 20, 48, -37], ![-848, 23, -52, -124, 96], ![1100, -28, 67, 160, -124], ![-1091, 29, -66, -159, 123], ![743, -21, 46, 110, -84]]]
  hmulB := by decide  
  f := ![![![146, 21, 10, 26, -17]], ![![78, 12, 6, 14, -9]], ![![36, 4, 3, 8, -4]], ![![-3, 1, 0, -1, 1]], ![![111, 17, 8, 20, -12]]]
  g := ![![![29, -9, 20, 48, -37], ![-75, 23, -52, -124, 96], ![96, -28, 67, 160, -124], ![-96, 29, -66, -159, 123], ![66, -21, 46, 110, -84]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1

def I83N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4, 1, 0, 2, -1]] i)))

def SI83N2: IdealEqSpanCertificate' Table ![![4, 1, 0, 2, -1]] 
 ![![83, 0, 0, 0, 0], ![75, 1, 0, 0, 0], ![51, 0, 1, 0, 0], ![50, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![4, 1, 0, 2, -1], ![-24, -3, 0, -8, 4], ![48, 2, 1, 16, -8], ![-53, -3, -2, -17, 9], ![65, 5, 2, 16, -10]]]
  hmulB := by decide  
  f := ![![![-46, -17, -6, -4, -1]], ![![-42, -16, -6, -4, -1]], ![![-30, -11, -5, -4, -1]], ![![-29, -11, -4, -3, -1]], ![![-9, -4, -2, -2, -1]]]
  g := ![![![-2, 1, 0, 2, -1], ![7, -3, 0, -8, 4], ![-11, 2, 1, 16, -8], ![13, -3, -2, -17, 9], ![-14, 5, 2, 16, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N2 : Nat.card (O ⧸ I83N2) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N2)

lemma isPrimeI83N2 : Ideal.IsPrime I83N2 := prime_ideal_of_norm_prime hp83.out _ NI83N2
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![35, 18, 18, 16, 2]] ![![328, -9, 20, 48, -37]]
  ![![46, 17, 6, 4, 1]] where
 M := ![![![46, 17, 6, 4, 1]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI83N1 : IdealMulLeCertificate' Table 
  ![![46, 17, 6, 4, 1]] ![![4, 1, 0, 2, -1]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0, 0, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0, 0, 0]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![0, 0, 89, 0, 0], ![0, 0, 0, 89, 0], ![0, 0, 0, 0, 89]] where
  M :=![![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![0, 0, 89, 0, 0], ![0, 0, 0, 89, 0], ![0, 0, 0, 0, 89]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 5 2 6 [64, 58, 67, 43, 4, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 31, 12, 85, 80], [44, 28, 50, 80, 81], [79, 28, 86, 78, 10], [41, 1, 30, 24, 7], [0, 1]]
 g := ![![[36, 35, 18, 24, 55], [39, 26, 45, 2], [41, 2, 3, 4], [41, 62, 43, 13, 16], [1], []], ![[65, 0, 44, 88, 27, 55, 79, 11], [37, 45, 74, 2], [0, 65, 81, 80], [61, 60, 4, 87, 67, 26, 22, 72], [0, 20, 79, 65, 62, 73, 7, 1], [58, 84, 15, 81]], ![[62, 23, 47, 10, 37, 68, 35, 87], [84, 26, 6, 11], [61, 77, 68, 21], [8, 48, 18, 77, 87, 6, 20, 45], [83, 65, 79, 21, 39, 62, 51, 68], [58, 3, 66, 64]], ![[15, 5, 82, 4, 87, 10, 69, 5], [32, 6, 9, 55], [33, 49, 20, 2], [10, 34, 24, 58, 8, 52, 19, 78], [87, 69, 10, 83, 39, 46, 0, 45], [32, 21, 3, 11]], ![[23, 20, 23, 14, 79, 71, 67, 46], [74, 3, 67, 72], [50, 4, 46, 84], [60, 7, 42, 81, 60, 7, 31, 76], [5, 18, 65, 0, 69, 1, 35, 66], [81, 20, 51, 49]]]
 h' := ![![[10, 31, 12, 85, 80], [49, 79, 55, 25, 12], [26, 0, 33, 47, 64], [46, 64, 20, 27, 2], [25, 31, 22, 46, 85], [0, 0, 1], [0, 1]], ![[44, 28, 50, 80, 81], [10, 56, 25, 31, 54], [81, 5, 59, 66, 64], [80, 1, 63, 12, 13], [73, 76, 45, 73, 9], [37, 68, 27, 16, 48], [10, 31, 12, 85, 80]], ![[79, 28, 86, 78, 10], [19, 53, 83, 12, 44], [12, 78, 67, 47, 10], [0, 44, 55, 5, 33], [20, 25, 2, 82, 36], [4, 65, 15, 22, 6], [44, 28, 50, 80, 81]], ![[41, 1, 30, 24, 7], [46, 87, 40, 18, 57], [74, 50, 45, 80, 12], [36, 56, 3, 3, 64], [18, 52, 5, 21, 41], [10, 67, 49, 40, 82], [79, 28, 86, 78, 10]], ![[0, 1], [34, 81, 64, 3, 11], [26, 45, 63, 27, 28], [17, 13, 37, 42, 66], [12, 83, 15, 45, 7], [57, 67, 86, 11, 42], [41, 1, 30, 24, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22, 47, 11, 69], [], [], []]
 b := ![[], [64, 56, 48, 12, 67], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 5
  hpos := by decide
  P := [64, 58, 67, 43, 4, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1182981383441583, 604504934738084, 514207629857981, 547997520350751, 211883632911081]
  a := ![34, 13, 25, 47, 42]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![13291925656647, 6792190277956, 5777613818629, 6157275509559, 2380714976529]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-118, -2, -6, -26, 17]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![-118, -2, -6, -26, 17]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![0, 0, 97, 0, 0], ![64, 39, 28, 1, 0], ![51, 31, 71, 0, 1]] where
  M :=![![![-118, -2, -6, -26, 17], ![396, 15, 18, 84, -52], ![-606, -3, -19, -134, 84], ![637, 10, 32, 149, -87], ![-573, -12, -22, -120, 88]]]
  hmulB := by decide  
  f := ![![![-20, 2, -2, -4, 3]], ![![68, 5, 6, 8, -8]], ![![-90, -1, 3, -6, 8]], ![![-11, 3, 2, -1, 1]], ![![-55, 2, 3, -4, 5]]]
  g := ![![![7, 5, -5, -26, 17], ![-24, -17, 14, 84, -52], ![38, 27, -23, -134, 84], ![-46, -32, 21, 149, -87], ![27, 20, -30, -120, 88]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [13, 88, 53, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [10, 83, 45], [34, 13, 52], [0, 1]]
 g := ![![[44, 18, 6], [20, 94], [20, 75], [73, 81], [34, 93], [1]], ![[50, 95, 68, 80], [22, 64], [88, 75], [29, 94], [8, 49], [26, 83, 24, 42]], ![[6, 92, 15, 57], [80, 33], [], [73, 95], [24, 79], [81, 70, 12, 55]]]
 h' := ![![[10, 83, 45], [42, 40, 43], [37, 12, 71], [54, 91, 47], [18, 27, 9], [84, 9, 44], [0, 1]], ![[34, 13, 52], [90, 67, 31], [45, 80, 8], [92, 61, 50], [88, 51, 71], [80, 96, 7], [10, 83, 45]], ![[0, 1], [28, 87, 23], [96, 5, 18], [22, 42], [1, 19, 17], [33, 89, 46], [34, 13, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [63, 35], []]
 b := ![[], [54, 34, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [13, 88, 53, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-245352, -119771, -89168, -98628, -39295]
  a := ![-4, 0, -4, -9, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![83205, 50978, 56313, -98628, -39295]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 912673 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-236, 7, -14, -34, 27]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![-236, 7, -14, -34, 27]] 
 ![![97, 0, 0, 0, 0], ![52, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![52, 0, 0, 1, 0], ![32, 0, 0, 0, 1]] where
  M :=![![![-236, 7, -14, -34, 27], ![620, -13, 40, 92, -68], ![-776, 30, -41, -108, 92], ![795, -17, 52, 119, -87], ![-507, 29, -20, -64, 66]]]
  hmulB := by decide  
  f := ![![![1366, 51, 48, 296, -183]], ![![688, 27, 24, 148, -92]], ![![156, 4, 7, 36, -22]], ![![655, 25, 22, 141, -87]], ![![525, 19, 18, 114, -70]]]
  g := ![![![4, 7, -14, -34, 27], ![-16, -13, 40, 92, -68], ![6, 30, -41, -108, 92], ![-21, -17, 52, 119, -87], ![-7, 29, -20, -64, 66]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1

def I97N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 3, 0, 2, -2]] i)))

def SI97N2: IdealEqSpanCertificate' Table ![![19, 3, 0, 2, -2]] 
 ![![97, 0, 0, 0, 0], ![73, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![72, 0, 0, 1, 0], ![75, 0, 0, 0, 1]] where
  M :=![![![19, 3, 0, 2, -2], ![-48, 3, 2, -12, 4], ![50, -13, 9, 26, -12], ![-76, -3, -8, -19, 14], ![108, 15, -6, 10, -7]]]
  hmulB := by decide  
  f := ![![![1975, -45, 126, 294, -218]], ![![1435, -32, 92, 214, -158]], ![![131, -2, 9, 20, -14]], ![![1400, -31, 90, 209, -154]], ![![1577, -34, 102, 236, -173]]]
  g := ![![![-2, 3, 0, 2, -2], ![3, 3, 2, -12, 4], ![0, -13, 9, 26, -12], ![5, -3, -8, -19, 14], ![-12, 15, -6, 10, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N2 : Nat.card (O ⧸ I97N2) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N2)

lemma isPrimeI97N2 : Ideal.IsPrime I97N2 := prime_ideal_of_norm_prime hp97.out _ NI97N2
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![-118, -2, -6, -26, 17]] ![![-236, 7, -14, -34, 27]]
  ![![1975, -45, 126, 294, -218]] where
 M := ![![![1975, -45, 126, 294, -218]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI97N1 : IdealMulLeCertificate' Table 
  ![![1975, -45, 126, 294, -218]] ![![19, 3, 0, 2, -2]]
  ![![97, 0, 0, 0, 0]] where
 M := ![![![97, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139409, -3769, 8500, 20314, -15722]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![139409, -3769, 8500, 20314, -15722]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![0, 0, 101, 0, 0], ![0, 0, 0, 101, 0], ![87, 5, 48, 39, 1]] where
  M :=![![![139409, -3769, 8500, 20314, -15722], ![-360328, 9725, -21982, -52516, 40628], ![465554, -12605, 28371, 67826, -52516], ![-462316, 12473, -28204, -67381, 52126], ![315156, -8569, 19182, 45898, -35569]]]
  hmulB := by decide  
  f := ![![![33, 11, -2, -2, -2]], ![![-52, 15, 14, -16, -4]], ![![-34, -59, 25, 50, -16]], ![![-64, -7, -22, -21, 22]], ![![-13, -20, 2, 13, -1]]]
  g := ![![![14923, 741, 7556, 6272, -15722], ![-38564, -1915, -19526, -16208, 40628], ![49846, 2475, 25239, 20950, -52516], ![-49478, -2457, -25052, -20795, 52126], ![33759, 1676, 17094, 14189, -35569]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 4 2 6 [17, 66, 28, 34, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [35, 81, 77, 59], [53, 52, 92, 54], [80, 68, 33, 89], [0, 1]]
 g := ![![[93, 76], [100, 40, 96], [89, 43, 18, 22], [34, 96, 25], [17, 67, 1], []], ![[59, 100, 52, 70, 55, 98], [94, 77, 16], [14, 78, 82, 65, 20, 27], [75, 36, 82], [0, 68, 5], [87, 32, 90, 42, 1, 46]], ![[65, 58, 50, 5, 72, 68], [82, 8, 47], [6, 9, 37, 80, 23, 13], [25, 69, 1], [31, 86, 96], [14, 66, 73, 53, 80, 5]], ![[30, 17, 83, 75, 99, 10], [82, 99, 64], [87, 17, 86, 26, 36, 62], [22, 83, 17], [26, 62, 20], [4, 33, 73, 80, 86, 90]]]
 h' := ![![[35, 81, 77, 59], [21, 51, 51], [2, 40, 93, 46], [22, 82, 12, 74], [14, 62, 34, 5], [0, 0, 0, 1], [0, 1]], ![[53, 52, 92, 54], [40, 19, 20, 60], [27, 31, 65, 4], [74, 59, 43, 18], [95, 45, 80, 53], [87, 4, 40, 56], [35, 81, 77, 59]], ![[80, 68, 33, 89], [26, 10, 93, 45], [39, 35, 41, 59], [97, 73, 36, 42], [57, 13, 100, 100], [68, 40, 58, 55], [53, 52, 92, 54]], ![[0, 1], [25, 21, 38, 97], [56, 96, 3, 93], [51, 89, 10, 68], [18, 82, 89, 44], [64, 57, 3, 90], [80, 68, 33, 89]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [31, 48, 2], []]
 b := ![[], [], [32, 81, 87, 86], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 4
  hpos := by decide
  P := [17, 66, 28, 34, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![119698050666, 61714792820, 52929010172, 56308376160, 22017109032]
  a := ![15, 17, 12, 6, 36]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-17780103318, -478918340, -9939526964, -7944147288, 22017109032]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 104060401 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![33, 11, -2, -2, -2]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![33, 11, -2, -2, -2]] 
 ![![101, 0, 0, 0, 0], ![23, 1, 0, 0, 0], ![89, 0, 1, 0, 0], ![71, 0, 0, 1, 0], ![51, 0, 0, 0, 1]] where
  M :=![![![33, 11, -2, -2, -2], ![-52, 15, 14, -16, -4], ![-34, -59, 25, 50, -16], ![-64, -7, -22, -21, 22], ![204, 53, -36, -14, 3]]]
  hmulB := by decide  
  f := ![![![139409, -3769, 8500, 20314, -15722]], ![![28179, -762, 1718, 4106, -3178]], ![![127455, -3446, 7771, 18572, -14374]], ![![93423, -2526, 5696, 13613, -10536]], ![![73515, -1988, 4482, 10712, -8291]]]
  g := ![![![2, 11, -2, -2, -2], ![-3, 15, 14, -16, -4], ![-36, -59, 25, 50, -16], ![24, -7, -22, -21, 22], ![30, 53, -36, -14, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![139409, -3769, 8500, 20314, -15722]] ![![33, 11, -2, -2, -2]]
  ![![101, 0, 0, 0, 0]] where
 M := ![![![101, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-52, 106, -178, -132, 117]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![-52, 106, -178, -132, 117]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![0, 0, 0, 103, 0], ![11, 37, 2, 20, 1]] where
  M :=![![![-52, 106, -178, -132, 117], ![2452, 1047, 90, -336, -264], ![-3078, -175, 873, 78, -336], ![399, -952, -96, 585, 55], ![-263, -688, -1134, -10, 772]]]
  hmulB := by decide  
  f := ![![![-270, -14, -18, -66, 33]], ![![756, -21, 2, 156, -132]], ![![-1582, -139, -151, -414, 156]], ![![1317, -26, 12, 277, -223]], ![![451, -19, -4, 90, -83]]]
  g := ![![![-13, -41, -4, -24, 117], ![52, 105, 6, 48, -264], ![6, 119, 15, 66, -336], ![-2, -29, -2, -5, 55], ![-85, -284, -26, -150, 772]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 4 2 6 [35, 7, 66, 25, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [38, 6, 91, 14], [15, 62, 83, 19], [25, 34, 32, 70], [0, 1]]
 g := ![![[46, 97, 31, 98], [76, 48, 83, 52], [7, 31, 97, 58], [95, 98, 63], [44, 78, 1], []], ![[71, 5, 38, 85, 74, 8], [96, 53, 25, 70, 40, 9], [63, 30, 82, 58, 44, 61], [62, 20, 52], [22, 28, 34], [37, 100, 92, 81, 49, 66]], ![[65, 26, 70, 89, 71, 8], [81, 98, 90, 13, 14, 25], [29, 101, 96, 59, 81, 61], [4, 43, 8], [99, 98, 33], [37, 93, 86, 62, 93, 61]], ![[43, 46, 91, 101, 40, 40], [66, 19, 25, 92, 72, 43], [36, 63, 63, 32, 94, 12], [52, 84, 15], [43, 10, 18], [88, 0, 4, 73, 58, 10]]]
 h' := ![![[38, 6, 91, 14], [18, 30, 49, 60], [64, 15, 12, 19], [99, 30, 99, 77], [5, 52, 17, 28], [0, 0, 0, 1], [0, 1]], ![[15, 62, 83, 19], [29, 33, 66, 66], [4, 84, 25, 76], [16, 65, 75, 10], [34, 4, 52, 84], [17, 88, 39, 72], [38, 6, 91, 14]], ![[25, 34, 32, 70], [99, 73, 54, 43], [22, 74, 84, 34], [73, 1, 71, 19], [25, 76, 47, 76], [20, 20, 10, 41], [15, 62, 83, 19]], ![[0, 1], [88, 70, 37, 37], [37, 33, 85, 77], [57, 7, 64, 100], [69, 74, 90, 18], [82, 98, 54, 92], [25, 34, 32, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [12, 79, 53], []]
 b := ![[], [], [27, 23, 45, 46], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 4
  hpos := by decide
  P := [35, 7, 66, 25, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7434666044, 3898389591, 3336104618, 3550867447, 1451139871]
  a := ![6, 12, 2, -5, 22]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-82794879, -483434812, 4211892, -247300291, 1451139871]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 112550881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![270, 14, 18, 66, -33]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![270, 14, 18, 66, -33]] 
 ![![103, 0, 0, 0, 0], ![63, 1, 0, 0, 0], ![24, 0, 1, 0, 0], ![77, 0, 0, 1, 0], ![92, 0, 0, 0, 1]] where
  M :=![![![270, 14, 18, 66, -33], ![-756, 21, -2, -156, 132], ![1582, 139, 151, 414, -156], ![-1317, 26, -12, -277, 223], ![1725, 228, 226, 488, -120]]]
  hmulB := by decide  
  f := ![![![52, -106, 178, 132, -117]], ![![8, -75, 108, 84, -69]], ![![42, -23, 33, 30, -24]], ![![35, -70, 134, 93, -88]], ![![49, -88, 170, 118, -112]]]
  g := ![![![-30, 14, 18, 66, -33], ![-21, 21, -2, -156, 132], ![-275, 139, 151, 414, -156], ![-18, 26, -12, -277, 223], ![-433, 228, 226, 488, -120]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![-52, 106, -178, -132, 117]] ![![270, 14, 18, 66, -33]]
  ![![103, 0, 0, 0, 0]] where
 M := ![![![-103, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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


lemma PB519I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 103 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 103 (by omega)

def PB519I2 : PrimesBelowBoundCertificateInterval O 61 103 519 where
  m := 9
  g := ![3, 2, 1, 2, 3, 1, 3, 2, 2]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103]
  hP := PB519I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0, I67N1, I67N2]
    · exact ![I71N0, I71N1]
    · exact ![I73N0]
    · exact ![I79N0, I79N1]
    · exact ![I83N0, I83N1, I83N2]
    · exact ![I89N0]
    · exact ![I97N0, I97N1, I97N2]
    · exact ![I101N0, I101N1]
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
    · exact ![4489, 4489, 67]
    · exact ![25411681, 71]
    · exact ![2073071593]
    · exact ![38950081, 79]
    · exact ![571787, 83, 83]
    · exact ![5584059449]
    · exact ![912673, 97, 97]
    · exact ![104060401, 101]
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
      exact NI79N1
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
      exact NI83N1
      exact NI83N2
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
      exact NI97N2
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
  β := ![I67N2, I71N1, I79N1, I83N1, I83N2, I97N1, I97N2, I101N1, I103N1]
  Il := ![[I67N2], [I71N1], [], [I79N1], [I83N1, I83N2], [], [I97N1, I97N2], [I101N1], [I103N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
