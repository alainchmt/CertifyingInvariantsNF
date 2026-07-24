
import IdealArithmetic.Examples.NF5_3_379687500_1.RI5_3_379687500_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![303, 38, 58, -764, -2874]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![303, 38, 58, -764, -2874]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![0, 0, 67, 0, 0], ![45, 38, 56, 1, 0], ![35, 18, 52, 0, 1]] where
  M :=![![![303, 38, 58, -764, -2874], ![-1346, -461, 620, 4314, 16770], ![8142, 2968, -4289, -26662, -103902], ![-50578, -18520, 26884, 165869, 646530], ![27432, 10042, -14574, -89956, -350627]]]
  hmulB := by decide  
  f := ![![![-251, -1078, -1554, 724, 1746]], ![![298, 473, -652, 278, 726]], ![![170, 576, 581, -282, -666]], ![![141, 24, -922, 405, 1020]], ![![81, 10, -540, 236, 595]]]
  g := ![![![2019, 1206, 2870, -764, -2874], ![-11678, -6959, -16612, 4314, 16770], ![72306, 43080, 102861, -26662, -103902], ![-449899, -268046, -640020, 165869, 646530], ![243991, 145368, 347098, -89956, -350627]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [38, 63, 14, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 39, 13], [45, 27, 54], [0, 1]]
 g := ![![[28, 23, 59], [28, 14, 33], [42, 65], [40, 1], [53, 1], []], ![[0, 6, 38, 2], [8, 61, 61, 42], [33, 19], [29, 40], [65, 59], [55, 35]], ![[54, 54, 40, 56], [29, 20, 36, 37], [64, 24], [43, 60], [65, 47], [14, 35]]]
 h' := ![![[8, 39, 13], [8, 55, 40], [41, 64, 10], [37, 3, 47], [63, 40, 66], [0, 0, 1], [0, 1]], ![[45, 27, 54], [9, 58, 53], [58, 48, 30], [46, 55, 35], [64, 36, 24], [51, 50, 27], [8, 39, 13]], ![[0, 1], [27, 21, 41], [29, 22, 27], [60, 9, 52], [35, 58, 44], [19, 17, 39], [45, 27, 54]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27, 38], []]
 b := ![[], [31, 4, 28], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [38, 63, 14, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![69500366, -95132178, -181040094, -895578414, -1914604020]
  a := ![5, -3, -9, -44, -105]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1602711488, 1020891342, 2231802390, -895578414, -1914604020]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 300763 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1663, 4019, 642, -395, -740]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![1663, 4019, 642, -395, -740]] 
 ![![67, 0, 0, 0, 0], ![37, 1, 0, 0, 0], ![38, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![19, 0, 0, 0, 1]] where
  M :=![![![1663, 4019, 642, -395, -740], ![50, 1268, 3574, -1633, -4010], ![-744, -1583, 379, -127, -416], ![-162, -871, -1548, 716, 1738], ![204, 640, 534, -256, -601]]]
  hmulB := by decide  
  f := ![![![-538067, 224169, -977556, 439857, 1115452]], ![![-293623, 122329, -533452, 240030, 608702]], ![![-306714, 127783, -557235, 250733, 635844]], ![![-7355, 3066, -13362, 6019, 15254]], ![![-153223, 63835, -278374, 125255, 317643]]]
  g := ![![![-2343, 4019, 642, -395, -740], ![-1565, 1268, 3574, -1633, -4010], ![768, -1583, 379, -127, -416], ![853, -871, -1548, 716, 1738], ![-479, 640, 534, -256, -601]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1

def I67N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4017, 1673, -7298, 3283, 8326]] i)))

def SI67N2: IdealEqSpanCertificate' Table ![![-4017, 1673, -7298, 3283, 8326]] 
 ![![67, 0, 0, 0, 0], ![41, 1, 0, 0, 0], ![61, 0, 1, 0, 0], ![45, 0, 0, 1, 0], ![25, 0, 0, 0, 1]] where
  M :=![![![-4017, 1673, -7298, 3283, 8326], ![1760, -734, 3196, -1443, -3656], ![-770, 317, -1407, 601, 1546], ![344, -169, 574, -466, -1040], ![-320, 140, -568, 310, 749]]]
  hmulB := by decide  
  f := ![![![109, 211, 276, -385, -1286]], ![![59, 125, 174, -214, -702]], ![![141, 206, 227, -488, -1708]], ![![-189, 46, 324, 603, 2494]], ![![183, 131, 28, -611, -2301]]]
  g := ![![![249, 1673, -7298, 3283, 8326], ![-101, -734, 3196, -1443, -3656], ![95, 317, -1407, 601, 1546], ![287, -169, 574, -466, -1040], ![-61, 140, -568, 310, 749]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N2 : Nat.card (O ⧸ I67N2) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N2)

lemma isPrimeI67N2 : Ideal.IsPrime I67N2 := prime_ideal_of_norm_prime hp67.out _ NI67N2
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![303, 38, 58, -764, -2874]] ![![1663, 4019, 642, -395, -740]]
  ![![109, 211, 276, -385, -1286]] where
 M := ![![![109, 211, 276, -385, -1286]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![109, 211, 276, -385, -1286]] ![![-4017, 1673, -7298, 3283, 8326]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-369, 163, -714, 321, 814]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-369, 163, -714, 321, 814]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![18, 1, 3, 1, 0], ![59, 49, 46, 0, 1]] where
  M :=![![![-369, 163, -714, 321, 814], ![172, -48, 312, -141, -356], ![-74, 31, -115, 51, 130], ![28, -23, 54, -28, -68], ![-28, 16, -56, 26, 65]]]
  hmulB := by decide  
  f := ![![![1, 1, -4, 1, 2]], ![![0, 2, 2, 1, 8]], ![![6, 1, -3, -29, -94]], ![![0, 0, -1, 0, 2]], ![![5, 3, -4, -18, -57]]]
  g := ![![![-763, -564, -551, 321, 814], ![334, 247, 241, -141, -356], ![-122, -90, -88, 51, 130], ![64, 47, 46, -28, -68], ![-61, -45, -44, 26, 65]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [70, 22, 23, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [36, 30, 54], [12, 40, 17], [0, 1]]
 g := ![![[36, 63, 64], [7, 59, 20], [3, 25, 43], [30, 29], [48, 1], []], ![[29, 15, 27, 19], [21, 39, 65, 36], [28, 0, 15, 57], [21, 5], [24, 38], [1, 5]], ![[55, 59, 41, 62], [39, 29, 54, 59], [65, 27, 19, 53], [35, 19], [33, 48], [38, 5]]]
 h' := ![![[36, 30, 54], [7, 56, 8], [3, 40, 34], [62, 45, 16], [48, 10, 10], [0, 0, 1], [0, 1]], ![[12, 40, 17], [45, 9, 7], [30, 9, 41], [69, 67, 17], [30, 4, 17], [19, 13, 40], [36, 30, 54]], ![[0, 1], [5, 6, 56], [68, 22, 67], [35, 30, 38], [0, 57, 44], [40, 58, 30], [12, 40, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 43], []]
 b := ![[], [8, 58, 61], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [70, 22, 23, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![107774693450, -210958567279, -356530107820, -1739987627741, -3508762220148]
  a := ![59, -60, -118, -533, -1236]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3358373563120, 2443075744334, 2341781618341, -1739987627741, -3508762220148]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 357911 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 1, -4, 1, 2]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![1, 1, -4, 1, 2]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![39, 68, 1, 0, 0], ![46, 30, 0, 1, 0], ![20, 15, 0, 0, 1]] where
  M :=![![![1, 1, -4, 1, 2], ![0, 2, 2, 1, 8], ![6, 1, -3, -29, -94], ![-36, -23, 8, 68, 380], ![20, 10, -8, -52, -233]]]
  hmulB := by decide  
  f := ![![![-369, 163, -714, 321, 814]], ![![172, -48, 312, -141, -356]], ![![-39, 44, -95, 42, 108]], ![![-166, 85, -330, 148, 376]], ![![-68, 36, -136, 61, 155]]]
  g := ![![![1, 3, -4, 1, 2], ![-4, -4, 2, 1, 8], ![47, 35, -3, -29, -94], ![-156, -117, 8, 68, 380], ![104, 79, -8, -52, -233]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P1 : CertificateIrreducibleZModOfList' 71 2 2 6 [49, 40, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 70], [0, 1]]
 g := ![![[24, 29], [44, 32], [42, 1], [54], [38], [1]], ![[0, 42], [42, 39], [2, 70], [54], [38], [1]]]
 h' := ![![[31, 70], [45, 10], [1, 23], [41, 1], [42, 57], [22, 31], [0, 1]], ![[0, 1], [0, 61], [4, 48], [1, 70], [34, 14], [60, 40], [31, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [38, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N1 : CertifiedPrimeIdeal' SI71N1 71 where
  n := 2
  hpos := by decide
  P := [49, 40, 1]
  hirr := P71P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9981, 14445, 27001, 133284, 282647]
  a := ![4, -3, -7, -36, -83]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-180944, -141688, 27001, 133284, 282647]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N1 B_one_repr
lemma NI71N1 : Nat.card (O ⧸ I71N1) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-369, 163, -714, 321, 814]] ![![1, 1, -4, 1, 2]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0, 0, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0, 0, 0]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![0, 0, 73, 0, 0], ![0, 0, 0, 73, 0], ![0, 0, 0, 0, 73]] where
  M :=![![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![0, 0, 73, 0, 0], ![0, 0, 0, 73, 0], ![0, 0, 0, 0, 73]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 5 2 6 [46, 26, 12, 44, 64, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [50, 5, 5, 8, 48], [39, 47, 37, 66, 13], [57, 61, 46, 19, 45], [9, 32, 58, 53, 40], [0, 1]]
 g := ![![[37, 71, 30, 52, 67], [49, 45, 37, 48], [39, 23, 15, 71], [45, 71, 37, 9, 1], [], []], ![[30, 46, 64, 44, 17, 55, 33, 57], [68, 22, 22, 36], [10, 43, 4, 70], [29, 37, 33, 57, 13, 61, 40, 1], [36, 34, 33, 50], [64, 67, 42, 41]], ![[60, 5, 43, 37, 57, 5, 50, 5], [25, 25, 72, 9], [32, 56, 45, 61], [57, 55, 43, 28, 25, 55, 38, 13], [20, 5, 62, 1], [30, 5, 25, 23]], ![[55, 54, 46, 7, 37, 29, 11, 56], [15, 39, 30, 24], [36, 32, 0, 69], [7, 42, 65, 71, 72, 61, 65, 30], [49, 20, 70, 27], [22, 62, 6, 54]], ![[48, 61, 12, 5, 32, 6, 41, 44], [61, 37, 47, 57], [61, 42, 63, 6], [43, 30, 3, 56, 2, 29, 59, 21], [19, 25, 58, 41], [63, 54, 25, 67]]]
 h' := ![![[50, 5, 5, 8, 48], [27, 64, 56, 37, 33], [50, 37, 66, 8, 62], [47, 17, 0, 26, 61], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[39, 47, 37, 66, 13], [43, 66, 19, 46, 30], [55, 71, 12, 60, 6], [71, 25, 35, 46, 17], [59, 53, 3, 8, 53], [67, 61, 25, 19, 14], [50, 5, 5, 8, 48]], ![[57, 61, 46, 19, 45], [34, 55, 56, 39, 58], [4, 22, 23, 38, 70], [69, 64, 66, 57, 34], [54, 65, 23, 14, 72], [68, 28, 24, 63, 1], [39, 47, 37, 66, 13]], ![[9, 32, 58, 53, 40], [72, 37, 3, 6, 12], [55, 62, 21, 25, 43], [55, 49, 31, 24, 19], [28, 31, 64, 65, 5], [47, 26, 24, 68, 10], [57, 61, 46, 19, 45]], ![[0, 1], [41, 70, 12, 18, 13], [0, 27, 24, 15, 38], [18, 64, 14, 66, 15], [26, 70, 56, 59, 15], [30, 31, 72, 69, 48], [9, 32, 58, 53, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 7, 59, 7], [], [], []]
 b := ![[], [49, 49, 45, 47, 47], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 5
  hpos := by decide
  P := [46, 26, 12, 44, 64, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4412372792736362458, 10287460872628739777, 16568713563024564102, 80375043827058450348, 157696519601872913411]
  a := ![-26, 23, 50, 230, 547]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-60443462914196746, 140924121542859449, 226968678945541974, 1101027997630937676, 2160226295916067307]
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


def P79P0 : CertificateIrreducibleZModOfList' 79 5 2 6 [7, 69, 31, 20, 51, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 41, 14, 56, 78], [47, 25, 39, 46, 2], [19, 10, 37, 71, 26], [8, 2, 68, 64, 52], [0, 1]]
 g := ![![[63, 14, 70, 54, 18], [16, 66, 49, 27, 72], [43, 35, 71, 53, 9], [18, 24, 53, 28, 1], [], []], ![[2, 44, 38, 52, 10, 50, 18, 70], [25, 41, 28, 52, 21, 17, 37, 68], [5, 17, 2, 67, 73, 69, 49, 43], [51, 66, 37, 40, 68, 14, 60, 71], [11, 58, 38, 8], [43, 25, 74, 1]], ![[78, 55, 32, 55, 25, 38, 47, 62], [6, 17, 29, 34, 6, 61, 29, 72], [18, 38, 0, 60, 9, 1, 58, 45], [24, 73, 32, 51, 25, 73, 58, 38], [64, 61, 69, 16], [48, 52, 59, 4]], ![[36, 50, 61, 18, 66, 73, 21, 1], [0, 30, 28, 20, 24, 22, 18, 23], [50, 58, 58, 47, 48, 19, 74, 19], [48, 47, 66, 16, 23, 9, 75, 20], [3, 27, 34, 18], [77, 19, 26, 44]], ![[33, 29, 47, 43, 44, 54, 4, 19], [70, 75, 53, 24, 72, 59, 20, 13], [74, 68, 44, 13, 13, 35, 64, 52], [4, 17, 68, 44, 32, 32, 34, 19], [53, 68, 9, 31], [77, 42, 50, 18]]]
 h' := ![![[33, 41, 14, 56, 78], [46, 2, 67, 61, 52], [15, 24, 78, 25, 25], [32, 12, 22, 20, 76], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[47, 25, 39, 46, 2], [69, 76, 10, 40, 76], [59, 75, 9, 23, 66], [41, 49, 67, 32, 73], [6, 26, 8, 66, 18], [77, 38, 56, 71, 61], [33, 41, 14, 56, 78]], ![[19, 10, 37, 71, 26], [72, 68, 9, 49, 49], [30, 27, 75, 49, 6], [20, 60, 52, 75, 46], [2, 63, 57, 59, 63], [56, 17, 66, 77, 75], [47, 25, 39, 46, 2]], ![[8, 2, 68, 64, 52], [38, 4, 59, 22, 47], [70, 29, 72, 48, 22], [25, 42, 21, 45, 41], [63, 4, 41, 70, 63], [59, 69, 75, 76, 52], [19, 10, 37, 71, 26]], ![[0, 1], [16, 8, 13, 65, 13], [77, 3, 3, 13, 39], [74, 74, 75, 65, 1], [25, 65, 52, 42, 13], [78, 34, 39, 13, 49], [8, 2, 68, 64, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33, 66, 7, 72], [], [], []]
 b := ![[], [5, 45, 29, 48, 72], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 5
  hpos := by decide
  P := [7, 69, 31, 20, 51, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![69417120630579711, -42283393260430600, -117818871308981748, -602546084983298736, -1463598069696206304]
  a := ![11, -6, -16, -92, -232]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![878697729501009, -535232826081400, -1491378117835212, -7627165632699984, -18526557844255776]
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

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2197, -7156, -6569, 3129, 7392]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-2197, -7156, -6569, 3129, 7392]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![0, 0, 83, 0, 0], ![0, 0, 0, 83, 0], ![42, 13, 64, 78, 1]] where
  M :=![![![-2197, -7156, -6569, 3129, 7392], ![1134, 932, -5161, 2272, 5754], ![1210, 3406, 1994, -1061, -2394], ![-272, 149, 2617, -1679, -3864], ![-120, -713, -1416, 785, 1835]]]
  hmulB := by decide  
  f := ![![![-11183, 4659, -20317, 9142, 23184]], ![![4900, -2041, 8901, -4007, -10164]], ![![-2150, 893, -3898, 1766, 4494]], ![![962, -384, 1697, -840, -2226]], ![![-5656, 2370, -10317, 4580, 11537]]]
  g := ![![![-3767, -1244, -5779, -6909, 7392], ![-2898, -890, -4499, -5380, 5754], ![1226, 416, 1870, 2237, -2394], ![1952, 607, 3011, 3611, -3864], ![-930, -296, -1432, -1715, 1835]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 4 2 6 [37, 28, 0, 52, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [72, 68, 66, 79], [28, 63, 42, 45], [14, 34, 58, 42], [0, 1]]
 g := ![![[16, 31, 6, 70], [49, 8, 24, 63], [69, 28, 44], [15, 12, 63], [31, 1], []], ![[44, 78, 17, 42, 46, 6], [46, 71, 59, 15, 72, 39], [63, 29, 81], [9, 12, 7], [32, 28, 38, 29, 29, 66], [81, 51, 16]], ![[34, 78, 32, 18, 62, 35], [63, 71, 30, 60, 45, 35], [42, 80, 69], [28, 49, 26], [38, 63, 15, 42, 77, 82], [38, 72, 33]], ![[39, 80, 80, 24, 19, 34], [30, 82, 72, 81, 35, 24], [10, 20, 33], [59, 38, 38], [21, 24, 17, 40, 15, 34], [62, 45, 21]]]
 h' := ![![[72, 68, 66, 79], [13, 70, 58, 30], [24, 14, 24, 48], [2, 40, 43, 25], [15, 8, 55, 48], [0, 0, 1], [0, 1]], ![[28, 63, 42, 45], [40, 29, 65, 66], [63, 6, 51, 54], [30, 46, 18, 74], [23, 45, 9, 67], [29, 76, 73, 5], [72, 68, 66, 79]], ![[14, 34, 58, 42], [74, 53, 72, 50], [49, 68, 35, 33], [21, 25, 23, 22], [12, 47, 20, 62], [42, 49, 13, 15], [28, 63, 42, 45]], ![[0, 1], [21, 14, 54, 20], [48, 78, 56, 31], [13, 55, 82, 45], [72, 66, 82, 72], [60, 41, 79, 63], [14, 34, 58, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [70, 12, 45], []]
 b := ![[], [], [35, 56, 4, 82], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 4
  hpos := by decide
  P := [37, 28, 0, 52, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1017234217899, -371902880248, 541901361680, 3340241801616, 13010762778384]
  a := ![-4, 2, 8, 24, 84]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6596015312169, -2042311072280, -10025866463312, -12186738010992, 13010762778384]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 47458321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11183, 4659, -20317, 9142, 23184]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-11183, 4659, -20317, 9142, 23184]] 
 ![![83, 0, 0, 0, 0], ![61, 1, 0, 0, 0], ![14, 0, 1, 0, 0], ![59, 0, 0, 1, 0], ![48, 0, 0, 0, 1]] where
  M :=![![![-11183, 4659, -20317, 9142, 23184], ![4900, -2041, 8901, -4007, -10164], ![-2150, 893, -3898, 1766, 4494], ![962, -384, 1697, -840, -2226], ![-898, 365, -1604, 763, 1987]]]
  hmulB := by decide  
  f := ![![![-2197, -7156, -6569, 3129, 7392]], ![![-1601, -5248, -4890, 2327, 5502]], ![![-356, -1166, -1084, 515, 1218]], ![![-1565, -5085, -4638, 2204, 5208]], ![![-1272, -4147, -3816, 1819, 4297]]]
  g := ![![![-20038, 4659, -20317, 9142, 23184], ![8784, -2041, 8901, -4007, -10164], ![-3879, 893, -3898, 1766, 4494], ![1892, -384, 1697, -840, -2226], ![-1700, 365, -1604, 763, 1987]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-2197, -7156, -6569, 3129, 7392]] ![![-11183, 4659, -20317, 9142, 23184]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![915, 340, -492, -3012, -11742]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![915, 340, -492, -3012, -11742]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![0, 0, 89, 0, 0], ![0, 0, 0, 89, 0], ![19, 27, 7, 32, 1]] where
  M :=![![![915, 340, -492, -3012, -11742], ![-5718, -2097, 3046, 18756, 73110], ![35598, 13038, -18939, -116762, -455118], ![-221594, -81164, 117870, 726815, 2833002], ![120172, 44016, -63922, -394158, -1536359]]]
  hmulB := by decide  
  f := ![![![-29, -36, -16, 8, 18]], ![![2, -21, -30, 12, 30]], ![![6, 14, -15, -6, -6]], ![![6, 0, 2, -81, -150]], ![![-3, -13, -13, -24, -41]]]
  g := ![![![2517, 3566, 918, 4188, -11742], ![-15672, -22203, -5716, -26076, 73110], ![97560, 138216, 35583, 162326, -455118], ![-607288, -860362, -221496, -1010441, 2833002], ![329337, 466581, 120119, 547970, -1536359]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 4 2 6 [73, 9, 51, 68, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [87, 64, 5, 77], [28, 24, 37, 19], [84, 0, 47, 82], [0, 1]]
 g := ![![[11, 29, 57, 32], [45, 57, 79], [0, 40, 47], [85, 46, 53, 88], [21, 1], []], ![[29, 82, 64, 40, 42, 83], [23, 74, 22], [54, 50, 81], [14, 22, 53, 41, 53, 86], [85, 71, 12, 67, 69, 43], [64, 56, 55]], ![[29, 35, 57, 60, 67, 48], [75, 72, 34], [3, 6, 25], [28, 1, 78, 70, 60, 58], [38, 38, 12, 73, 48, 33], [26, 87, 5]], ![[22, 77, 79, 3, 25, 52], [79, 62, 85], [16, 28, 40], [28, 34, 17, 68, 7, 59], [81, 75, 67, 84, 5, 60], [25, 15, 49]]]
 h' := ![![[87, 64, 5, 77], [12, 15, 57, 11], [2, 55, 0, 48], [25, 15, 82, 74], [69, 5, 77, 34], [0, 0, 1], [0, 1]], ![[28, 24, 37, 19], [29, 1, 63, 32], [62, 84, 69, 72], [55, 6, 67, 80], [29, 70, 4, 44], [49, 64, 31, 16], [87, 64, 5, 77]], ![[84, 0, 47, 82], [53, 55, 11, 60], [59, 10, 25, 37], [79, 43, 43, 84], [48, 14, 33, 73], [43, 10, 85, 61], [28, 24, 37, 19]], ![[0, 1], [27, 18, 47, 75], [86, 29, 84, 21], [39, 25, 75, 29], [8, 0, 64, 27], [69, 15, 61, 12], [84, 0, 47, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [43, 24, 35], []]
 b := ![[], [], [85, 0, 6, 45], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 4
  hpos := by decide
  P := [73, 9, 51, 68, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-242145653523, 486994586698, 816596416631, 3981435062389, 7994171661809]
  a := ![-4, 8, 13, 41, 97]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1709341654246, -2419726295305, -619579833888, -2829573686691, 7994171661809]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 62742241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 36, 16, -8, -18]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![29, 36, 16, -8, -18]] 
 ![![89, 0, 0, 0, 0], ![8, 1, 0, 0, 0], ![25, 0, 1, 0, 0], ![67, 0, 0, 1, 0], ![81, 0, 0, 0, 1]] where
  M :=![![![29, 36, 16, -8, -18], ![-2, 21, 30, -12, -30], ![-6, -14, 15, 6, 6], ![-6, 0, -2, 81, 150], ![4, 4, 2, -22, -41]]]
  hmulB := by decide  
  f := ![![![-915, -340, 492, 3012, 11742]], ![![-18, -7, 10, 60, 234]], ![![-657, -242, 351, 2158, 8412]], ![![1801, 656, -954, -5899, -22992]], ![![-2183, -804, 1166, 7170, 27949]]]
  g := ![![![15, 36, 16, -8, -18], ![26, 21, 30, -12, -30], ![-13, -14, 15, 6, 6], ![-197, 0, -2, 81, 150], ![53, 4, 2, -22, -41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![915, 340, -492, -3012, -11742]] ![![29, 36, 16, -8, -18]]
  ![![89, 0, 0, 0, 0]] where
 M := ![![![-89, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0, 0, 0]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0, 0, 0]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![0, 0, 97, 0, 0], ![0, 0, 0, 97, 0], ![0, 0, 0, 0, 97]] where
  M :=![![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![0, 0, 97, 0, 0], ![0, 0, 0, 97, 0], ![0, 0, 0, 0, 97]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 5 2 6 [65, 3, 91, 91, 95, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [21, 69, 96, 4, 90], [47, 23, 26, 96, 54], [57, 67, 84, 30, 51], [71, 34, 85, 64, 96], [0, 1]]
 g := ![![[34, 38, 35, 55, 85], [91, 49, 82, 95], [6, 91, 25, 6], [37, 90, 75, 3], [2, 1], []], ![[11, 57, 15, 53, 29, 33, 23, 20], [36, 29, 70, 72], [27, 18, 2, 93], [36, 5, 11, 36], [94, 4, 48, 35], [46, 63, 52, 34, 24, 76, 96, 45]], ![[22, 52, 77, 84, 85, 6, 24, 1], [10, 82, 17, 70], [66, 10, 24, 18], [63, 52, 19, 91], [45, 5, 68, 91], [82, 70, 14, 72, 46, 51, 48, 33]], ![[85, 33, 87, 68, 41, 23, 23, 21], [12, 53], [27, 43, 65, 50], [76, 2, 37, 85], [63, 72, 57, 11], [39, 48, 1, 61, 73, 76, 36, 52]], ![[38, 80, 3, 33, 63, 69, 15, 22], [53, 21, 55, 73], [1, 84, 23, 50], [56, 88, 71, 91], [73, 58, 78, 44], [81, 40, 81, 32, 36, 78, 93, 96]]]
 h' := ![![[21, 69, 96, 4, 90], [64, 11, 4, 39, 52], [16, 69, 60, 26, 80], [42, 83, 9, 10, 54], [64, 26, 9, 18, 10], [0, 0, 0, 1], [0, 1]], ![[47, 23, 26, 96, 54], [89, 90, 91, 54, 60], [2, 60, 34, 70, 84], [37, 40, 84, 42, 44], [90, 84, 4, 94, 91], [63, 45, 59, 94, 36], [21, 69, 96, 4, 90]], ![[57, 67, 84, 30, 51], [37, 72, 86, 2, 94], [69, 0, 88, 16, 78], [73, 47, 86, 83, 42], [71, 20, 22, 35, 24], [38, 88, 77, 34, 24], [47, 23, 26, 96, 54]], ![[71, 34, 85, 64, 96], [92, 39, 88, 92, 38], [22, 80, 90, 76], [15, 8, 63, 73, 27], [28, 10, 10, 19, 45], [7, 9, 54, 69, 60], [57, 67, 84, 30, 51]], ![[0, 1], [14, 79, 22, 7, 47], [8, 82, 19, 6, 49], [49, 16, 49, 83, 27], [87, 54, 52, 28, 24], [51, 52, 4, 93, 74], [71, 34, 85, 64, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 0, 58, 94], [], [], []]
 b := ![[], [9, 93, 33, 96, 55], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 5
  hpos := by decide
  P := [65, 3, 91, 91, 95, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![22951687428555, -101764675679413, -143834351260664, -685229323803522, -1230860349147575]
  a := ![2, -3, -4, -20, -43]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![236615334315, -1049120367829, -1482828363512, -7064219833026, -12689281949975]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![51, -27, 111, -22, -22]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![51, -27, 111, -22, -22]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![0, 0, 101, 0, 0], ![4, 20, 19, 1, 0], ![35, 96, 54, 0, 1]] where
  M :=![![![51, -27, 111, -22, -22], ![22, 29, -71, -131, -550], ![-288, -109, 186, 1002, 3848], ![1844, 714, -951, -5868, -23332], ![-1000, -379, 532, 3241, 12757]]]
  hmulB := by decide  
  f := ![![![-369, -1078, -711, 347, 802]], ![![108, -22, -839, 376, 940]], ![![188, 484, 166, -87, -188]], ![![42, 45, -159, 70, 178]], ![![75, -137, -957, 432, 1073]]]
  g := ![![![9, 25, 17, -22, -22], ![196, 549, 318, -131, -550], ![-1376, -3857, -2244, 1002, 3848], ![8336, 23346, 13569, -5868, -23332], ![-4559, -12771, -7425, 3241, 12757]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [73, 23, 28, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [44, 39, 4], [29, 61, 97], [0, 1]]
 g := ![![[16, 7, 96], [15, 37], [63, 98, 33], [14, 58], [41, 77], [1]], ![[26, 91, 18, 30], [26, 97], [22, 26, 71, 84], [35, 5], [23, 21], [21, 88, 80, 64]], ![[88, 86, 86, 13], [9, 65], [57, 80, 2, 52], [55, 56], [70, 100], [60, 75, 74, 37]]]
 h' := ![![[44, 39, 4], [3, 75, 55], [47, 88, 80], [56, 59, 72], [13, 26, 82], [28, 78, 73], [0, 1]], ![[29, 61, 97], [30, 20, 19], [3, 88, 81], [77, 59, 83], [62, 71, 56], [23, 31, 18], [44, 39, 4]], ![[0, 1], [86, 6, 27], [6, 26, 41], [9, 84, 47], [61, 4, 64], [11, 93, 10], [29, 61, 97]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53, 89], []]
 b := ![[], [59, 17, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [73, 23, 28, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-52688751, -9308582, 39961836, 228125940, 758612124]
  a := ![-3, 3, 13, 23, 66]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-272441751, -766322686, -448113720, 228125940, 758612124]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 1030301 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![369, 1078, 711, -347, -802]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![369, 1078, 711, -347, -802]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![99, 82, 1, 0, 0], ![63, 41, 0, 1, 0], ![3, 89, 0, 0, 1]] where
  M :=![![![369, 1078, 711, -347, -802], ![-108, 22, 839, -376, -940], ![-188, -484, -166, 87, 188], ![14, -101, -411, 185, 458], ![30, 131, 192, -89, -215]]]
  hmulB := by decide  
  f := ![![![-51, 27, -111, 22, 22]], ![![-22, -29, 71, 131, 550]], ![![-65, 4, -53, 118, 430]], ![![-59, -2, -31, 125, 468]], ![![-11, -21, 54, 84, 359]]]
  g := ![![![-453, 281, 711, -347, -802], ![-561, 300, 839, -376, -940], ![101, -71, -166, 87, 188], ![274, -146, -411, 185, 458], ![-126, 71, 192, -89, -215]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P1 : CertificateIrreducibleZModOfList' 101 2 2 6 [6, 70, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [31, 100], [0, 1]]
 g := ![![[79, 17], [56], [6, 17], [16], [96], [31, 1]], ![[0, 84], [56], [28, 84], [16], [96], [62, 100]]]
 h' := ![![[31, 100], [51, 57], [65, 64], [92, 57], [84, 4], [16, 46], [0, 1]], ![[0, 1], [0, 44], [29, 37], [41, 44], [6, 97], [28, 55], [31, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [72]]
 b := ![[], [48, 36]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N1 : CertifiedPrimeIdeal' SI101N1 101 where
  n := 2
  hpos := by decide
  P := [6, 70, 1]
  hirr := P101P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-52436, 32220, 89216, 456579, 1107993]
  a := ![-8, 5, 12, 68, 169]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-405676, -1233808, 89216, 456579, 1107993]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N1 B_one_repr
lemma NI101N1 : Nat.card (O ⧸ I101N1) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![51, -27, 111, -22, -22]] ![![369, 1078, 711, -347, -802]]
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


def P103P0 : CertificateIrreducibleZModOfList' 103 5 2 6 [82, 47, 80, 14, 74, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [38, 55, 90, 96, 94], [44, 35, 55, 86, 2], [4, 22, 41, 99, 60], [46, 93, 20, 28, 50], [0, 1]]
 g := ![![[95, 6, 99, 26, 50], [61, 79, 21, 10, 49], [95, 16, 11, 80, 23], [33, 55, 23, 9], [29, 1], []], ![[68, 38, 6, 27, 55, 8, 76, 71], [13, 56, 62, 86, 80, 77, 54, 11], [59, 92, 29, 66, 82, 75, 101, 75], [9, 48, 40, 55], [9, 11, 67, 49], [96, 54, 96, 7, 25, 34, 24, 95]], ![[22, 83, 76, 67, 34, 72, 88, 8], [29, 75, 90, 14, 17, 24, 49, 49], [64, 100, 15, 54, 65, 37, 75, 92], [17, 12, 15, 81], [89, 24, 92, 83], [42, 28, 47, 9, 57, 4, 28, 8]], ![[27, 61, 6, 72, 3, 43, 61, 49], [41, 14, 61, 46, 15, 78, 87, 30], [12, 11, 53, 98, 49, 66, 15, 15], [43, 3, 83, 97], [81, 97, 3, 60], [94, 2, 4, 79, 59, 15, 12, 9]], ![[93, 100, 67, 77, 94, 32, 36, 66], [94, 56, 23, 52, 36, 59, 62, 32], [10, 90, 93, 14, 51, 85, 73, 82], [35, 66, 86, 30], [57, 89, 1, 41], [34, 81, 16, 97, 96, 5, 1, 61]]]
 h' := ![![[38, 55, 90, 96, 94], [45, 30, 90, 7, 16], [38, 19, 20, 64, 96], [53, 70, 72, 98, 69], [94, 100, 2, 29, 3], [0, 0, 0, 1], [0, 1]], ![[44, 35, 55, 86, 2], [81, 25, 50, 19, 85], [36, 51, 19, 6, 57], [100, 99, 96, 50, 52], [80, 24, 67, 90, 40], [32, 42, 69, 82, 96], [38, 55, 90, 96, 94]], ![[4, 22, 41, 99, 60], [42, 78, 47, 61, 101], [40, 63, 25, 68, 30], [8, 8, 9, 31, 56], [28, 89, 7, 61, 94], [61, 14, 46, 59, 86], [44, 35, 55, 86, 2]], ![[46, 93, 20, 28, 50], [87, 49, 6, 9, 37], [95, 44, 86, 19, 84], [48, 101, 7, 84, 52], [22, 7, 97, 70, 32], [81, 79, 40, 66, 36], [4, 22, 41, 99, 60]], ![[0, 1], [11, 24, 13, 7, 70], [30, 29, 56, 49, 42], [23, 31, 22, 46, 80], [100, 89, 33, 59, 37], [97, 71, 51, 101, 91], [46, 93, 20, 28, 50]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61, 83, 79, 35], [], [], []]
 b := ![[], [50, 62, 56, 71, 84], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 5
  hpos := by decide
  P := [82, 47, 80, 14, 74, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-455665161232806, 1070884940888422, 1721204407102253, 8347380559111845, 16357625974548148]
  a := ![-4, 4, 7, 37, 88]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4423933604202, 10396941173674, 16710722399051, 81042529700115, 158811902665516]
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



lemma PB953I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 103 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 103 (by omega)

def PB953I2 : PrimesBelowBoundCertificateInterval O 61 103 953 where
  m := 9
  g := ![3, 2, 1, 1, 2, 2, 1, 2, 1]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103]
  hP := PB953I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0, I67N1, I67N2]
    · exact ![I71N0, I71N1]
    · exact ![I73N0]
    · exact ![I79N0]
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
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
    · exact ![300763, 67, 67]
    · exact ![357911, 5041]
    · exact ![2073071593]
    · exact ![3077056399]
    · exact ![47458321, 83]
    · exact ![62742241, 89]
    · exact ![8587340257]
    · exact ![1030301, 10201]
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
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
      exact NI83N1
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
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
  β := ![I67N1, I67N2, I83N1, I89N1]
  Il := ![[I67N1, I67N2], [], [], [], [I83N1], [I89N1], [], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
