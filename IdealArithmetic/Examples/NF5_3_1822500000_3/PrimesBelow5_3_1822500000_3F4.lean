
import IdealArithmetic.Examples.NF5_3_1822500000_3.RI5_3_1822500000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-317, 210, 14, -48, -47]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![-317, 210, 14, -48, -47]] 
 ![![157, 0, 0, 0, 0], ![0, 157, 0, 0, 0], ![0, 0, 157, 0, 0], ![117, 24, 23, 1, 0], ![81, 118, 33, 0, 1]] where
  M :=![![![-317, 210, 14, -48, -47], ![92, -126, 79, -108, -341], ![1148, 757, -138, 42, 409], ![-450, -24, 86, -117, -325], ![-68, -292, 28, 10, -87]]]
  hmulB := by decide  
  f := ![![![15, 14, -6, -22, -9]], ![![-8, 90, -71, -124, -219]], ![![628, 583, -258, -922, -393]], ![![101, 113, -56, -175, -107]], ![![135, 197, -110, -298, -249]]]
  g := ![![![58, 44, 17, -48, -47], ![257, 272, 88, -108, -341], ![-235, -309, -93, 42, 409], ![252, 262, 86, -117, -325], ![37, 62, 17, 10, -87]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [108, 9, 50, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [70, 138, 145], [37, 18, 12], [0, 1]]
 g := ![![[136, 42, 56], [142, 13], [16, 13, 44], [111, 14, 49], [148, 10, 127], [107, 1], []], ![[58, 35, 6, 9], [37, 58], [131, 101, 35, 48], [89, 108, 56, 124], [47, 63, 124, 110], [58, 10], [7, 144]], ![[130, 103, 55, 100], [132, 141], [89, 34, 109, 58], [110, 111, 35, 127], [64, 82, 56, 13], [123, 47], [140, 144]]]
 h' := ![![[70, 138, 145], [51, 108, 128], [156, 18, 22], [101, 116, 63], [30, 19, 7], [62, 28, 136], [0, 0, 1], [0, 1]], ![[37, 18, 12], [4, 89, 66], [111, 156, 23], [38, 107, 56], [67, 140, 55], [92, 6, 71], [62, 94, 18], [70, 138, 145]], ![[0, 1], [121, 117, 120], [54, 140, 112], [10, 91, 38], [89, 155, 95], [47, 123, 107], [65, 63, 138], [37, 18, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [146, 67], []]
 b := ![[], [91, 16, 71], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [108, 9, 50, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2606968066, 8005532557, -6885348145, -10717273104, -22293429440]
  a := ![-55, 82, -115, -139, -330]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![19471858406, 18444871089, 6212070731, -10717273104, -22293429440]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 3869893 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![175, 0, 52, -30, 264]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![175, 0, 52, -30, 264]] 
 ![![157, 0, 0, 0, 0], ![59, 1, 0, 0, 0], ![130, 0, 1, 0, 0], ![113, 0, 0, 1, 0], ![111, 0, 0, 0, 1]] where
  M :=![![![175, 0, 52, -30, 264], ![-1116, 1, -332, 192, -1680], ![7104, -12, 2117, -1224, 10704], ![-8728, 14, -2602, 1505, -13152], ![4868, -8, 1452, -840, 7337]]]
  hmulB := by decide  
  f := ![![![-269, -204, 88, 186, 168]], ![![-103, -83, 36, 78, 72]], ![![-242, -204, 93, 204, 192]], ![![-209, -178, 82, 179, 168]], ![![-187, -140, 60, 126, 113]]]
  g := ![![![-207, 0, 52, -30, 264], ![1317, 1, -332, 192, -1680], ![-8390, -12, 2117, -1224, 10704], ![10309, 14, -2602, 1505, -13152], ![-5751, -8, 1452, -840, 7337]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1

def I157N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![373, 750, -462, -1112, -1161]] i)))

def SI157N2: IdealEqSpanCertificate' Table ![![373, 750, -462, -1112, -1161]] 
 ![![157, 0, 0, 0, 0], ![118, 1, 0, 0, 0], ![49, 0, 1, 0, 0], ![101, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  M :=![![![373, 750, -462, -1112, -1161], ![2420, 4870, -2999, -7220, -7539], ![15716, 31619, -19470, -46874, -48945], ![14386, 28944, -17822, -42907, -44803], ![-1708, -3436, 2116, 5094, 5319]]]
  hmulB := by decide  
  f := ![![![-231, -254, 86, -66, -175]], ![![-170, -190, 63, -48, -131]], ![![-71, -81, 32, -24, -38]], ![![-161, -164, 50, -39, -136]], ![![3, -10, 6, -4, 8]]]
  g := ![![![350, 750, -462, -1112, -1161], ![2272, 4870, -2999, -7220, -7539], ![14749, 31619, -19470, -46874, -48945], ![13500, 28944, -17822, -42907, -44803], ![-1603, -3436, 2116, 5094, 5319]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N2 : Nat.card (O ⧸ I157N2) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N2)

lemma isPrimeI157N2 : Ideal.IsPrime I157N2 := prime_ideal_of_norm_prime hp157.out _ NI157N2
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![-317, 210, 14, -48, -47]] ![![175, 0, 52, -30, 264]]
  ![![-231, -254, 86, -66, -175]] where
 M := ![![![-231, -254, 86, -66, -175]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI157N1 : IdealMulLeCertificate' Table 
  ![![-231, -254, 86, -66, -175]] ![![373, 750, -462, -1112, -1161]]
  ![![157, 0, 0, 0, 0]] where
 M := ![![![157, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC157 : ContainsPrimesAboveP 157 ![I157N0, I157N1, I157N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
    exact isPrimeI157N1
    exact isPrimeI157N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 157 (by decide) (𝕀 ⊙ MulI157N0 ⊙ MulI157N1)
instance hp163 : Fact (Nat.Prime 163) := {out := by norm_num}

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-229, 2, 24, -30, -79]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![-229, 2, 24, -30, -79]] 
 ![![163, 0, 0, 0, 0], ![0, 163, 0, 0, 0], ![122, 25, 1, 0, 0], ![69, 75, 0, 1, 0], ![152, 74, 0, 0, 1]] where
  M :=![![![-229, 2, 24, -30, -79], ![256, -60, -15, 24, 35], ![-92, 149, -14, 6, 113], ![-58, -62, 10, -11, -101], ![184, -38, -6, 14, 49]]]
  hmulB := by decide  
  f := ![![![81, 150, -68, -184, -199]], ![![428, 832, -455, -1144, -1213]], ![![142, 271, -139, -358, -382]], ![![245, 474, -255, -645, -685]], ![![268, 514, -268, -686, -731]]]
  g := ![![![67, 46, 24, -30, -79], ![-30, -25, -15, 24, 35], ![-98, -51, -14, 6, 113], ![91, 49, 10, -11, -101], ![-46, -28, -6, 14, 49]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [100, 157, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 162], [0, 1]]
 g := ![![[101, 119], [59, 126], [57], [91], [49], [157, 36], [1]], ![[0, 44], [0, 37], [57], [91], [49], [47, 127], [1]]]
 h' := ![![[6, 162], [131, 114], [102, 146], [89, 63], [86, 55], [111, 7], [63, 6], [0, 1]], ![[0, 1], [0, 49], [0, 17], [141, 100], [90, 108], [153, 156], [99, 157], [6, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43]]
 b := ![[], [17, 103]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [100, 157, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![59940784, -154616353, 136326425, 206365570, 445379507]
  a := ![-689, 1003, -1441, -1754, -4137]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-604348420, -319007842, 136326425, 206365570, 445379507]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![251, 197, -69, 66, 255]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![251, 197, -69, 66, 255]] 
 ![![163, 0, 0, 0, 0], ![12, 1, 0, 0, 0], ![19, 0, 1, 0, 0], ![149, 0, 0, 1, 0], ![97, 0, 0, 0, 1]] where
  M :=![![![251, 197, -69, 66, 255], ![-888, -202, 137, -150, -483], ![1632, 45, -182, 222, 615], ![-608, 51, 53, -71, -171], ![-560, -134, 88, -96, -311]]]
  hmulB := by decide  
  f := ![![![-175, -155, 25, 174, 51]], ![![-12, -16, 5, 18, 15]], ![![-55, -44, 11, 60, 12]], ![![-145, -164, 44, 187, 120]], ![![-117, -89, 9, 102, 4]]]
  g := ![![![-217, 197, -69, 66, 255], ![418, -202, 137, -150, -483], ![-541, 45, -182, 222, 615], ![153, 51, 53, -71, -171], ![269, -134, 88, -96, -311]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1

def I163N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-77, -106, -10, 38, 61]] i)))

def SI163N2: IdealEqSpanCertificate' Table ![![-77, -106, -10, 38, 61]] 
 ![![163, 0, 0, 0, 0], ![23, 1, 0, 0, 0], ![123, 0, 1, 0, 0], ![160, 0, 0, 1, 0], ![26, 0, 0, 0, 1]] where
  M :=![![![-77, -106, -10, 38, 61], ![-168, -252, -25, 92, 151], ![-420, -595, -60, 218, 349], ![-90, -138, -12, 49, 87], ![120, 172, 16, -62, -105]]]
  hmulB := by decide  
  f := ![![![-167, -338, 214, 532, 569]], ![![-31, -62, 39, 96, 102]], ![![-171, -347, 218, 538, 572]], ![![-206, -416, 262, 647, 689]], ![![-22, -44, 28, 70, 75]]]
  g := ![![![-25, -106, -10, 38, 61], ![-61, -252, -25, 92, 151], ![-143, -595, -60, 218, 349], ![-34, -138, -12, 49, 87], ![42, 172, 16, -62, -105]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N2 : Nat.card (O ⧸ I163N2) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N2)

lemma isPrimeI163N2 : Ideal.IsPrime I163N2 := prime_ideal_of_norm_prime hp163.out _ NI163N2

def I163N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![483, 931, -499, -1264, -1342]] i)))

def SI163N3: IdealEqSpanCertificate' Table ![![483, 931, -499, -1264, -1342]] 
 ![![163, 0, 0, 0, 0], ![103, 1, 0, 0, 0], ![149, 0, 1, 0, 0], ![134, 0, 0, 1, 0], ![99, 0, 0, 0, 1]] where
  M :=![![![483, 931, -499, -1264, -1342], ![2840, 5617, -3282, -8050, -8458], ![17732, 35448, -21407, -51892, -54310], ![15954, 32045, -19635, -47353, -49474], ![-2000, -3958, 2316, 5678, 5965]]]
  hmulB := by decide  
  f := ![![![-43255, 63, -13129, 7634, -65862]], ![![-25623, 38, -7785, 4528, -39036]], ![![-50461, 73, -15258, 8862, -76668]], ![![-22136, 31, -6791, 3961, -33914]], ![![-33763, 51, -10207, 5928, -51289]]]
  g := ![![![1725, 931, -499, -1264, -1342], ![11223, 5617, -3282, -8050, -8458], ![72923, 35448, -21407, -51892, -54310], ![66774, 32045, -19635, -47353, -49474], ![-7919, -3958, 2316, 5678, 5965]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N3 : Nat.card (O ⧸ I163N3) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N3)

lemma isPrimeI163N3 : Ideal.IsPrime I163N3 := prime_ideal_of_norm_prime hp163.out _ NI163N3
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![-229, 2, 24, -30, -79]] ![![251, 197, -69, 66, 255]]
  ![![42393, -35381, 3165, -372, -14902]] where
 M := ![![![42393, -35381, 3165, -372, -14902]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI163N1 : IdealMulLeCertificate' Table 
  ![![42393, -35381, 3165, -372, -14902]] ![![-77, -106, -10, 38, 61]]
  ![![-404313, 27371, 36727, -48452, -119627]] where
 M := ![![![-404313, 27371, 36727, -48452, -119627]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI163N2 : IdealMulLeCertificate' Table 
  ![![-404313, 27371, 36727, -48452, -119627]] ![![483, 931, -499, -1264, -1342]]
  ![![163, 0, 0, 0, 0]] where
 M := ![![![-55583, 65526, 4564, -16952, -20049]]]
 hmul := by decide  
 g := ![![![![-341, 402, 28, -104, -123]]]]
 hle2 := by decide  


def PBC163 : ContainsPrimesAboveP 163 ![I163N0, I163N1, I163N2, I163N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI163N0
    exact isPrimeI163N1
    exact isPrimeI163N2
    exact isPrimeI163N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 163 (by decide) (𝕀 ⊙ MulI163N0 ⊙ MulI163N1 ⊙ MulI163N2)
instance hp167 : Fact (Nat.Prime 167) := {out := by norm_num}

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1667, 145, -201, 272, 754]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![1667, 145, -201, 272, 754]] 
 ![![167, 0, 0, 0, 0], ![0, 167, 0, 0, 0], ![103, 45, 1, 0, 0], ![101, 34, 0, 1, 0], ![30, 77, 0, 0, 1]] where
  M :=![![![1667, 145, -201, 272, 754], ![-2472, 97, 278, -118, -506], ![1788, -1612, 409, 1196, 1114], ![-642, -217, 343, 1007, 1278], ![-1536, 198, 92, -302, -575]]]
  hmulB := by decide  
  f := ![![![-3395, -6827, -279, 2258, 6034]], ![![-19620, -16203, -4108, 7358, -3074]], ![![-7219, -8808, -1206, 3404, 3514]], ![![-6479, -7480, -1128, 2951, 2460]], ![![-9390, -8631, -1872, 3736, -41]]]
  g := ![![![-166, -348, -201, 272, 754], ![-24, 183, 278, -118, -506], ![-1165, -877, 409, 1196, 1114], ![-1054, -888, 343, 1007, 1278], ![220, 303, 92, -302, -575]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [116, 160, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 166], [0, 1]]
 g := ![![[82, 36], [158, 49], [73, 85], [2], [8], [55, 49], [1]], ![[0, 131], [0, 118], [0, 82], [2], [8], [64, 118], [1]]]
 h' := ![![[7, 166], [42, 161], [49, 160], [149, 98], [61, 154], [133, 141], [51, 7], [0, 1]], ![[0, 1], [0, 6], [0, 7], [0, 69], [137, 13], [118, 26], [100, 160], [7, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [132]]
 b := ![[], [103, 66]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [116, 160, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![376232, -931685, 820474, 1235541, 2697282]
  a := ![-54, 80, -113, -137, -325]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1735573, -1721869, 820474, 1235541, 2697282]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-395, 53, 29, -42, -98]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![-395, 53, 29, -42, -98]] 
 ![![167, 0, 0, 0, 0], ![0, 167, 0, 0, 0], ![25, 9, 1, 0, 0], ![14, 17, 0, 1, 0], ![77, 63, 0, 0, 1]] where
  M :=![![![-395, 53, 29, -42, -98], ![308, -171, 12, 6, -14], ![68, 304, -121, 96, 142], ![-74, -111, 91, -73, 50], ![116, -108, -22, 22, -145]]]
  hmulB := by decide  
  f := ![![![3147, 4561, 435, -1684, -2722]], ![![7520, 10921, 982, -4126, -6598]], ![![985, 1430, 130, -538, -862]], ![![1056, 1534, 137, -581, -928]], ![![4257, 6178, 567, -2316, -3717]]]
  g := ![![![42, 40, 29, -42, -98], ![6, 3, 12, 6, -14], ![-55, -55, -121, 96, 142], ![-31, -17, 91, -73, 50], ![69, 53, -22, 22, -145]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P1 : CertificateIrreducibleZModOfList' 167 2 2 7 [120, 79, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [88, 166], [0, 1]]
 g := ![![[144, 127], [144, 24], [111, 11], [18], [115], [34, 62], [1]], ![[131, 40], [85, 143], [77, 156], [18], [115], [146, 105], [1]]]
 h' := ![![[88, 166], [88, 36], [40, 109], [126, 41], [68, 39], [95, 99], [47, 88], [0, 1]], ![[0, 1], [83, 131], [113, 58], [60, 126], [160, 128], [123, 68], [109, 79], [88, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [158, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N1 : CertifiedPrimeIdeal' SI167N1 167 where
  n := 2
  hpos := by decide
  P := [120, 79, 1]
  hirr := P167P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7770106, -19648751, 17391905, 26219974, 56867281]
  a := ![246, -359, 514, 624, 1475]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-30975376, -25176971, 17391905, 26219974, 56867281]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N1 B_one_repr
lemma NI167N1 : Nat.card (O ⧸ I167N1) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N1

def I167N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, -2, 20, -12, 93]] i)))

def SI167N2: IdealEqSpanCertificate' Table ![![59, -2, 20, -12, 93]] 
 ![![167, 0, 0, 0, 0], ![113, 1, 0, 0, 0], ![90, 0, 1, 0, 0], ![127, 0, 0, 1, 0], ![124, 0, 0, 0, 1]] where
  M :=![![![59, -2, 20, -12, 93], ![-396, 2, -123, 72, -609], ![2580, -3, 776, -450, 3909], ![-3186, 4, -952, 551, -4809], ![1788, -2, 530, -306, 2687]]]
  hmulB := by decide  
  f := ![![![517, 682, 152, -102, -267]], ![![355, 468, 107, -66, -180]], ![![282, 363, 104, -18, -111]], ![![383, 496, 134, -37, -162]], ![![380, 502, 110, -78, -199]]]
  g := ![![![-69, -2, 20, -12, 93], ![460, 2, -123, 72, -609], ![-2961, -3, 776, -450, 3909], ![3643, 4, -952, 551, -4809], ![-2036, -2, 530, -306, 2687]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N2 : Nat.card (O ⧸ I167N2) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N2)

lemma isPrimeI167N2 : Ideal.IsPrime I167N2 := prime_ideal_of_norm_prime hp167.out _ NI167N2
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![1667, 145, -201, 272, 754]] ![![-395, 53, 29, -42, -98]]
  ![![-560137, -109172, 82568, -91708, -289668]] where
 M := ![![![-560137, -109172, 82568, -91708, -289668]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI167N1 : IdealMulLeCertificate' Table 
  ![![-560137, -109172, 82568, -91708, -289668]] ![![59, -2, 20, -12, 93]]
  ![![167, 0, 0, 0, 0]] where
 M := ![![![-2535227, 866730, 80160, -187040, -162825]]]
 hmul := by decide  
 g := ![![![![-15181, 5190, 480, -1120, -975]]]]
 hle2 := by decide  


def PBC167 : ContainsPrimesAboveP 167 ![I167N0, I167N1, I167N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI167N0
    exact isPrimeI167N1
    exact isPrimeI167N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 167 (by decide) (𝕀 ⊙ MulI167N0 ⊙ MulI167N1)
instance hp173 : Fact (Nat.Prime 173) := {out := by norm_num}

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-959, 6, -308, 182, -1502]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![-959, 6, -308, 182, -1502]] 
 ![![173, 0, 0, 0, 0], ![0, 173, 0, 0, 0], ![17, 139, 1, 0, 0], ![7, 133, 0, 1, 0], ![20, 27, 0, 0, 1]] where
  M :=![![![-959, 6, -308, 182, -1502], ![6372, -3, 1928, -1120, 9694], ![-41016, 38, -12249, 7088, -61910], ![50472, -68, 15050, -8705, 76086], ![-28212, 50, -8394, 4852, -42459]]]
  hmulB := by decide  
  f := ![![![1085, 1662, -68, -970, -1298]], ![![3252, 5293, -988, -4288, -5150]], ![![2789, 4539, -845, -3674, -4414]], ![![2587, 4219, -806, -3447, -4130]], ![![620, 997, -158, -764, -933]]]
  g := ![![![191, 342, -308, 182, -1502], ![-1228, -2201, 1928, -1120, 9694], ![7837, 14055, -12249, 7088, -61910], ![-9631, -17275, 15050, -8705, 76086], ![5374, 9641, -8394, 4852, -42459]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [23, 43, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [130, 172], [0, 1]]
 g := ![![[47, 158], [14], [172, 37], [135, 78], [29], [148, 119], [1]], ![[0, 15], [14], [138, 136], [68, 95], [29], [48, 54], [1]]]
 h' := ![![[130, 172], [34, 37], [23, 138], [9, 146], [47, 50], [56, 78], [150, 130], [0, 1]], ![[0, 1], [0, 136], [144, 35], [132, 27], [146, 123], [162, 95], [96, 43], [130, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [128]]
 b := ![[], [165, 64]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [23, 43, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![141167, -291998, 264916, 384018, 881889]
  a := ![-31, 46, -64, -76, -185]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-142707, -647403, 264916, 384018, 881889]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2527, -5084, 3130, 7536, 7869]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![-2527, -5084, 3130, 7536, 7869]] 
 ![![173, 0, 0, 0, 0], ![0, 173, 0, 0, 0], ![80, 130, 1, 0, 0], ![41, 116, 0, 1, 0], ![138, 135, 0, 0, 1]] where
  M :=![![![-2527, -5084, 3130, 7536, 7869], ![-16404, -33004, 20321, 48924, 51087], ![-106500, -214263, 131926, 317622, 331653], ![-97478, -196126, 120762, 290737, 303591], ![11572, 23286, -14338, -34518, -36047]]]
  hmulB := by decide  
  f := ![![![1165, -524, -18, 78, 3]], ![![144, 928, -233, 204, 921]], ![![628, 447, -180, 186, 681]], ![![383, 500, -162, 157, 624]], ![![1042, 310, -197, 222, 724]]]
  g := ![![![-9525, -13575, 3130, 7536, 7869], ![-61838, -88131, 20321, 48924, 51087], ![-401452, -572150, 131926, 317622, 331653], ![-367481, -523731, 120762, 290737, 303591], ![43632, 62183, -14338, -34518, -36047]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P1 : CertificateIrreducibleZModOfList' 173 2 2 7 [165, 61, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [112, 172], [0, 1]]
 g := ![![[14, 10], [159], [23, 124], [92, 73], [21], [57, 88], [1]], ![[96, 163], [159], [71, 49], [137, 100], [21], [52, 85], [1]]]
 h' := ![![[112, 172], [9, 150], [11, 141], [44, 41], [158, 108], [110, 59], [8, 112], [0, 1]], ![[0, 1], [28, 23], [60, 32], [138, 132], [144, 65], [144, 114], [96, 61], [112, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [98]]
 b := ![[], [24, 49]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N1 : CertifiedPrimeIdeal' SI173N1 173 where
  n := 2
  hpos := by decide
  P := [165, 61, 1]
  hirr := P173P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![279437, -1093272, 919570, 1482558, 2929632]
  a := ![-56, 84, -118, -150, -336]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3111909, -3977540, 919570, 1482558, 2929632]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N1 B_one_repr
lemma NI173N1 : Nat.card (O ⧸ I173N1) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N1

def I173N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 2, 0, 8]] i)))

def SI173N2: IdealEqSpanCertificate' Table ![![5, 0, 2, 0, 8]] 
 ![![173, 0, 0, 0, 0], ![77, 1, 0, 0, 0], ![126, 0, 1, 0, 0], ![92, 0, 0, 1, 0], ![34, 0, 0, 0, 1]] where
  M :=![![![5, 0, 2, 0, 8], ![-32, -3, -6, 12, -40], ![184, -28, 79, 12, 344], ![-256, -28, -54, 85, -320], ![136, 2, 38, -28, 199]]]
  hmulB := by decide  
  f := ![![![3609, 328, -446, 520, 1528]], ![![1577, 149, -196, 228, 672]], ![![2654, 228, -325, 380, 1112]], ![![1916, 180, -238, 277, 816]], ![![690, 66, -86, 100, 295]]]
  g := ![![![-3, 0, 2, 0, 8], ![7, -3, -6, 12, -40], ![-118, -28, 79, 12, 344], ![68, -28, -54, 85, -320], ![-52, 2, 38, -28, 199]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N2 : Nat.card (O ⧸ I173N2) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N2)

lemma isPrimeI173N2 : Ideal.IsPrime I173N2 := prime_ideal_of_norm_prime hp173.out _ NI173N2
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![-959, 6, -308, 182, -1502]] ![![-2527, -5084, 3130, 7536, 7869]]
  ![![4829, 32, 1408, -886, 7183]] where
 M := ![![![4829, 32, 1408, -886, 7183]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI173N1 : IdealMulLeCertificate' Table 
  ![![4829, 32, 1408, -886, 7183]] ![![5, 0, 2, 0, 8]]
  ![![173, 0, 0, 0, 0]] where
 M := ![![![1485897, -346, 441496, -259154, 2234641]]]
 hmul := by decide  
 g := ![![![![8589, -2, 2552, -1498, 12917]]]]
 hle2 := by decide  


def PBC173 : ContainsPrimesAboveP 173 ![I173N0, I173N1, I173N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI173N0
    exact isPrimeI173N1
    exact isPrimeI173N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 173 (by decide) (𝕀 ⊙ MulI173N0 ⊙ MulI173N1)
instance hp179 : Fact (Nat.Prime 179) := {out := by norm_num}

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -12, -16, 12, -64]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![-1, -12, -16, 12, -64]] 
 ![![179, 0, 0, 0, 0], ![0, 179, 0, 0, 0], ![140, 67, 1, 0, 0], ![84, 159, 0, 1, 0], ![129, 58, 0, 0, 1]] where
  M :=![![![-1, -12, -16, 12, -64], ![280, 27, 84, -48, 464], ![-1952, -40, -545, 312, -2896], ![2360, 8, 684, -389, 3520], ![-1304, 20, -388, 224, -1937]]]
  hmulB := by decide  
  f := ![![![22989, 33268, 3280, -12116, -19712]], ![![54616, 79049, 7796, -28784, -46832]], ![![39148, 56657, 5587, -20632, -33568]], ![![59468, 86069, 8488, -31341, -50992]], ![![34055, 49286, 4860, -17948, -29201]]]
  g := ![![![53, 16, -16, 12, -64], ![-376, -139, 84, -48, 464], ![2356, 865, -545, 312, -2896], ![-2876, -1051, 684, -389, 3520], ![1587, 574, -388, 224, -1937]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [80, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [162, 178], [0, 1]]
 g := ![![[83, 47], [144, 19], [59], [100], [167, 39], [134, 110], [1]], ![[0, 132], [0, 160], [59], [100], [41, 140], [54, 69], [1]]]
 h' := ![![[162, 178], [115, 91], [11, 127], [163, 43], [65, 169], [20, 155], [99, 162], [0, 1]], ![[0, 1], [0, 88], [0, 52], [148, 136], [56, 10], [70, 24], [30, 17], [162, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [168, 104]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [80, 17, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![209250, -178361, 198137, 212838, 723553]
  a := ![-26, 45, -55, -58, -169]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-775121, -498664, 198137, 212838, 723553]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233889, -378, 69740, -40338, 352486]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![233889, -378, 69740, -40338, 352486]] 
 ![![179, 0, 0, 0, 0], ![0, 179, 0, 0, 0], ![136, 76, 1, 0, 0], ![164, 2, 0, 1, 0], ![146, 109, 0, 0, 1]] where
  M :=![![![233889, -378, 69740, -40338, 352486], ![-1490620, 2417, -444476, 257088, -2246486], ![9500120, -15398, 2832779, -1638504, 14317486], ![-11674512, 18924, -3481150, 2013527, -17594494], ![6513580, -10558, 1942246, -1123412, 9816533]]]
  hmulB := by decide  
  f := ![![![-13565, -27262, 16804, 40418, 42182]], ![![-87892, -177001, 109032, 262496, 274106]], ![![-50816, -102286, 63015, 151680, 158370]], ![![-16332, -32834, 20234, 48679, 50810]], ![![-64238, -129321, 79670, 191776, 200239]]]
  g := ![![![-302225, -243804, 69740, -40338, 352486], ![1926160, 1553829, -444476, 257088, -2246486], ![-12275956, -9902992, 2832779, -1638504, 14317486], ![15085696, 12169604, -3481150, 2013527, -17594494], ![-8416794, -6789813, 1942246, -1123412, 9816533]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P1 : CertificateIrreducibleZModOfList' 179 2 2 7 [11, 127, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [52, 178], [0, 1]]
 g := ![![[158, 121], [86, 149], [45], [135], [127, 82], [23, 19], [1]], ![[6, 58], [137, 30], [45], [135], [95, 97], [116, 160], [1]]]
 h' := ![![[52, 178], [128, 11], [159, 111], [98, 90], [35, 80], [105, 34], [168, 52], [0, 1]], ![[0, 1], [163, 168], [24, 68], [124, 89], [78, 99], [83, 145], [8, 127], [52, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [172]]
 b := ![[], [91, 86]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N1 : CertifiedPrimeIdeal' SI179N1 179 where
  n := 2
  hpos := by decide
  P := [11, 127, 1]
  hirr := P179P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![41801, -162197, 134941, 218076, 432339]
  a := ![-22, 31, -46, -58, -131]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-654727, -323904, 134941, 218076, 432339]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N1 B_one_repr
lemma NI179N1 : Nat.card (O ⧸ I179N1) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N1

def I179N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1699, -433, 269, -290, -952]] i)))

def SI179N2: IdealEqSpanCertificate' Table ![![-1699, -433, 269, -290, -952]] 
 ![![179, 0, 0, 0, 0], ![36, 1, 0, 0, 0], ![136, 0, 1, 0, 0], ![116, 0, 0, 1, 0], ![144, 0, 0, 0, 1]] where
  M :=![![![-1699, -433, 269, -290, -952], ![3228, 123, -372, 454, 1280], ![-4212, 586, 287, -416, -952], ![1198, -433, -21, 79, 120], ![2068, 122, -248, 290, 785]]]
  hmulB := by decide  
  f := ![![![36699103, 73835927, -45463253, -109454804, -114291568]], ![![8711868, 17527645, -10792358, -25983082, -27131264]], ![![36524468, 73484574, -45246913, -108933956, -113747704]], ![![31692614, 63763235, -39261159, -94522987, -98699920]], ![![28584184, 57509300, -35410402, -85252118, -89019375]]]
  g := ![![![827, -433, 269, -290, -952], ![-1048, 123, -372, 454, 1280], ![676, 586, 287, -416, -952], ![-38, -433, -21, 79, 120], ![-644, 122, -248, 290, 785]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N2 : Nat.card (O ⧸ I179N2) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N2)

lemma isPrimeI179N2 : Ideal.IsPrime I179N2 := prime_ideal_of_norm_prime hp179.out _ NI179N2
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![-1, -12, -16, 12, -64]] ![![233889, -378, 69740, -40338, 352486]]
  ![![-691311633, 1120542, -206138036, 119232038, -1041866470]] where
 M := ![![![-691311633, 1120542, -206138036, 119232038, -1041866470]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI179N1 : IdealMulLeCertificate' Table 
  ![![-691311633, 1120542, -206138036, 119232038, -1041866470]] ![![-1699, -433, 269, -290, -952]]
  ![![179, 0, 0, 0, 0]] where
 M := ![![![34669103239, -56307135, 10337724529, -5979422684, 52249044258]]]
 hmul := by decide  
 g := ![![![![193682141, -314565, 57752651, -33404596, 291894102]]]]
 hle2 := by decide  


def PBC179 : ContainsPrimesAboveP 179 ![I179N0, I179N1, I179N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI179N0
    exact isPrimeI179N1
    exact isPrimeI179N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 179 (by decide) (𝕀 ⊙ MulI179N0 ⊙ MulI179N1)
instance hp181 : Fact (Nat.Prime 181) := {out := by norm_num}

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1149, 1455, 135, -522, -841]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![1149, 1455, 135, -522, -841]] 
 ![![181, 0, 0, 0, 0], ![0, 181, 0, 0, 0], ![0, 0, 181, 0, 0], ![0, 0, 0, 181, 0], ![83, 150, 152, 88, 1]] where
  M :=![![![1149, 1455, 135, -522, -841], ![2320, 3556, 343, -1278, -2059], ![5680, 8213, 846, -3054, -5041], ![1396, 1945, 173, -681, -1067], ![-1728, -2364, -238, 872, 1425]]]
  hmulB := by decide  
  f := ![![![1, 1, -1, -2, -3]], ![![8, 10, -5, -14, -9]], ![![8, 59, -42, -86, -123]], ![![52, 55, -27, -85, -49]], ![![39, 85, -53, -126, -136]]]
  g := ![![![392, 705, 707, 406, -841], ![957, 1726, 1731, 994, -2059], ![2343, 4223, 4238, 2434, -5041], ![497, 895, 897, 515, -1067], ![-663, -1194, -1198, -688, 1425]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 4 2 7 [146, 161, 53, 66, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [63, 41, 130, 110], [65, 55, 15, 120], [168, 84, 36, 132], [0, 1]]
 g := ![![[38, 97, 27, 70], [17, 111, 106], [106, 23, 27, 87], [97, 52, 65], [68, 0, 45, 52], [115, 1], []], ![[162, 69, 148, 161, 61, 115], [52, 10, 87], [119, 28, 62, 50, 93, 90], [142, 9, 15], [90, 68, 136, 90, 117, 84], [8, 50, 117, 142, 149, 134], [107, 155, 154]], ![[76, 10, 53, 46, 80, 164], [165, 10, 70], [85, 146, 101, 19, 81, 123], [12, 146, 60], [53, 178, 57, 22, 55, 84], [29, 71, 105, 18, 134, 90], [106, 11, 101]], ![[22, 23, 29, 114, 143, 55], [90, 114, 129], [144, 175, 45, 112, 49, 1], [86, 115, 177], [179, 174, 33, 166], [30, 122, 64, 144, 37, 114], [47, 1, 48]]]
 h' := ![![[63, 41, 130, 110], [7, 141, 110, 147], [90, 102, 119, 58], [142, 28, 1, 79], [27, 132, 43, 101], [43, 163, 79, 140], [0, 0, 1], [0, 1]], ![[65, 55, 15, 120], [92, 86, 100, 164], [25, 97, 14, 102], [23, 13, 146, 72], [170, 77, 68, 14], [125, 179, 85, 153], [112, 61, 65, 15], [63, 41, 130, 110]], ![[168, 84, 36, 132], [178, 75, 103, 109], [106, 54, 65, 147], [87, 94, 64, 79], [145, 73, 41, 28], [113, 19, 15, 69], [152, 62, 35, 107], [65, 55, 15, 120]], ![[0, 1], [61, 60, 49, 123], [168, 109, 164, 55], [141, 46, 151, 132], [99, 80, 29, 38], [118, 1, 2], [4, 58, 80, 59], [168, 84, 36, 132]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [23, 40, 71], []]
 b := ![[], [], [121, 162, 28, 16], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 4
  hpos := by decide
  P := [146, 161, 53, 66, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3053975033783, -7952137384148, 6976966711221, 10564062424062, 22842529447237]
  a := ![33, -48, 69, 80, 195]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-10457878282248, -18974207483258, -19144129885463, -11047395187474, 22842529447237]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 1073283121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 1, -1, -2, -3]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![1, 1, -1, -2, -3]] 
 ![![181, 0, 0, 0, 0], ![35, 1, 0, 0, 0], ![42, 0, 1, 0, 0], ![110, 0, 0, 1, 0], ![105, 0, 0, 0, 1]] where
  M :=![![![1, 1, -1, -2, -3], ![8, 10, -5, -14, -9], ![8, 59, -42, -86, -123], ![52, 55, -27, -85, -49], ![-16, -6, 0, 12, -9]]]
  hmulB := by decide  
  f := ![![![1149, 1455, 135, -522, -841]], ![![235, 301, 28, -108, -174]], ![![298, 383, 36, -138, -223]], ![![706, 895, 83, -321, -517]], ![![657, 831, 77, -298, -480]]]
  g := ![![![3, 1, -1, -2, -3], ![13, 10, -5, -14, -9], ![122, 59, -42, -86, -123], ![76, 55, -27, -85, -49], ![-1, -6, 0, 12, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![1149, 1455, 135, -522, -841]] ![![1, 1, -1, -2, -3]]
  ![![181, 0, 0, 0, 0]] where
 M := ![![![181, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC181 : ContainsPrimesAboveP 181 ![I181N0, I181N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI181N0
    exact isPrimeI181N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 181 (by decide) (𝕀 ⊙ MulI181N0)
instance hp191 : Fact (Nat.Prime 191) := {out := by norm_num}

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3641407, 7326248, -4511016, -10860472, -11340392]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![3641407, 7326248, -4511016, -10860472, -11340392]] 
 ![![191, 0, 0, 0, 0], ![0, 191, 0, 0, 0], ![0, 0, 191, 0, 0], ![106, 181, 1, 1, 0], ![71, 1, 142, 0, 1]] where
  M :=![![![3641407, 7326248, -4511016, -10860472, -11340392], ![23640624, 47563215, -29286264, -70507984, -73623704], ![153478848, 308788280, -190131281, -457749520, -477977288], ![140488544, 282652736, -174038752, -419006041, -437521752], ![-16679632, -33558208, 20662912, 49746880, 51945175]]]
  hmulB := by decide  
  f := ![![![-895, -1048, -104, 392, 664]], ![![-1872, -2735, -248, 944, 1384]], ![![-3648, -6088, -591, 2288, 4408]], ![![-2298, -3213, -297, 1127, 1704]], ![![-3047, -4921, -478, 1848, 3527]]]
  g := ![![![10261881, 10389592, 8464320, -10860472, -11340392], ![66621832, 67450953, 54951768, -70507984, -73623704], ![432519976, 437902768, 356755985, -457749520, -477977288], ![395911902, 400839099, 326560503, -419006041, -437521752], ![-47005007, -47589993, -38771198, 49746880, 51945175]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 3 2 7 [75, 4, 20, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [118, 86, 20], [53, 104, 171], [0, 1]]
 g := ![![[57, 57, 86], [181, 136, 100], [131, 184, 23], [46, 72, 118], [0, 7, 180], [14, 171, 1], []], ![[90, 66, 144, 135], [87, 124, 129, 163], [189, 73, 23, 121], [141, 95, 176, 65], [152, 161, 71, 81], [24, 158, 133, 108], [24, 18]], ![[124, 92, 102, 140], [158, 67, 108, 70], [7, 39, 70, 62], [183, 122, 181, 11], [129, 34, 152, 73], [58, 91, 101, 105], [64, 18]]]
 h' := ![![[118, 86, 20], [177, 143, 75], [107, 145, 10], [179, 146, 65], [0, 96, 140], [96, 107, 107], [0, 0, 1], [0, 1]], ![[53, 104, 171], [1, 42, 155], [173, 38, 120], [20, 126, 130], [2, 187, 54], [112, 24, 89], [91, 132, 104], [118, 86, 20]], ![[0, 1], [153, 6, 152], [106, 8, 61], [169, 110, 187], [51, 99, 188], [156, 60, 186], [110, 59, 86], [53, 104, 171]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [134, 93], []]
 b := ![[], [33, 123, 24], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 3
  hpos := by decide
  P := [75, 4, 20, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![353437807, -1035227743, 895258208, 1383119984, 2907426889]
  a := ![28, -41, 58, 70, 167]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1846516176, -1331347496, -2164096754, 1383119984, 2907426889]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 6967871 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![895, 1048, 104, -392, -664]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![895, 1048, 104, -392, -664]] 
 ![![191, 0, 0, 0, 0], ![0, 191, 0, 0, 0], ![40, 186, 1, 0, 0], ![154, 67, 0, 1, 0], ![126, 179, 0, 0, 1]] where
  M :=![![![895, 1048, 104, -392, -664], ![1872, 2735, 248, -944, -1384], ![3648, 6088, 591, -2288, -4408], ![1568, 1472, 224, -553, -168], ![-1456, -1728, -256, 704, 807]]]
  hmulB := by decide  
  f := ![![![-3641407, -7326248, 4511016, 10860472, 11340392]], ![![-23640624, -47563215, 29286264, 70507984, 73623704]], ![![-24587912, -49469090, 30459775, 73333264, 76573832]], ![![-11964330, -24071363, 14821544, 35683527, 37260368]], ![![-24470206, -49232275, 30313960, 72982208, 76207263]]]
  g := ![![![737, 664, 104, -392, -664], ![1632, 1401, 248, -944, -1384], ![4648, 4390, 591, -2288, -4408], ![518, 141, 224, -553, -168], ![-1054, -763, -256, 704, 807]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P1 : CertificateIrreducibleZModOfList' 191 2 2 7 [81, 45, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [146, 190], [0, 1]]
 g := ![![[43, 158], [165, 65], [144, 34], [46, 50], [147, 51], [14, 115], [1]], ![[0, 33], [105, 126], [142, 157], [88, 141], [144, 140], [187, 76], [1]]]
 h' := ![![[146, 190], [5, 85], [178, 175], [94, 15], [126, 94], [12, 54], [110, 146], [0, 1]], ![[0, 1], [0, 106], [134, 16], [183, 176], [98, 97], [65, 137], [34, 45], [146, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [170]]
 b := ![[], [98, 85]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N1 : CertifiedPrimeIdeal' SI191N1 191 where
  n := 2
  hpos := by decide
  P := [81, 45, 1]
  hirr := P191P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2351, -7657, 5385, 11634, 14232]
  a := ![4, -4, 8, 13, 20]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-19909, -22703, 5385, 11634, 14232]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N1 B_one_repr
lemma NI191N1 : Nat.card (O ⧸ I191N1) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![3641407, 7326248, -4511016, -10860472, -11340392]] ![![895, 1048, 104, -392, -664]]
  ![![191, 0, 0, 0, 0]] where
 M := ![![![-191, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC191 : ContainsPrimesAboveP 191 ![I191N0, I191N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI191N0
    exact isPrimeI191N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 191 (by decide) (𝕀 ⊙ MulI191N0)
instance hp193 : Fact (Nat.Prime 193) := {out := by norm_num}

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29139, 58697, -36269, -87212, -91028]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![29139, 58697, -36269, -87212, -91028]] 
 ![![193, 0, 0, 0, 0], ![0, 193, 0, 0, 0], ![0, 0, 193, 0, 0], ![0, 0, 0, 193, 0], ![34, 77, 162, 182, 1]] where
  M :=![![![29139, 58697, -36269, -87212, -91028], ![189688, 381803, -235392, -566462, -591404], ![1232692, 2480478, -1528033, -3678200, -3840524], ![1128834, 2271223, -1398633, -3367133, -3515876], ![-133840, -269390, 166080, 399670, 417269]]]
  hmulB := by decide  
  f := ![![![-173, 39, 7, -14, -36]], ![![116, -95, 26, -14, 12]], ![![-76, 146, -137, 100, -228]], ![![198, -49, 129, -87, 428]], ![![138, 45, 18, -6, 209]]]
  g := ![![![16187, 36621, 76219, 85388, -91028], ![105168, 237927, 495192, 554762, -591404], ![682956, 1545082, 3215735, 3602576, -3840524], ![625226, 1414475, 2943903, 3298043, -3515876], ![-74202, -167871, -349386, -391416, 417269]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 4 2 7 [61, 33, 112, 70, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [46, 70, 149, 14], [75, 174, 56, 96], [2, 141, 181, 83], [0, 1]]
 g := ![![[91, 40, 75, 27], [54, 35, 97], [61, 187, 2], [13, 161, 191], [166, 19, 46], [156, 123, 1], []], ![[86, 51, 74, 118, 168, 24], [162, 115, 124], [160, 92, 24], [81, 153, 147], [117, 177, 63], [5, 101, 131], [131, 12, 162, 28, 138, 42]], ![[7, 57, 153, 143, 136, 16], [116, 77, 9], [119, 133, 93], [78, 20, 143], [112, 23, 191], [48, 23, 56], [28, 26, 25, 187, 99, 24]], ![[33, 39, 75, 40, 91, 134], [105, 2, 48], [148, 190, 175], [102, 81, 93], [81, 180, 49], [137, 121, 55], [28, 6, 88, 176, 23, 121]]]
 h' := ![![[46, 70, 149, 14], [130, 9, 113, 42], [170, 158, 83, 26], [113, 43, 5, 52], [110, 81, 82, 159], [134, 87, 24, 168], [0, 0, 0, 1], [0, 1]], ![[75, 174, 56, 96], [90, 1, 138, 150], [69, 70, 66, 33], [76, 161, 32, 88], [112, 131, 186, 95], [84, 165, 116, 177], [179, 37, 27, 18], [46, 70, 149, 14]], ![[2, 141, 181, 83], [34, 30, 23, 136], [82, 91, 43, 190], [59, 75, 164, 155], [125, 183, 126, 170], [3, 44, 126, 34], [6, 140, 122, 153], [75, 174, 56, 96]], ![[0, 1], [36, 153, 112, 58], [74, 67, 1, 137], [80, 107, 185, 91], [133, 184, 185, 155], [153, 90, 120, 7], [37, 16, 44, 21], [2, 141, 181, 83]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [54, 89, 38], []]
 b := ![[], [], [23, 121, 114, 76], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 4
  hpos := by decide
  P := [61, 33, 112, 70, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5107702457432239, -13186478347085778, 11582317273556844, 17510011000969338, 37943568869147481]
  a := ![-209, 318, -440, -518, -1261]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6657894503075555, -15206431509178455, -31788993987193446, -35690256596807628, 37943568869147481]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 1387488001 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, -39, -7, 14, 36]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![173, -39, -7, 14, 36]] 
 ![![193, 0, 0, 0, 0], ![137, 1, 0, 0, 0], ![145, 0, 1, 0, 0], ![139, 0, 0, 1, 0], ![122, 0, 0, 0, 1]] where
  M :=![![![173, -39, -7, 14, 36], ![-116, 95, -26, 14, -12], ![76, -146, 137, -100, 228], ![-198, 49, -129, 87, -428], ![140, 60, 50, -30, 323]]]
  hmulB := by decide  
  f := ![![![-29139, -58697, 36269, 87212, 91028]], ![![-21667, -43644, 26965, 64842, 67680]], ![![-28279, -56951, 35166, 84580, 88288]], ![![-26835, -54042, 33368, 80257, 83776]], ![![-17726, -35708, 22066, 53058, 55379]]]
  g := ![![![1, -39, -7, 14, 36], ![-51, 95, -26, 14, -12], ![-71, -146, 137, -100, 228], ![269, 49, -129, 87, -428], ![-262, 60, 50, -30, 323]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![29139, 58697, -36269, -87212, -91028]] ![![173, -39, -7, 14, 36]]
  ![![193, 0, 0, 0, 0]] where
 M := ![![![-193, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC193 : ContainsPrimesAboveP 193 ![I193N0, I193N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI193N0
    exact isPrimeI193N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 193 (by decide) (𝕀 ⊙ MulI193N0)
instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29063, -73, 8753, -5078, 44012]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![29063, -73, 8753, -5078, 44012]] 
 ![![197, 0, 0, 0, 0], ![0, 197, 0, 0, 0], ![0, 0, 197, 0, 0], ![51, 93, 168, 1, 0], ![66, 41, 153, 0, 1]] where
  M :=![![![29063, -73, 8753, -5078, 44012], ![-186204, 285, -55644, 32206, -280996], ![1188396, -1826, 354461, -205040, 1791452], ![-1460714, 2315, -435573, 251941, -2201532], ![815212, -1330, 243004, -140542, 1228355]]]
  hmulB := by decide  
  f := ![![![-5669, -11371, 6937, 16756, 17516]], ![![-36552, -73453, 45074, 108646, 113492]], ![![-236676, -475982, 292713, 705028, 736292]], ![![-221657, -445743, 274058, 660145, 689436]], ![![-193190, -388505, 238879, 575396, 600923]]]
  g := ![![![-13283, -6763, -29807, -5078, 44012], ![84858, 43279, 190488, 32206, -280996], ![-541068, -276054, -1214675, -205040, 1791452], ![664931, 339262, 1492755, 251941, -2201532], ![-371008, -189307, -832915, -140542, 1228355]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 3 2 7 [143, 50, 104, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [113, 55, 151], [177, 141, 46], [0, 1]]
 g := ![![[86, 96, 105], [22, 51], [131, 17, 93], [83, 96], [32, 25], [162, 178], [1]], ![[103, 123, 142, 8], [57, 114], [139, 11, 104, 21], [14, 16], [138, 70], [107, 42], [151, 186, 155, 179]], ![[122, 11, 101, 68], [141, 41], [24, 176, 158, 151], [0, 63], [92, 136], [169, 97], [130, 160, 195, 18]]]
 h' := ![![[113, 55, 151], [133, 5, 156], [179, 106, 53], [5, 64, 68], [60, 74, 80], [41, 52, 192], [54, 147, 93], [0, 1]], ![[177, 141, 46], [162, 137, 96], [165, 108, 36], [73, 126, 143], [156, 135, 193], [105, 114, 55], [146, 100, 47], [113, 55, 151]], ![[0, 1], [129, 55, 142], [1, 180, 108], [161, 7, 183], [84, 185, 121], [89, 31, 147], [5, 147, 57], [177, 141, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59, 192], []]
 b := ![[], [16, 58, 47], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 3
  hpos := by decide
  P := [143, 50, 104, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2183267173, 5096341643, -4538543088, -6730795947, -14979091908]
  a := ![-48, 74, -101, -119, -289]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![6749783716, 6320828086, 17350437756, -6730795947, -14979091908]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 7645373 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 67, -27, 26, 88]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![103, 67, -27, 26, 88]] 
 ![![197, 0, 0, 0, 0], ![24, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![36, 0, 0, 1, 0], ![147, 0, 0, 0, 1]] where
  M :=![![![103, 67, -27, 26, 88], ![-300, -63, 56, -58, -128], ![396, 2, -111, 104, -56], ![6, 23, 79, -59, 264], ![-324, -42, -4, -14, -285]]]
  hmulB := by decide  
  f := ![![![-24037, -34727, -3579, 12404, 20368]], ![![-3216, -4645, -482, 1654, 2720]], ![![-2499, -3599, -400, 1240, 2072]], ![![-4530, -6533, -703, 2287, 3792]], ![![-17739, -25629, -2639, 9158, 15035]]]
  g := ![![![-76, 67, -27, 26, 88], ![108, -63, 56, -58, -128], ![33, 2, -111, 104, -56], ![-195, 23, 79, -59, 264], ![219, -42, -4, -14, -285]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1

def I197N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-87, -27, -25, 22, -102]] i)))

def SI197N2: IdealEqSpanCertificate' Table ![![-87, -27, -25, 22, -102]] 
 ![![197, 0, 0, 0, 0], ![151, 1, 0, 0, 0], ![51, 0, 1, 0, 0], ![87, 0, 0, 1, 0], ![112, 0, 0, 0, 1]] where
  M :=![![![-87, -27, -25, 22, -102], ![452, -51, 138, -62, 774], ![-3220, -136, -935, 580, -4614], ![3806, -35, 1133, -645, 5774], ![-2100, 46, -632, 354, -3227]]]
  hmulB := by decide  
  f := ![![![-448067, -901517, 555091, 1336412, 1395470]], ![![-358209, -720720, 443769, 1068398, 1115612]], ![![-211865, -426267, 262466, 631900, 659824]], ![![-285631, -574686, 353852, 851917, 889564]], ![![-244320, -491576, 302678, 728714, 760917]]]
  g := ![![![75, -27, -25, 22, -102], ![-407, -51, 138, -62, 774], ![2697, -136, -935, 580, -4614], ![-3245, -35, 1133, -645, 5774], ![1796, 46, -632, 354, -3227]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N2 : Nat.card (O ⧸ I197N2) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N2)

lemma isPrimeI197N2 : Ideal.IsPrime I197N2 := prime_ideal_of_norm_prime hp197.out _ NI197N2
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![29063, -73, 8753, -5078, 44012]] ![![103, 67, -27, 26, 88]]
  ![![-7808779, 4028, -2337582, 1353618, -11807292]] where
 M := ![![![-7808779, 4028, -2337582, 1353618, -11807292]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI197N1 : IdealMulLeCertificate' Table 
  ![![-7808779, 4028, -2337582, 1353618, -11807292]] ![![-87, -27, -25, 22, -102]]
  ![![197, 0, 0, 0, 0]] where
 M := ![![![38155381777, -61969305, 11377272247, -6580705412, 57503138094]]]
 hmul := by decide  
 g := ![![![![193682141, -314565, 57752651, -33404596, 291894102]]]]
 hle2 := by decide  


def PBC197 : ContainsPrimesAboveP 197 ![I197N0, I197N1, I197N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
    exact isPrimeI197N1
    exact isPrimeI197N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 197 (by decide) (𝕀 ⊙ MulI197N0 ⊙ MulI197N1)


lemma PB2088I4_primes (p : ℕ) :
  p ∈ Set.range ![157, 163, 167, 173, 179, 181, 191, 193, 197] ↔ Nat.Prime p ∧ 151 < p ∧ p ≤ 197 := by
  rw [← List.mem_ofFn']
  convert primes_range 151 197 (by omega)

def PB2088I4 : PrimesBelowBoundCertificateInterval O 151 197 2088 where
  m := 9
  g := ![3, 4, 3, 3, 3, 2, 2, 2, 3]
  P := ![157, 163, 167, 173, 179, 181, 191, 193, 197]
  hP := PB2088I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I157N0, I157N1, I157N2]
    · exact ![I163N0, I163N1, I163N2, I163N3]
    · exact ![I167N0, I167N1, I167N2]
    · exact ![I173N0, I173N1, I173N2]
    · exact ![I179N0, I179N1, I179N2]
    · exact ![I181N0, I181N1]
    · exact ![I191N0, I191N1]
    · exact ![I193N0, I193N1]
    · exact ![I197N0, I197N1, I197N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC157
    · exact PBC163
    · exact PBC167
    · exact PBC173
    · exact PBC179
    · exact PBC181
    · exact PBC191
    · exact PBC193
    · exact PBC197
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![3869893, 157, 157]
    · exact ![26569, 163, 163, 163]
    · exact ![27889, 27889, 167]
    · exact ![29929, 29929, 173]
    · exact ![32041, 32041, 179]
    · exact ![1073283121, 181]
    · exact ![6967871, 36481]
    · exact ![1387488001, 193]
    · exact ![7645373, 197, 197]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
      exact NI157N1
      exact NI157N2
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
      exact NI163N1
      exact NI163N2
      exact NI163N3
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
      exact NI167N2
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
      exact NI173N1
      exact NI173N2
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
      exact NI179N1
      exact NI179N2
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
      exact NI181N1
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
      exact NI197N1
      exact NI197N2
  β := ![I157N1, I157N2, I163N1, I163N2, I163N3, I167N2, I173N2, I179N2, I181N1, I193N1, I197N1, I197N2]
  Il := ![[I157N1, I157N2], [I163N1, I163N2, I163N3], [I167N2], [I173N2], [I179N2], [I181N1], [], [I193N1], [I197N1, I197N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
