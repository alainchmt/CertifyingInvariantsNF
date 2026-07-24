
import IdealArithmetic.Examples.NF5_3_1822500000_2.RI5_3_1822500000_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp467 : Fact (Nat.Prime 467) := {out := by norm_num}

def I467N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2333, 10352, -3499, -5587, -17012]] i)))

def SI467N0: IdealEqSpanCertificate' Table ![![2333, 10352, -3499, -5587, -17012]] 
 ![![467, 0, 0, 0, 0], ![0, 467, 0, 0, 0], ![76, 120, 1, 0, 0], ![220, 153, 0, 1, 0], ![431, 414, 0, 0, 1]] where
  M :=![![![2333, 10352, -3499, -5587, -17012], ![6024, 21353, -6223, -10657, -32146], ![4200, 39570, -17250, -24737, -76506], ![55080, 99066, -6593, -30004, -83146], ![-22392, -57066, 11464, 23972, 70603]]]
  hmulB := by decide  
  f := ![![![-2321, 104, -1881, -1547, -4372]], ![![-6456, -101, -12271, -9279, -25826]], ![![-2140, -2, -3638, -2771, -7722]], ![![-3940, 43, -6140, -4705, -13124]], ![![-7613, -4, -12189, -9331, -26033]]]
  g := ![![![18907, 17833, -3499, -5587, -17012], ![35714, 33634, -6223, -10657, -32146], ![85078, 80445, -17250, -24737, -76506], ![92062, 85446, -6593, -30004, -83146], ![-78367, -73512, 11464, 23972, 70603]]]
  hle1 := by decide   
  hle2 := by decide  


def P467P0 : CertificateIrreducibleZModOfList' 467 2 2 8 [458, 356, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [111, 466], [0, 1]]
 g := ![![[168, 74], [232, 64], [430], [121], [382, 114], [112], [73, 319], [111, 1]], ![[443, 393], [331, 403], [430], [121], [427, 353], [112], [457, 148], [222, 466]]]
 h' := ![![[111, 466], [220, 298], [271, 8], [229, 373], [169, 456], [215, 54], [190, 255], [65, 188], [0, 1]], ![[0, 1], [141, 169], [225, 459], [69, 94], [349, 11], [138, 413], [8, 212], [385, 279], [111, 466]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [341]]
 b := ![[], [461, 404]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI467N0 : CertifiedPrimeIdeal' SI467N0 467 where
  n := 2
  hpos := by decide
  P := [458, 356, 1]
  hirr := P467P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![713678, 141346, 792151, 590155, 1767783]
  a := ![-180, -61, -183, -126, -395]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2036913, -1963753, 792151, 590155, 1767783]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI467N0 : Ideal.IsPrime I467N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI467N0 B_one_repr
lemma NI467N0 : Nat.card (O ⧸ I467N0) = 218089 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI467N0

def I467N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-31, -7, -5, -8, -26]] i)))

def SI467N1: IdealEqSpanCertificate' Table ![![-31, -7, -5, -8, -26]] 
 ![![467, 0, 0, 0, 0], ![39, 1, 0, 0, 0], ![347, 0, 1, 0, 0], ![10, 0, 0, 1, 0], ![334, 0, 0, 0, 1]] where
  M :=![![![-31, -7, -5, -8, -26], ![48, 11, 7, 11, 36], ![-72, -12, -14, -19, -62], ![120, 30, 27, 28, 98], ![0, -3, -2, 1, 1]]]
  hmulB := by decide  
  f := ![![![187, 95, 3, 16, 60]], ![![15, 8, 0, 1, 4]], ![![139, 71, 1, 11, 42]], ![![2, 4, -5, -4, -10]], ![![134, 67, 4, 13, 47]]]
  g := ![![![23, -7, -5, -8, -26], ![-32, 11, 7, 11, 36], ![56, -12, -14, -19, -62], ![-93, 30, 27, 28, 98], ![1, -3, -2, 1, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI467N1 : Nat.card (O ⧸ I467N1) = 467 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI467N1)

lemma isPrimeI467N1 : Ideal.IsPrime I467N1 := prime_ideal_of_norm_prime hp467.out _ NI467N1

def I467N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![65, 4, 107, 79, 218]] i)))

def SI467N2: IdealEqSpanCertificate' Table ![![65, 4, 107, 79, 218]] 
 ![![467, 0, 0, 0, 0], ![336, 1, 0, 0, 0], ![118, 0, 1, 0, 0], ![47, 0, 0, 1, 0], ![52, 0, 0, 0, 1]] where
  M :=![![![65, 4, 107, 79, 218], ![456, -1, 757, 569, 1582], ![3000, -126, 5150, 3895, 10802], ![21192, -738, 35763, 27068, 75310], ![-7296, 246, -12322, -9322, -25927]]]
  hmulB := by decide  
  f := ![![![131491, 48604, 24681, 38331, 125694]], ![![94056, 34799, 17663, 27429, 89946]], ![![34190, 12542, 6392, 9935, 32574]], ![![11671, 4522, 2246, 3471, 11392]], ![![14660, 5390, 2744, 4264, 13981]]]
  g := ![![![-62, 4, 107, 79, 218], ![-423, -1, 757, 569, 1582], ![-2799, -126, 5150, 3895, 10802], ![-19570, -738, 35763, 27068, 75310], ![6746, 246, -12322, -9322, -25927]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI467N2 : Nat.card (O ⧸ I467N2) = 467 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI467N2)

lemma isPrimeI467N2 : Ideal.IsPrime I467N2 := prime_ideal_of_norm_prime hp467.out _ NI467N2

def I467N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-301, 407, -460, -501, -1624]] i)))

def SI467N3: IdealEqSpanCertificate' Table ![![-301, 407, -460, -501, -1624]] 
 ![![467, 0, 0, 0, 0], ![439, 1, 0, 0, 0], ![150, 0, 1, 0, 0], ![464, 0, 0, 1, 0], ![391, 0, 0, 0, 1]] where
  M :=![![![-301, 407, -460, -501, -1624], ![2904, 2291, 1186, 474, 2042], ![-14880, -4098, -10073, -7786, -27208], ![92400, 43128, 53308, 35955, 130212], ![-26064, -13659, -14256, -9095, -33457]]]
  hmulB := by decide  
  f := ![![![400009, 103925, 63426, 102083, 332646]], ![![374669, 97386, 59420, 95631, 311624]], ![![130482, 33768, 20655, 33256, 108360]], ![![394720, 102836, 62668, 100831, 328580]], ![![334685, 86914, 53056, 85398, 278275]]]
  g := ![![![1622, 407, -460, -501, -1624], ![-4709, 2291, 1186, 474, 2042], ![37572, -4098, -10073, -7786, -27208], ![-202212, 43128, 53308, 35955, 130212], ![54412, -13659, -14256, -9095, -33457]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI467N3 : Nat.card (O ⧸ I467N3) = 467 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI467N3)

lemma isPrimeI467N3 : Ideal.IsPrime I467N3 := prime_ideal_of_norm_prime hp467.out _ NI467N3
def MulI467N0 : IdealMulLeCertificate' Table 
  ![![2333, 10352, -3499, -5587, -17012]] ![![-31, -7, -5, -8, -26]]
  ![![6061, 22955, -7040, -11759, -35586]] where
 M := ![![![6061, 22955, -7040, -11759, -35586]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI467N1 : IdealMulLeCertificate' Table 
  ![![6061, 22955, -7040, -11759, -35586]] ![![65, 4, 107, 79, 218]]
  ![![180173, 812315, -276963, -440506, -1342040]] where
 M := ![![![180173, 812315, -276963, -440506, -1342040]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI467N2 : IdealMulLeCertificate' Table 
  ![![180173, 812315, -276963, -440506, -1342040]] ![![-301, 407, -460, -501, -1624]]
  ![![467, 0, 0, 0, 0]] where
 M := ![![![702116287, 2402120042, -679997299, -1181334875, -3556779410]]]
 hmul := by decide  
 g := ![![![![1503461, 5143726, -1456097, -2529625, -7616230]]]]
 hle2 := by decide  


def PBC467 : ContainsPrimesAboveP 467 ![I467N0, I467N1, I467N2, I467N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI467N0
    exact isPrimeI467N1
    exact isPrimeI467N2
    exact isPrimeI467N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 467 (by decide) (𝕀 ⊙ MulI467N0 ⊙ MulI467N1 ⊙ MulI467N2)
instance hp479 : Fact (Nat.Prime 479) := {out := by norm_num}

def I479N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-127, -18, -84, -76, -222]] i)))

def SI479N0: IdealEqSpanCertificate' Table ![![-127, -18, -84, -76, -222]] 
 ![![479, 0, 0, 0, 0], ![0, 479, 0, 0, 0], ![0, 0, 479, 0, 0], ![265, 132, 469, 1, 0], ![473, 408, 116, 0, 1]] where
  M :=![![![-127, -18, -84, -76, -222], ![-144, 47, -460, -332, -908], ![-2112, 60, -3305, -2532, -7056], ![-12960, 624, -22488, -17009, -47256], ![4584, -198, 7776, 5898, 16399]]]
  hmulB := by decide  
  f := ![![![79, 30, 12, 16, 54]], ![![-144, -23, -44, -52, -172]], ![![384, 156, 137, 108, 384]], ![![377, 162, 127, 99, 354]], ![![49, 48, 8, -2, 1]]]
  g := ![![![261, 210, 128, -76, -222], ![1080, 865, 544, -332, -908], ![8364, 6708, 4181, -2532, -7056], ![56047, 44940, 28051, -17009, -47256], ![-19447, -15594, -9730, 5898, 16399]]]
  hle1 := by decide   
  hle2 := by decide  


def P479P0 : CertificateIrreducibleZModOfList' 479 3 2 8 [117, 214, 100, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [285, 400, 89], [94, 78, 390], [0, 1]]
 g := ![![[452, 293, 10], [29, 126, 161], [155, 162, 375], [333, 386, 61], [352, 65, 384], [290, 173], [385, 321, 420], [1]], ![[111, 360, 131, 267], [355, 369, 227, 271], [422, 11, 192, 131], [178, 43, 284, 388], [431, 415, 347, 417], [415, 309], [266, 132, 210, 445], [12, 110, 328, 360]], ![[90, 380, 466, 475], [13, 299, 60, 31], [445, 259, 280, 273], [219, 103, 392, 376], [111, 192, 222, 285], [7, 305], [391, 57, 168, 238], [177, 136, 338, 119]]]
 h' := ![![[285, 400, 89], [439, 306, 197], [67, 465, 139], [317, 73, 422], [10, 18, 260], [440, 400, 87], [460, 80, 80], [362, 265, 379], [0, 1]], ![[94, 78, 390], [128, 176, 448], [39, 474, 16], [420, 123, 135], [476, 132, 327], [447, 125, 234], [12, 422, 427], [46, 96, 457], [285, 400, 89]], ![[0, 1], [188, 476, 313], [383, 19, 324], [76, 283, 401], [454, 329, 371], [452, 433, 158], [411, 456, 451], [365, 118, 122], [94, 78, 390]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [365, 165], []]
 b := ![[], [230, 311, 461], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI479N0 : CertifiedPrimeIdeal' SI479N0 479 where
  n := 3
  hpos := by decide
  P := [117, 214, 100, 1]
  hirr := P479P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![17111097564, 3399084875, 19299919016, 14319120659, 42828931956]
  a := ![309, 41, 314, 215, 678]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-50178581821, -40419476159, -24351824169, 14319120659, 42828931956]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI479N0 : Ideal.IsPrime I479N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI479N0 B_one_repr
lemma NI479N0 : Nat.card (O ⧸ I479N0) = 109902239 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI479N0

def I479N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 30, 12, 16, 54]] i)))

def SI479N1: IdealEqSpanCertificate' Table ![![79, 30, 12, 16, 54]] 
 ![![479, 0, 0, 0, 0], ![0, 479, 0, 0, 0], ![402, 10, 1, 0, 0], ![291, 302, 0, 1, 0], ![367, 104, 0, 0, 1]] where
  M :=![![![79, 30, 12, 16, 54], ![-144, -23, -44, -52, -172], ![384, 156, 137, 108, 384], ![-1440, -480, -792, -607, -2136], ![312, 90, 216, 162, 569]]]
  hmulB := by decide  
  f := ![![![-127, -18, -84, -76, -222]], ![![-144, 47, -460, -332, -908]], ![![-114, -14, -87, -76, -220]], ![![-195, 20, -388, -291, -806]], ![![-119, -4, -148, -118, -333]]]
  g := ![![![-61, -22, 12, 16, 54], ![200, 71, -44, -52, -172], ![-474, -154, 137, 108, 384], ![2667, 862, -792, -607, -2136], ![-715, -230, 216, 162, 569]]]
  hle1 := by decide   
  hle2 := by decide  


def P479P1 : CertificateIrreducibleZModOfList' 479 2 2 8 [76, 467, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 478], [0, 1]]
 g := ![![[378, 196], [294, 194], [250, 160], [359, 48], [182, 210], [89], [432, 313], [12, 1]], ![[335, 283], [227, 285], [254, 319], [456, 431], [307, 269], [89], [356, 166], [24, 478]]]
 h' := ![![[12, 478], [169, 14], [160, 302], [19, 309], [59, 124], [3, 249], [219, 277], [46, 68], [0, 1]], ![[0, 1], [337, 465], [431, 177], [374, 170], [110, 355], [117, 230], [190, 202], [383, 411], [12, 478]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [443, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI479N1 : CertifiedPrimeIdeal' SI479N1 479 where
  n := 2
  hpos := by decide
  P := [76, 467, 1]
  hirr := P479P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1094, -1888, -369, -395, -1028]
  a := ![-5, -4, -5, -4, -11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1335, 476, -369, -395, -1028]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI479N1 : Ideal.IsPrime I479N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI479N1 B_one_repr
lemma NI479N1 : Nat.card (O ⧸ I479N1) = 229441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI479N1
def MulI479N0 : IdealMulLeCertificate' Table 
  ![![-127, -18, -84, -76, -222]] ![![79, 30, 12, 16, 54]]
  ![![479, 0, 0, 0, 0]] where
 M := ![![![479, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC479 : ContainsPrimesAboveP 479 ![I479N0, I479N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI479N0
    exact isPrimeI479N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 479 (by decide) (𝕀 ⊙ MulI479N0)
instance hp487 : Fact (Nat.Prime 487) := {out := by norm_num}

def I487N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![487, 0, 0, 0, 0]] i)))

def SI487N0: IdealEqSpanCertificate' Table ![![487, 0, 0, 0, 0]] 
 ![![487, 0, 0, 0, 0], ![0, 487, 0, 0, 0], ![0, 0, 487, 0, 0], ![0, 0, 0, 487, 0], ![0, 0, 0, 0, 487]] where
  M :=![![![487, 0, 0, 0, 0], ![0, 487, 0, 0, 0], ![0, 0, 487, 0, 0], ![0, 0, 0, 487, 0], ![0, 0, 0, 0, 487]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P487P0 : CertificateIrreducibleZModOfList' 487 5 2 8 [483, 447, 19, 1, 309, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [237, 472, 298, 331, 165], [149, 316, 250, 372, 484], [229, 478, 322, 321, 453], [50, 194, 104, 437, 359], [0, 1]]
 g := ![![[181, 344, 73, 98, 256], [168, 312, 468, 389, 182], [131, 197, 289, 274, 464], [170, 385, 175, 336], [473, 486, 341, 169], [359, 80, 474, 320, 71], [28, 178, 1], []], ![[314, 299, 171, 168, 3, 87, 172, 246], [39, 96, 359, 243, 332, 257, 146, 74], [117, 337, 292, 49, 348, 51, 228, 175], [175, 382, 185, 51], [383, 331, 361, 295], [71, 68, 379, 3, 274, 87, 46, 366], [3, 290, 190, 240, 136, 439, 125, 429], [439, 245, 213, 475, 101, 109, 336, 37]], ![[84, 439, 332, 379, 224, 223, 194, 116], [128, 117, 101, 138, 430, 462, 338, 204], [93, 131, 190, 99, 310, 320, 90, 314], [343, 132, 398, 16], [226, 389, 58, 50], [19, 294, 460, 206, 134, 117, 40, 258], [384, 107, 141, 470, 92, 438, 467, 8], [423, 141, 452, 67, 206, 8, 368, 460]], ![[33, 217, 295, 373, 457, 453, 353, 450], [0, 10, 14, 122, 414, 251, 199, 289], [298, 194, 79, 197, 241, 252, 434, 171], [270, 286, 118, 8], [275, 91, 388, 264], [261, 242, 347, 441, 339, 293, 327, 460], [62, 349, 336, 134, 184, 2, 128, 460], [188, 331, 75, 304, 65, 6, 76, 143]], ![[27, 190, 135, 380, 116, 390, 385, 186], [181, 391, 178, 393, 247, 207, 199, 416], [484, 9, 310, 316, 296, 242, 143, 13], [350, 44, 88, 299], [172, 474, 26, 386], [217, 115, 376, 466, 465, 483, 295, 145], [399, 133, 83, 288, 145, 172, 405, 218], [202, 52, 326, 366, 87, 209, 38, 357]]]
 h' := ![![[237, 472, 298, 331, 165], [185, 84, 70, 173, 471], [37, 245, 171, 263, 453], [99, 199, 303, 211, 225], [82, 375, 420, 249, 290], [462, 439, 50, 186, 13], [112, 371, 261, 39, 404], [0, 0, 0, 1], [0, 1]], ![[149, 316, 250, 372, 484], [38, 78, 70, 431, 56], [441, 177, 391, 21, 405], [199, 270, 90, 215, 394], [331, 117, 231, 401, 349], [387, 275, 358, 343, 176], [247, 259, 439, 125, 392], [203, 446, 144, 181, 10], [237, 472, 298, 331, 165]], ![[229, 478, 322, 321, 453], [335, 3, 409, 15, 338], [130, 448, 332, 64, 76], [149, 101, 392, 318, 41], [403, 348, 80, 428, 483], [331, 370, 235, 151, 32], [85, 381, 106, 2, 346], [476, 308, 252, 444, 36], [149, 316, 250, 372, 484]], ![[50, 194, 104, 437, 359], [275, 334, 439, 162, 320], [50, 257, 88, 359, 268], [168, 231, 139, 341, 399], [190, 378, 428, 363, 182], [8, 470, 376, 124, 87], [26, 248, 66, 486, 267], [321, 367, 136, 36, 267], [229, 478, 322, 321, 453]], ![[0, 1], [422, 475, 473, 193, 276], [58, 334, 479, 267, 259], [216, 173, 50, 376, 402], [367, 243, 302, 20, 157], [436, 394, 442, 170, 179], [357, 202, 102, 322, 52], [162, 340, 442, 312, 174], [50, 194, 104, 437, 359]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [288, 72, 74, 229], [], [], []]
 b := ![[], [422, 179, 454, 403, 462], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI487N0 : CertifiedPrimeIdeal' SI487N0 487 where
  n := 5
  hpos := by decide
  P := [483, 447, 19, 1, 309, 1]
  hirr := P487P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1204469851194028554, 64211926114743930, 1774470538008938664, 1335860481000345239, 3797999837718235476]
  a := ![319, 126, 324, 221, 700]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2473244047626342, 131852004342390, 3643676669422872, 2743040002054097, 7798767633918348]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI487N0 : Ideal.IsPrime I487N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI487N0 B_one_repr
lemma NI487N0 : Nat.card (O ⧸ I487N0) = 27393328531207 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI487N0

def PBC487 : ContainsPrimesAboveP 487 ![I487N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI487N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![487, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 487 (by decide) 𝕀

instance hp491 : Fact (Nat.Prime 491) := {out := by norm_num}

def I491N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![33169, 9859, 5585, 8870, 28972]] i)))

def SI491N0: IdealEqSpanCertificate' Table ![![33169, 9859, 5585, 8870, 28972]] 
 ![![491, 0, 0, 0, 0], ![0, 491, 0, 0, 0], ![0, 0, 491, 0, 0], ![477, 253, 479, 1, 0], ![240, 424, 353, 0, 1]] where
  M :=![![![33169, 9859, 5585, 8870, 28972], ![-56688, -14699, -8987, -14467, -47140], ![89736, 20364, 13430, 21903, 71214], ![-132120, -25518, -18639, -30844, -100026], ![-5016, -3417, -1338, -1953, -6481]]]
  hmulB := by decide  
  f := ![![![131, 13, 185, 138, 394]], ![![480, -103, 1025, 781, 2104]], ![![5736, 288, 8518, 6411, 18198]], ![![6021, 232, 9119, 6868, 19430]], ![![4584, 127, 7064, 5324, 15019]]]
  g := ![![![-22711, -29569, -29471, 8870, 28972], ![36981, 48132, 47986, -14467, -47140], ![-55905, -72741, -72539, 21903, 71214], ![78588, 102218, 101965, -30844, -100026], ![5055, 6596, 6562, -1953, -6481]]]
  hle1 := by decide   
  hle2 := by decide  


def P491P0 : CertificateIrreducibleZModOfList' 491 3 2 8 [304, 106, 218, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [417, 335, 242], [347, 155, 249], [0, 1]]
 g := ![![[81, 336, 429], [140, 68, 3], [390, 100], [91, 71, 257], [3, 44], [253, 19, 31], [72, 421, 388], [1]], ![[404, 439, 124, 360], [480, 178, 211, 98], [146, 1], [167, 45, 303, 57], [437, 144], [354, 279, 435, 32], [327, 295, 420, 319], [133, 279, 54, 264]], ![[484, 456, 412, 318], [213, 430, 94, 215], [19, 81], [325, 190, 141, 152], [379, 131], [365, 164, 224, 407], [324, 104, 85, 227], [451, 138, 32, 227]]]
 h' := ![![[417, 335, 242], [157, 395, 263], [8, 314, 378], [323, 373, 10], [253, 94, 301], [175, 435, 59], [207, 8, 86], [187, 385, 273], [0, 1]], ![[347, 155, 249], [28, 365, 348], [147, 35, 44], [82, 309, 490], [281, 247, 172], [331, 201, 12], [418, 417, 45], [172, 29, 460], [417, 335, 242]], ![[0, 1], [235, 222, 371], [400, 142, 69], [61, 300, 482], [303, 150, 18], [25, 346, 420], [131, 66, 360], [163, 77, 249], [347, 155, 249]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [471, 357], []]
 b := ![[], [442, 49, 102], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI491N0 : CertifiedPrimeIdeal' SI491N0 491 where
  n := 3
  hpos := by decide
  P := [304, 106, 218, 1]
  hirr := P491P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-31904117027, -6309923379, -36042044113, -26745972629, -79965823350]
  a := ![-391, -131, -396, -270, -858]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![65005544666, 82822668538, 83509601808, -26745972629, -79965823350]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI491N0 : Ideal.IsPrime I491N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI491N0 B_one_repr
lemma NI491N0 : Nat.card (O ⧸ I491N0) = 118370771 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI491N0

def I491N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-29, -7, -5, -8, -26]] i)))

def SI491N1: IdealEqSpanCertificate' Table ![![-29, -7, -5, -8, -26]] 
 ![![491, 0, 0, 0, 0], ![62, 1, 0, 0, 0], ![84, 0, 1, 0, 0], ![193, 0, 0, 1, 0], ![381, 0, 0, 0, 1]] where
  M :=![![![-29, -7, -5, -8, -26], ![48, 13, 7, 11, 36], ![-72, -12, -12, -19, -62], ![120, 30, 27, 30, 98], ![0, -3, -2, 1, 3]]]
  hmulB := by decide  
  f := ![![![209, 71, 23, 40, 128]], ![![26, 9, 3, 5, 16]], ![![36, 12, 4, 7, 22]], ![![91, 31, 18, 22, 70]], ![![159, 54, 15, 29, 93]]]
  g := ![![![25, -7, -5, -8, -26], ![-35, 13, 7, 11, 36], ![59, -12, -12, -19, -62], ![-96, 30, 27, 30, 98], ![-2, -3, -2, 1, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI491N1 : Nat.card (O ⧸ I491N1) = 491 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI491N1)

lemma isPrimeI491N1 : Ideal.IsPrime I491N1 := prime_ideal_of_norm_prime hp491.out _ NI491N1

def I491N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![65, -12, 134, 102, 276]] i)))

def SI491N2: IdealEqSpanCertificate' Table ![![65, -12, 134, 102, 276]] 
 ![![491, 0, 0, 0, 0], ![441, 1, 0, 0, 0], ![446, 0, 1, 0, 0], ![205, 0, 0, 1, 0], ![380, 0, 0, 0, 1]] where
  M :=![![![65, -12, 134, 102, 276], ![720, 29, 1086, 818, 2316], ![3312, -492, 6475, 4930, 13444], ![32304, 636, 50186, 37871, 106740], ![-10848, -96, -17136, -12940, -36375]]]
  hmulB := by decide  
  f := ![![![173611, 8148, 17694, 32054, 102436]], ![![155625, 7361, 15876, 28752, 91888]], ![![157774, 7236, 16035, 29074, 92900]], ![![72989, 3792, 7536, 13597, 43480]], ![![134044, 6240, 13648, 24732, 79033]]]
  g := ![![![-367, -12, 134, 102, 276], ![-3145, 29, 1086, 818, 2316], ![-17896, -492, 6475, 4930, 13444], ![-144513, 636, 50186, 37871, 106740], ![49184, -96, -17136, -12940, -36375]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI491N2 : Nat.card (O ⧸ I491N2) = 491 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI491N2)

lemma isPrimeI491N2 : Ideal.IsPrime I491N2 := prime_ideal_of_norm_prime hp491.out _ NI491N2
def MulI491N0 : IdealMulLeCertificate' Table 
  ![![33169, 9859, 5585, 8870, 28972]] ![![-29, -7, -5, -8, -26]]
  ![![173611, 8148, 17694, 32054, 102436]] where
 M := ![![![173611, 8148, 17694, 32054, 102436]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI491N1 : IdealMulLeCertificate' Table 
  ![![173611, 8148, 17694, 32054, 102436]] ![![65, -12, 134, 102, 276]]
  ![![491, 0, 0, 0, 0]] where
 M := ![![![491, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC491 : ContainsPrimesAboveP 491 ![I491N0, I491N1, I491N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI491N0
    exact isPrimeI491N1
    exact isPrimeI491N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 491 (by decide) (𝕀 ⊙ MulI491N0 ⊙ MulI491N1)
instance hp499 : Fact (Nat.Prime 499) := {out := by norm_num}

def I499N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![635, 2465, -731, -1250, -3812]] i)))

def SI499N0: IdealEqSpanCertificate' Table ![![635, 2465, -731, -1250, -3812]] 
 ![![499, 0, 0, 0, 0], ![0, 499, 0, 0, 0], ![0, 0, 499, 0, 0], ![208, 302, 125, 1, 0], ![48, 406, 85, 0, 1]] where
  M :=![![![635, 2465, -731, -1250, -3812], ![1488, 4943, -1109, -2239, -6900], ![4392, 9852, 196, -2659, -8762], ![18840, 19434, 17271, 7438, 17978], ![-7848, -12351, -4112, 427, 2893]]]
  hmulB := by decide  
  f := ![![![-3007, -305, -351, -610, -1962]], ![![3168, 11, 291, 541, 1720]], ![![-2328, 672, -56, -179, -522]], ![![80, 44, 15, 27, 88]], ![![1896, 95, 194, 352, 1125]]]
  g := ![![![889, 3863, 961, -1250, -3812], ![1600, 6979, 1734, -2239, -6900], ![1960, 8758, 2159, -2659, -8762], ![-4792, -19090, -4891, 7438, 17978], ![-472, -2637, -608, 427, 2893]]]
  hle1 := by decide   
  hle2 := by decide  


def P499P0 : CertificateIrreducibleZModOfList' 499 3 2 8 [343, 161, 451, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [334, 337, 83], [213, 161, 416], [0, 1]]
 g := ![![[354, 189, 440], [169, 177, 386], [264, 457], [304, 339], [391, 439, 36], [452, 337, 336], [470, 326, 308], [1]], ![[403, 438, 149, 354], [138, 419, 131, 383], [328, 20], [445, 328], [145, 301, 24, 368], [404, 78, 61, 160], [175, 427, 337, 273], [291, 444, 14, 432]], ![[425, 374, 414, 170], [256, 312, 110, 489], [166, 46], [115, 45], [284, 456, 86, 289], [431, 263, 270, 167], [57, 329, 87, 270], [170, 143, 277, 67]]]
 h' := ![![[334, 337, 83], [416, 308, 77], [109, 367, 302], [470, 447, 170], [118, 0, 426], [153, 350, 6], [466, 21, 325], [156, 338, 48], [0, 1]], ![[213, 161, 416], [17, 498, 37], [447, 37, 241], [473, 416, 100], [311, 251, 223], [360, 56, 76], [373, 368, 176], [359, 92, 353], [334, 337, 83]], ![[0, 1], [50, 192, 385], [185, 95, 455], [82, 135, 229], [448, 248, 349], [195, 93, 417], [11, 110, 497], [36, 69, 98], [213, 161, 416]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48, 24], []]
 b := ![[], [3, 248, 144], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI499N0 : CertifiedPrimeIdeal' SI499N0 499 where
  n := 3
  hpos := by decide
  P := [343, 161, 451, 1]
  hirr := P499P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11163658399, 4468128792, 7242798496, 5126175904, 17871741662]
  a := ![216, 72, 220, 140, 474]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3833516091, -17634397012, -4313882226, 5126175904, 17871741662]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI499N0 : Ideal.IsPrime I499N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI499N0 B_one_repr
lemma NI499N0 : Nat.card (O ⧸ I499N0) = 124251499 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI499N0

def I499N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4517, -552, -551, -947, -3052]] i)))

def SI499N1: IdealEqSpanCertificate' Table ![![-4517, -552, -551, -947, -3052]] 
 ![![499, 0, 0, 0, 0], ![160, 1, 0, 0, 0], ![348, 0, 1, 0, 0], ![208, 0, 0, 1, 0], ![379, 0, 0, 0, 1]] where
  M :=![![![-4517, -552, -551, -947, -3052], ![5064, 223, 513, 931, 2974], ![-4344, 642, -216, -521, -1602], ![936, -2430, -545, -634, -2218], ![3048, 726, 460, 752, 2449]]]
  hmulB := by decide  
  f := ![![![-7703, -10152, -1013, 1601, 3516]], ![![-2408, -3257, -273, 559, 1282]], ![![-5796, -7314, -932, 977, 1934]], ![![-824, -3342, 1073, 1754, 5322]], ![![-6503, -7914, -1199, 891, 1529]]]
  g := ![![![3265, -552, -551, -947, -3052], ![-3066, 223, 513, 931, 2974], ![1370, 642, -216, -521, -1602], ![3110, -2430, -545, -634, -2218], ![-2721, 726, 460, 752, 2449]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI499N1 : Nat.card (O ⧸ I499N1) = 499 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI499N1)

lemma isPrimeI499N1 : Ideal.IsPrime I499N1 := prime_ideal_of_norm_prime hp499.out _ NI499N1

def I499N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, -31, 10, 17, 52]] i)))

def SI499N2: IdealEqSpanCertificate' Table ![![-5, -31, 10, 17, 52]] 
 ![![499, 0, 0, 0, 0], ![214, 1, 0, 0, 0], ![112, 0, 1, 0, 0], ![483, 0, 0, 1, 0], ![44, 0, 0, 0, 1]] where
  M :=![![![-5, -31, 10, 17, 52], ![-24, -65, 14, 28, 86], ![-48, -126, 1, 38, 124], ![-240, -252, -204, -83, -196], ![96, 159, 46, -11, -53]]]
  hmulB := by decide  
  f := ![![![-2351, -653, -516, -651, -2166]], ![![-998, -277, -218, -276, -918]], ![![-560, -158, -131, -158, -528]], ![![-2127, -573, -416, -570, -1882]], ![![-244, -73, -68, -73, -247]]]
  g := ![![![-10, -31, 10, 17, 52], ![-10, -65, 14, 28, 86], ![6, -126, 1, 38, 124], ![251, -252, -204, -83, -196], ![-63, 159, 46, -11, -53]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI499N2 : Nat.card (O ⧸ I499N2) = 499 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI499N2)

lemma isPrimeI499N2 : Ideal.IsPrime I499N2 := prime_ideal_of_norm_prime hp499.out _ NI499N2
def MulI499N0 : IdealMulLeCertificate' Table 
  ![![635, 2465, -731, -1250, -3812]] ![![-4517, -552, -551, -947, -3052]]
  ![![953, -139, 286, 297, 864]] where
 M := ![![![953, -139, 286, 297, 864]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI499N1 : IdealMulLeCertificate' Table 
  ![![953, -139, 286, 297, 864]] ![![-5, -31, 10, 17, 52]]
  ![![499, 0, 0, 0, 0]] where
 M := ![![![-3493, 5988, -12974, -10978, -30938]]]
 hmul := by decide  
 g := ![![![![-7, 12, -26, -22, -62]]]]
 hle2 := by decide  


def PBC499 : ContainsPrimesAboveP 499 ![I499N0, I499N1, I499N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI499N0
    exact isPrimeI499N1
    exact isPrimeI499N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 499 (by decide) (𝕀 ⊙ MulI499N0 ⊙ MulI499N1)
instance hp503 : Fact (Nat.Prime 503) := {out := by norm_num}

def I503N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19949, 83063, -27062, -43947, -133512]] i)))

def SI503N0: IdealEqSpanCertificate' Table ![![19949, 83063, -27062, -43947, -133512]] 
 ![![503, 0, 0, 0, 0], ![0, 503, 0, 0, 0], ![272, 366, 1, 0, 0], ![42, 114, 0, 1, 0], ![60, 66, 0, 0, 1]] where
  M :=![![![19949, 83063, -27062, -43947, -133512], ![40104, 166829, -54292, -88220, -268026], ![80784, 335058, -108633, -176876, -537460], ![163968, 672900, -215310, -353073, -1073408], ![-102240, -422391, 136292, 222485, 676173]]]
  hmulB := by decide  
  f := ![![![97963, 16913, 13260, 22173, 71786]], ![![-126408, -15959, -15536, -26666, -85966]], ![![-38720, -2452, -4105, -7360, -23564]], ![![-20718, -2172, -2426, -4223, -13584]], ![![-5004, -105, -474, -881, -2805]]]
  g := ![![![34269, 47335, -27062, -43947, -133512], ![68776, 94999, -54292, -88220, -268026], ![137784, 190320, -108633, -176876, -537460], ![274278, 378870, -215310, -353073, -1073408], ![-173138, -239157, 136292, 222485, 676173]]]
  hle1 := by decide   
  hle2 := by decide  


def P503P0 : CertificateIrreducibleZModOfList' 503 2 2 8 [251, 111, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [392, 502], [0, 1]]
 g := ![![[281, 493], [6, 184], [145, 28], [83], [190, 452], [360, 21], [281, 4], [392, 1]], ![[385, 10], [205, 319], [55, 475], [83], [318, 51], [41, 482], [340, 499], [281, 502]]]
 h' := ![![[392, 502], [3, 281], [324, 297], [264, 110], [95, 470], [180, 288], [392, 185], [196, 501], [0, 1]], ![[0, 1], [501, 222], [52, 206], [126, 393], [237, 33], [404, 215], [480, 318], [418, 2], [392, 502]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [222, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI503N0 : CertifiedPrimeIdeal' SI503N0 503 where
  n := 2
  hpos := by decide
  P := [251, 111, 1]
  hirr := P503P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8992761, 1594802, 10629645, 7904143, 23407998]
  a := ![619, 214, 629, 437, 1358]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-9182355, -12594146, 10629645, 7904143, 23407998]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI503N0 : Ideal.IsPrime I503N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI503N0 B_one_repr
lemma NI503N0 : Nat.card (O ⧸ I503N0) = 253009 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI503N0

def I503N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2309, 597, 365, 588, 1916]] i)))

def SI503N1: IdealEqSpanCertificate' Table ![![2309, 597, 365, 588, 1916]] 
 ![![503, 0, 0, 0, 0], ![0, 503, 0, 0, 0], ![317, 179, 1, 0, 0], ![96, 468, 0, 1, 0], ![365, 198, 0, 0, 1]] where
  M :=![![![2309, 597, 365, 588, 1916], ![-3648, -823, -547, -891, -2896], ![5352, 1032, 742, 1239, 4022], ![-7320, -1110, -1027, -1660, -5338], ![-600, -267, -98, -171, -573]]]
  hmulB := by decide  
  f := ![![![403, 327, 161, 60, 266]], ![![-2064, -551, -1411, -1095, -3820]], ![![-455, 22, -386, -342, -1156]], ![![-1992, -510, -1373, -1072, -3734]], ![![-479, 36, -413, -369, -1245]]]
  g := ![![![-1728, -1430, 365, 588, 1916], ![2609, 2162, -547, -891, -2896], ![-3612, -2998, 742, 1239, 4022], ![4823, 4009, -1027, -1660, -5338], ![509, 419, -98, -171, -573]]]
  hle1 := by decide   
  hle2 := by decide  


def P503P1 : CertificateIrreducibleZModOfList' 503 2 2 8 [67, 325, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [178, 502], [0, 1]]
 g := ![![[155, 488], [205, 256], [35, 126], [79], [343, 363], [215, 380], [352, 154], [178, 1]], ![[0, 15], [0, 247], [331, 377], [79], [70, 140], [453, 123], [99, 349], [356, 502]]]
 h' := ![![[178, 502], [349, 453], [170, 16], [242, 252], [157, 443], [182, 466], [57, 216], [146, 431], [0, 1]], ![[0, 1], [0, 50], [0, 487], [331, 251], [40, 60], [135, 37], [277, 287], [408, 72], [178, 502]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [433]]
 b := ![[], [97, 468]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI503N1 : CertifiedPrimeIdeal' SI503N1 503 where
  n := 2
  hpos := by decide
  P := [67, 325, 1]
  hirr := P503P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![74905, 26318, 57721, 40179, 135432]
  a := ![41, 10, 42, 27, 90]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-142172, -111183, 57721, 40179, 135432]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI503N1 : Ideal.IsPrime I503N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI503N1 B_one_repr
lemma NI503N1 : Nat.card (O ⧸ I503N1) = 253009 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI503N1

def I503N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-199, -38, -29, -47, -152]] i)))

def SI503N2: IdealEqSpanCertificate' Table ![![-199, -38, -29, -47, -152]] 
 ![![503, 0, 0, 0, 0], ![461, 1, 0, 0, 0], ![248, 0, 1, 0, 0], ![356, 0, 0, 1, 0], ![460, 0, 0, 0, 1]] where
  M :=![![![-199, -38, -29, -47, -152], ![264, 41, 27, 53, 174], ![-360, -30, -92, -107, -326], ![120, 6, -343, -226, -606], ![168, 24, 144, 122, 351]]]
  hmulB := by decide  
  f := ![![![-1361, -1478, -355, 57, -88]], ![![-1235, -1353, -316, 60, -54]], ![![-752, -770, -220, -1, -150]], ![![-500, -866, 35, 246, 670]], ![![-1372, -1396, -406, -8, -293]]]
  g := ![![![221, -38, -29, -47, -152], ![-247, 41, 27, 53, 174], ![446, -30, -92, -107, -326], ![878, 6, -343, -226, -606], ![-500, 24, 144, 122, 351]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI503N2 : Nat.card (O ⧸ I503N2) = 503 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI503N2)

lemma isPrimeI503N2 : Ideal.IsPrime I503N2 := prime_ideal_of_norm_prime hp503.out _ NI503N2
def MulI503N0 : IdealMulLeCertificate' Table 
  ![![19949, 83063, -27062, -43947, -133512]] ![![2309, 597, 365, 588, 1916]]
  ![![11833, 49594, -16335, -26367, -80066]] where
 M := ![![![11833, 49594, -16335, -26367, -80066]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI503N1 : IdealMulLeCertificate' Table 
  ![![11833, 49594, -16335, -26367, -80066]] ![![-199, -38, -29, -47, -152]]
  ![![503, 0, 0, 0, 0]] where
 M := ![![![3521, -6036, 13078, 11066, 31186]]]
 hmul := by decide  
 g := ![![![![7, -12, 26, 22, 62]]]]
 hle2 := by decide  


def PBC503 : ContainsPrimesAboveP 503 ![I503N0, I503N1, I503N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI503N0
    exact isPrimeI503N1
    exact isPrimeI503N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 503 (by decide) (𝕀 ⊙ MulI503N0 ⊙ MulI503N1)
instance hp509 : Fact (Nat.Prime 509) := {out := by norm_num}

def I509N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11509, -2176, -1378, -2506, -8208]] i)))

def SI509N0: IdealEqSpanCertificate' Table ![![-11509, -2176, -1378, -2506, -8208]] 
 ![![509, 0, 0, 0, 0], ![0, 509, 0, 0, 0], ![0, 0, 509, 0, 0], ![0, 0, 0, 509, 0], ![490, 34, 451, 405, 1]] where
  M :=![![![-11509, -2176, -1378, -2506, -8208], ![16560, 2219, 3670, 4650, 14452], ![-12048, -1908, 9273, 4938, 12100], ![65136, -2436, 80266, 62573, 175204], ![-10416, 2244, -26224, -19080, -52361]]]
  hmulB := by decide  
  f := ![![![3799, 15824, -5158, -8374, -25440]], ![![7632, 31783, -10358, -16818, -51092]], ![![15312, 63828, -20815, -33786, -102644]], ![![30864, 128244, -41738, -67811, -205988]], ![![42254, 175794, -57259, -92993, -282497]]]
  g := ![![![7879, 544, 7270, 6526, -8208], ![-13880, -961, -12798, -11490, 14452], ![-11672, -812, -10703, -9618, 12100], ![-168536, -11708, -155082, -139283, 175204], ![50386, 3502, 46343, 41625, -52361]]]
  hle1 := by decide   
  hle2 := by decide  


def P509P0 : CertificateIrreducibleZModOfList' 509 4 2 8 [210, 190, 508, 178, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [219, 258, 463, 191], [110, 257, 70, 237], [2, 502, 485, 81], [0, 1]]
 g := ![![[268, 492, 505, 180], [233, 392, 313], [196, 451, 439, 238], [424, 98, 417, 326], [357, 89, 58, 253], [330, 493, 508, 416], [440, 127, 331, 1], []], ![[398, 278, 233, 243, 82, 75], [497, 234, 445], [120, 74, 356, 38, 229, 317], [415, 10, 440, 10, 134, 321], [359, 494, 127, 301, 475, 147], [194, 327, 378, 181, 336, 203], [44, 298, 252, 104, 259, 147], [429, 492, 294, 113, 421, 170]], ![[218, 48, 190, 50, 141, 302], [98, 121, 293], [23, 335, 457, 26, 8, 382], [325, 147, 235, 265, 158, 152], [185, 267, 19, 286, 102, 394], [149, 199, 197, 457, 159, 393], [347, 504, 498, 133, 311, 473], [120, 245, 107, 115, 154, 176]], ![[275, 282, 116, 488, 505, 372], [301, 302, 16], [258, 7, 267, 118, 360, 406], [455, 153, 151, 177, 68, 23], [441, 372, 182, 306, 237, 81], [146, 503, 294, 495, 464, 103], [366, 324, 471, 44, 391, 228], [410, 235, 358, 261, 94, 45]]]
 h' := ![![[219, 258, 463, 191], [114, 79, 151, 69], [69, 88, 229, 367], [35, 382, 100, 298], [362, 187, 327, 210], [433, 358, 86, 274], [238, 183, 456, 209], [0, 0, 0, 1], [0, 1]], ![[110, 257, 70, 237], [463, 207, 462, 320], [139, 21, 11, 372], [312, 436, 292, 115], [73, 483, 143, 158], [296, 134, 480, 448], [152, 372, 136, 126], [247, 381, 140, 61], [219, 258, 463, 191]], ![[2, 502, 485, 81], [3, 383, 436, 166], [321, 89, 257, 275], [497, 454, 332, 103], [38, 56, 461, 102], [309, 444, 175, 297], [266, 337, 273, 245], [215, 212, 168, 466], [110, 257, 70, 237]], ![[0, 1], [54, 349, 478, 463], [120, 311, 12, 4], [47, 255, 294, 502], [35, 292, 87, 39], [140, 82, 277, 508], [410, 126, 153, 438], [438, 425, 201, 490], [2, 502, 485, 81]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [257, 481, 144], []]
 b := ![[], [], [23, 28, 478, 270], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI509N0 : CertifiedPrimeIdeal' SI509N0 509 where
  n := 4
  hpos := by decide
  P := [210, 190, 508, 178, 1]
  hirr := P509P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![575263731631407, 91961573747724, 701759958303652, 523148168434716, 1539550396679284]
  a := ![453, 153, 463, 312, 994]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1480951730139917, -102657665841548, -1362741589281048, -1223958276005256, 1539550396679284]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI509N0 : Ideal.IsPrime I509N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI509N0 B_one_repr
lemma NI509N0 : Nat.card (O ⧸ I509N0) = 67122964561 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI509N0

def I509N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3799, -15824, 5158, 8374, 25440]] i)))

def SI509N1: IdealEqSpanCertificate' Table ![![-3799, -15824, 5158, 8374, 25440]] 
 ![![509, 0, 0, 0, 0], ![194, 1, 0, 0, 0], ![30, 0, 1, 0, 0], ![288, 0, 0, 1, 0], ![176, 0, 0, 0, 1]] where
  M :=![![![-3799, -15824, 5158, 8374, 25440], ![-7632, -31783, 10358, 16818, 51092], ![-15312, -63828, 20815, 33786, 102644], ![-30864, -128244, 41738, 67811, 205988], ![19344, 80484, -26216, -42576, -129339]]]
  hmulB := by decide  
  f := ![![![11509, 2176, 1378, 2506, 8208]], ![![4354, 825, 518, 946, 3100]], ![![702, 132, 63, 138, 460]], ![![6384, 1236, 622, 1295, 4300]], ![![4000, 748, 528, 904, 2941]]]
  g := ![![![-7815, -15824, 5158, 8374, 25440], ![-15694, -31783, 10358, 16818, 51092], ![-31538, -63828, 20815, 33786, 102644], ![-63236, -128244, 41738, 67811, 205988], ![39720, 80484, -26216, -42576, -129339]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI509N1 : Nat.card (O ⧸ I509N1) = 509 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI509N1)

lemma isPrimeI509N1 : Ideal.IsPrime I509N1 := prime_ideal_of_norm_prime hp509.out _ NI509N1
def MulI509N0 : IdealMulLeCertificate' Table 
  ![![-11509, -2176, -1378, -2506, -8208]] ![![-3799, -15824, 5158, 8374, 25440]]
  ![![509, 0, 0, 0, 0]] where
 M := ![![![-509, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC509 : ContainsPrimesAboveP 509 ![I509N0, I509N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI509N0
    exact isPrimeI509N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 509 (by decide) (𝕀 ⊙ MulI509N0)
instance hp521 : Fact (Nat.Prime 521) := {out := by norm_num}

def I521N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1967, -351, -268, -447, -1448]] i)))

def SI521N0: IdealEqSpanCertificate' Table ![![-1967, -351, -268, -447, -1448]] 
 ![![521, 0, 0, 0, 0], ![0, 521, 0, 0, 0], ![375, 325, 1, 0, 0], ![39, 513, 0, 1, 0], ![279, 166, 0, 0, 1]] where
  M :=![![![-1967, -351, -268, -447, -1448], ![2568, 337, 322, 550, 1774], ![-2976, -198, -315, -562, -1800], ![2736, -264, 176, 385, 1204], ![1008, 291, 164, 259, 845]]]
  hmulB := by decide  
  f := ![![![-703, -303, -422, -293, -1050]], ![![4104, 1715, 2458, 1728, 6206]], ![![2007, 832, 1201, 847, 3044]], ![![4263, 1782, 2552, 1794, 6444]], ![![855, 352, 512, 362, 1301]]]
  g := ![![![998, 1068, -268, -447, -1448], ![-1218, -1307, 322, 550, 1774], ![1227, 1323, -315, -562, -1800], ![-795, -873, 176, 385, 1204], ![-588, -626, 164, 259, 845]]]
  hle1 := by decide   
  hle2 := by decide  


def P521P0 : CertificateIrreducibleZModOfList' 521 2 2 9 [424, 228, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [293, 520], [0, 1]]
 g := ![![[379, 333], [250], [519], [509, 284], [450], [517], [211], [405], [1]], ![[0, 188], [250], [519], [361, 237], [450], [517], [211], [405], [1]]]
 h' := ![![[293, 520], [268, 120], [102, 280], [399, 163], [371, 201], [153, 433], [398, 470], [241, 451], [97, 293], [0, 1]], ![[0, 1], [0, 401], [345, 241], [226, 358], [391, 320], [419, 88], [43, 51], [50, 70], [502, 228], [293, 520]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [498]]
 b := ![[], [252, 249]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI521N0 : CertifiedPrimeIdeal' SI521N0 521 where
  n := 2
  hpos := by decide
  P := [424, 228, 1]
  hirr := P521P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1564685, 392904, 1583183, 1163012, 3568502]
  a := ![247, 84, 250, 171, 542]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3134546, -3268979, 1583183, 1163012, 3568502]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI521N0 : Ideal.IsPrime I521N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI521N0 B_one_repr
lemma NI521N0 : Nat.card (O ⧸ I521N0) = 271441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI521N0

def I521N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![25861, 7715, 4349, 6906, 22560]] i)))

def SI521N1: IdealEqSpanCertificate' Table ![![25861, 7715, 4349, 6906, 22560]] 
 ![![521, 0, 0, 0, 0], ![0, 521, 0, 0, 0], ![512, 134, 1, 0, 0], ![164, 270, 0, 1, 0], ![222, 469, 0, 0, 1]] where
  M :=![![![25861, 7715, 4349, 6906, 22560], ![-44208, -11435, -7027, -11311, -36852], ![70056, 15996, 10458, 17055, 55462], ![-103128, -19782, -14615, -24184, -78410], ![-3912, -2769, -1006, -1461, -4865]]]
  hmulB := by decide  
  f := ![![![-22771, -9649, -13489, -9446, -34038]], ![![136800, 56867, 83667, 58819, 209432]], ![![11288, 4498, 7368, 5219, 18154]], ![![72908, 30236, 44761, 31482, 111938]], ![![110886, 46024, 67987, 47810, 170077]]]
  g := ![![![-16011, -24991, 4349, 6906, 22560], ![26084, 40821, -7027, -11311, -36852], ![-39144, -61424, 10458, 17055, 55462], ![55188, 86838, -14615, -24184, -78410], ![3514, 5390, -1006, -1461, -4865]]]
  hle1 := by decide   
  hle2 := by decide  


def P521P1 : CertificateIrreducibleZModOfList' 521 2 2 9 [111, 118, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [403, 520], [0, 1]]
 g := ![![[48, 151], [511], [53], [423, 396], [114], [457], [232], [378], [1]], ![[465, 370], [511], [53], [64, 125], [114], [457], [232], [378], [1]]]
 h' := ![![[403, 520], [313, 190], [170, 135], [458, 400], [129, 104], [291, 487], [251, 317], [60, 348], [410, 403], [0, 1]], ![[0, 1], [296, 331], [391, 386], [148, 121], [361, 417], [135, 34], [357, 204], [155, 173], [267, 118], [403, 520]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [79]]
 b := ![[], [507, 300]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI521N1 : CertifiedPrimeIdeal' SI521N1 521 where
  n := 2
  hpos := by decide
  P := [111, 118, 1]
  hirr := P521P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1262483, 219996, 1505286, 1119273, 3309165]
  a := ![232, 80, 235, 164, 509]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3239231, -3945663, 1505286, 1119273, 3309165]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI521N1 : Ideal.IsPrime I521N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI521N1 B_one_repr
lemma NI521N1 : Nat.card (O ⧸ I521N1) = 271441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI521N1

def I521N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-84749, 45198, 4417, 613, 5666]] i)))

def SI521N2: IdealEqSpanCertificate' Table ![![-84749, 45198, 4417, 613, 5666]] 
 ![![521, 0, 0, 0, 0], ![62, 1, 0, 0, 0], ![324, 0, 1, 0, 0], ![231, 0, 0, 1, 0], ![192, 0, 0, 0, 1]] where
  M :=![![![-84749, 45198, 4417, 613, 5666], ![-91848, -121031, -40371, -55589, -186446], ![472296, 252030, 109230, 163315, 539238], ![-1183032, -461286, -228449, -352828, -1158130], ![223872, 32208, 28600, 48542, 156763]]]
  hmulB := by decide  
  f := ![![![-179581, 61194, -345031, -276269, -774894]], ![![-23854, 7597, -45443, -36255, -101630]], ![![-128940, 39234, -244310, -194455, -544882]], ![![-198555, 33216, -356372, -276819, -772536]], ![![-25200, 20220, -56898, -48440, -137185]]]
  g := ![![![-10648, 45198, 4417, 613, 5666], ![132689, -121031, -40371, -55589, -186446], ![-368145, 252030, 109230, 163315, 539238], ![777924, -461286, -228449, -352828, -1158130], ![-100482, 32208, 28600, 48542, 156763]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI521N2 : Nat.card (O ⧸ I521N2) = 521 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI521N2)

lemma isPrimeI521N2 : Ideal.IsPrime I521N2 := prime_ideal_of_norm_prime hp521.out _ NI521N2
def MulI521N0 : IdealMulLeCertificate' Table 
  ![![-1967, -351, -268, -447, -1448]] ![![25861, 7715, 4349, 6906, 22560]]
  ![![-2363795, -2596582, -901157, -1258905, -4210494]] where
 M := ![![![-2363795, -2596582, -901157, -1258905, -4210494]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI521N1 : IdealMulLeCertificate' Table 
  ![![-2363795, -2596582, -901157, -1258905, -4210494]] ![![-84749, 45198, 4417, 613, 5666]]
  ![![521, 0, 0, 0, 0]] where
 M := ![![![559920466711, 425413172000, 163127810242, 235511068600, 782716943464]]]
 hmul := by decide  
 g := ![![![![1074703391, 816532000, 313105202, 452036600, 1502335784]]]]
 hle2 := by decide  


def PBC521 : ContainsPrimesAboveP 521 ![I521N0, I521N1, I521N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI521N0
    exact isPrimeI521N1
    exact isPrimeI521N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 521 (by decide) (𝕀 ⊙ MulI521N0 ⊙ MulI521N1)
instance hp523 : Fact (Nat.Prime 523) := {out := by norm_num}

def I523N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![115661, 33404, 19192, 30600, 99910]] i)))

def SI523N0: IdealEqSpanCertificate' Table ![![115661, 33404, 19192, 30600, 99910]] 
 ![![523, 0, 0, 0, 0], ![0, 523, 0, 0, 0], ![0, 0, 523, 0, 0], ![0, 0, 0, 523, 0], ![343, 519, 206, 231, 1]] where
  M :=![![![115661, 33404, 19192, 30600, 99910], ![-194640, -49129, -30726, -49368, -160700], ![302304, 66828, 43107, 72074, 234856], ![-447216, -81624, -73458, -110889, -355108], ![-17880, -12252, -806, -4250, -15765]]]
  hmulB := by decide  
  f := ![![![-217, -1220, 460, 700, 2146]], ![![-1104, -2731, 522, 1124, 3300]], ![![1728, -3828, 3421, 3922, 12592]], ![![-19824, -17472, -7138, -1951, -9924]], ![![-9301, -12719, -984, 2255, 5253]]]
  g := ![![![-65303, -99082, -39316, -44070, 99910], ![105020, 159377, 63238, 70884, -160700], ![-153448, -232932, -92423, -103594, 234856], ![232036, 352236, 139730, 156633, -355108], ![10305, 15621, 6208, 6955, -15765]]]
  hle1 := by decide   
  hle2 := by decide  


def P523P0 : CertificateIrreducibleZModOfList' 523 4 2 9 [138, 441, 522, 194, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [116, 81, 285, 346], [153, 167, 187, 32], [60, 274, 51, 145], [0, 1]]
 g := ![![[507, 244, 269, 40], [174, 374, 408, 137], [351, 146, 426], [143, 287, 90, 54], [508, 466, 263], [152, 323, 341], [428, 354, 503], [1], []], ![[424, 74, 302, 11, 290, 386], [22, 407, 302, 444, 407, 328], [243, 514, 294], [229, 2, 384, 311, 66, 46], [21, 102, 124], [118, 461, 9], [264, 375, 119], [263, 417, 157], [82, 6, 472]], ![[496, 154, 411, 390, 255, 317], [348, 460, 387, 289, 92, 407], [198, 93, 11], [407, 74, 29, 512, 244, 358], [64, 314, 92], [91, 189, 1], [196, 180, 13], [314, 277, 285], [379, 23, 501]], ![[168, 250, 453, 21, 485, 452], [100, 261, 259, 325, 169, 332], [179, 367, 246], [263, 186, 160, 168, 299, 108], [339, 232, 324], [315, 137, 287], [201, 80, 323], [139, 241, 203], [488, 173, 105]]]
 h' := ![![[116, 81, 285, 346], [46, 411, 197, 404], [450, 358, 481, 264], [140, 217, 487, 85], [208, 42, 213, 69], [185, 361, 374, 273], [251, 222, 485, 247], [385, 82, 1, 329], [0, 0, 1], [0, 1]], ![[153, 167, 187, 32], [339, 145, 455, 51], [272, 348, 187, 503], [452, 456, 393, 362], [378, 267, 145, 414], [344, 86, 66, 80], [203, 468, 455, 3], [5, 442, 336, 347], [48, 107, 274, 189], [116, 81, 285, 346]], ![[60, 274, 51, 145], [225, 64, 422, 334], [513, 342, 211, 218], [173, 363, 445, 150], [8, 307, 135, 122], [177, 432, 132, 152], [461, 285, 70, 522], [248, 517, 370, 333], [395, 33, 456, 81], [153, 167, 187, 32]], ![[0, 1], [299, 426, 495, 257], [351, 521, 167, 61], [177, 10, 244, 449], [57, 430, 30, 441], [111, 167, 474, 18], [457, 71, 36, 274], [352, 5, 339, 37], [62, 383, 315, 253], [60, 274, 51, 145]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [238, 295, 431], []]
 b := ![[], [], [469, 132, 497, 199], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI523N0 : CertifiedPrimeIdeal' SI523N0 523 where
  n := 4
  hpos := by decide
  P := [138, 441, 522, 194, 1]
  hirr := P523P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![257913002484864, 52546413315529, 287718121001135, 213339423967510, 639577197735442]
  a := ![-359, -113, -376, -246, -788]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-418961884934554, -634585122775103, -251367465798279, -282082205072504, 639577197735442]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI523N0 : Ideal.IsPrime I523N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI523N0 B_one_repr
lemma NI523N0 : Nat.card (O ⧸ I523N0) = 74818113841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI523N0

def I523N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![217, 1220, -460, -700, -2146]] i)))

def SI523N1: IdealEqSpanCertificate' Table ![![217, 1220, -460, -700, -2146]] 
 ![![523, 0, 0, 0, 0], ![162, 1, 0, 0, 0], ![429, 0, 1, 0, 0], ![61, 0, 0, 1, 0], ![189, 0, 0, 0, 1]] where
  M :=![![![217, 1220, -460, -700, -2146], ![1104, 2731, -522, -1124, -3300], ![-1728, 3828, -3421, -3922, -12592], ![19824, 17472, 7138, 1951, 9924], ![-6360, -8412, -822, 1342, 2967]]]
  hmulB := by decide  
  f := ![![![-115661, -33404, -19192, -30600, -99910]], ![![-35454, -10253, -5886, -9384, -30640]], ![![-95451, -27528, -15825, -25238, -82402]], ![![-12635, -3740, -2098, -3357, -10974]], ![![-41763, -12048, -6934, -11050, -36075]]]
  g := ![![![857, 1220, -460, -700, -2146], ![908, 2731, -522, -1124, -3300], ![6625, 3828, -3421, -3922, -12592], ![-15043, 17472, 7138, 1951, 9924], ![2039, -8412, -822, 1342, 2967]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI523N1 : Nat.card (O ⧸ I523N1) = 523 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI523N1)

lemma isPrimeI523N1 : Ideal.IsPrime I523N1 := prime_ideal_of_norm_prime hp523.out _ NI523N1
def MulI523N0 : IdealMulLeCertificate' Table 
  ![![115661, 33404, 19192, 30600, 99910]] ![![217, 1220, -460, -700, -2146]]
  ![![523, 0, 0, 0, 0]] where
 M := ![![![-523, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC523 : ContainsPrimesAboveP 523 ![I523N0, I523N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI523N0
    exact isPrimeI523N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 523 (by decide) (𝕀 ⊙ MulI523N0)


lemma PB2088I10_primes (p : ℕ) :
  p ∈ Set.range ![467, 479, 487, 491, 499, 503, 509, 521, 523] ↔ Nat.Prime p ∧ 463 < p ∧ p ≤ 523 := by
  rw [← List.mem_ofFn']
  convert primes_range 463 523 (by omega)

def PB2088I10 : PrimesBelowBoundCertificateInterval O 463 523 2088 where
  m := 9
  g := ![4, 2, 1, 3, 3, 3, 2, 3, 2]
  P := ![467, 479, 487, 491, 499, 503, 509, 521, 523]
  hP := PB2088I10_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I467N0, I467N1, I467N2, I467N3]
    · exact ![I479N0, I479N1]
    · exact ![I487N0]
    · exact ![I491N0, I491N1, I491N2]
    · exact ![I499N0, I499N1, I499N2]
    · exact ![I503N0, I503N1, I503N2]
    · exact ![I509N0, I509N1]
    · exact ![I521N0, I521N1, I521N2]
    · exact ![I523N0, I523N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC467
    · exact PBC479
    · exact PBC487
    · exact PBC491
    · exact PBC499
    · exact PBC503
    · exact PBC509
    · exact PBC521
    · exact PBC523
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![218089, 467, 467, 467]
    · exact ![109902239, 229441]
    · exact ![27393328531207]
    · exact ![118370771, 491, 491]
    · exact ![124251499, 499, 499]
    · exact ![253009, 253009, 503]
    · exact ![67122964561, 509]
    · exact ![271441, 271441, 521]
    · exact ![74818113841, 523]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI467N0
      exact NI467N1
      exact NI467N2
      exact NI467N3
    · dsimp ; intro j
      fin_cases j
      exact NI479N0
      exact NI479N1
    · dsimp ; intro j
      fin_cases j
      exact NI487N0
    · dsimp ; intro j
      fin_cases j
      exact NI491N0
      exact NI491N1
      exact NI491N2
    · dsimp ; intro j
      fin_cases j
      exact NI499N0
      exact NI499N1
      exact NI499N2
    · dsimp ; intro j
      fin_cases j
      exact NI503N0
      exact NI503N1
      exact NI503N2
    · dsimp ; intro j
      fin_cases j
      exact NI509N0
      exact NI509N1
    · dsimp ; intro j
      fin_cases j
      exact NI521N0
      exact NI521N1
      exact NI521N2
    · dsimp ; intro j
      fin_cases j
      exact NI523N0
      exact NI523N1
  β := ![I467N1, I467N2, I467N3, I491N1, I491N2, I499N1, I499N2, I503N2, I509N1, I521N2, I523N1]
  Il := ![[I467N1, I467N2, I467N3], [], [], [I491N1, I491N2], [I499N1, I499N2], [I503N2], [I509N1], [I521N2], [I523N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
