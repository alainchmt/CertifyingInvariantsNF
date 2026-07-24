
import IdealArithmetic.Examples.NF5_3_1215000000_5.RI5_3_1215000000_5
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp467 : Fact (Nat.Prime 467) := {out := by norm_num}

def I467N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![136, 38, -36, -13, -53]] i)))

def SI467N0: IdealEqSpanCertificate' Table ![![136, 38, -36, -13, -53]] 
 ![![467, 0, 0, 0, 0], ![0, 467, 0, 0, 0], ![143, 237, 1, 0, 0], ![100, 241, 0, 1, 0], ![52, 255, 0, 0, 1]] where
  M :=![![![136, 38, -36, -13, -53], ![396, 143, -118, -44, -176], ![1320, 410, -385, -148, -616], ![2094, 666, -624, -191, -876], ![-693, -212, 212, 73, 332]]]
  hmulB := by decide  
  f := ![![![-4504, -1618, 1224, 449, 1879]], ![![-13968, -4959, 3770, 1384, 5788]], ![![-8560, -3045, 2313, 849, 3551]], ![![-8300, -2951, 2242, 823, 3442]], ![![-8081, -2871, 2182, 801, 3350]]]
  g := ![![![20, 54, -36, -13, -53], ![66, 179, -118, -44, -176], ![221, 609, -385, -148, -616], ![334, 895, -624, -191, -876], ![-119, -327, 212, 73, 332]]]
  hle1 := by decide   
  hle2 := by decide  


def P467P0 : CertificateIrreducibleZModOfList' 467 2 2 8 [158, 455, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 466], [0, 1]]
 g := ![![[195, 334], [288, 443], [425], [413], [400, 157], [109], [334, 196], [12, 1]], ![[0, 133], [0, 24], [425], [413], [416, 310], [109], [351, 271], [24, 466]]]
 h' := ![![[12, 466], [262, 56], [41, 269], [334, 357], [312, 170], [58, 422], [466, 443], [439, 453], [0, 1]], ![[0, 1], [0, 411], [0, 198], [415, 110], [17, 297], [452, 45], [178, 24], [271, 14], [12, 466]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [356]]
 b := ![[], [333, 178]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI467N0 : CertifiedPrimeIdeal' SI467N0 467 where
  n := 2
  hpos := by decide
  P := [158, 455, 1]
  hirr := P467P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-609523, -84864, 231546, -66907, 101403]
  a := ![33, -74, -69, -37, -209]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-69171, -138532, 231546, -66907, 101403]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI467N0 : Ideal.IsPrime I467N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI467N0 B_one_repr
lemma NI467N0 : Nat.card (O ⧸ I467N0) = 218089 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI467N0

def I467N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-44, 73, 63, -11, 127]] i)))

def SI467N1: IdealEqSpanCertificate' Table ![![-44, 73, 63, -11, 127]] 
 ![![467, 0, 0, 0, 0], ![0, 467, 0, 0, 0], ![366, 187, 1, 0, 0], ![337, 445, 0, 1, 0], ![215, 406, 0, 0, 1]] where
  M :=![![![-44, 73, 63, -11, 127], ![-696, -632, -59, -194, -1180], ![8244, 1443, -2960, 1078, -292], ![-2010, 10549, 7219, 663, 21948], ![-5625, -3840, 312, -1051, -5752]]]
  hmulB := by decide  
  f := ![![![376220, 122731, -108373, -39681, -162781]], ![![1214772, 403118, -353441, -129270, -531192]], ![![789768, 260403, -228921, -83762, -343974]], ![![1441516, 476816, -418617, -153140, -629077]], ![![1224959, 405531, -355907, -130192, -534855]]]
  g := ![![![-100, -125, 63, -11, 127], ![728, 1233, -59, -194, -1180], ![1694, 415, -2960, 1078, -292], ![-16245, -22581, 7219, 663, 21948], ![3150, 5869, 312, -1051, -5752]]]
  hle1 := by decide   
  hle2 := by decide  


def P467P1 : CertificateIrreducibleZModOfList' 467 2 2 8 [346, 198, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [269, 466], [0, 1]]
 g := ![![[338, 113], [279, 81], [108], [156], [55, 299], [327], [80, 69], [269, 1]], ![[380, 354], [119, 386], [108], [156], [162, 168], [327], [428, 398], [71, 466]]]
 h' := ![![[269, 466], [135, 264], [206, 9], [342, 62], [117, 256], [123, 220], [340, 248], [326, 97], [0, 1]], ![[0, 1], [167, 203], [292, 458], [208, 405], [332, 211], [461, 247], [271, 219], [267, 370], [269, 466]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [134]]
 b := ![[], [95, 67]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI467N1 : CertifiedPrimeIdeal' SI467N1 467 where
  n := 2
  hpos := by decide
  P := [346, 198, 1]
  hirr := P467P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2365076, -2326694, -264912, -483098, -3811307]
  a := ![-45, 35, 95, -17, 286]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2305841, 3874906, -264912, -483098, -3811307]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI467N1 : Ideal.IsPrime I467N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI467N1 B_one_repr
lemma NI467N1 : Nat.card (O ⧸ I467N1) = 218089 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI467N1

def I467N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10543, 3583, -3099, -1132, -4664]] i)))

def SI467N2: IdealEqSpanCertificate' Table ![![10543, 3583, -3099, -1132, -4664]] 
 ![![467, 0, 0, 0, 0], ![43, 1, 0, 0, 0], ![19, 0, 1, 0, 0], ![37, 0, 0, 1, 0], ![423, 0, 0, 0, 1]] where
  M :=![![![10543, 3583, -3099, -1132, -4664], ![34776, 11384, -10001, -3662, -15032], ![112164, 37297, -32560, -11910, -48964], ![165234, 54623, -47811, -17495, -71882], ![-57630, -19060, 16676, 6102, 25073]]]
  hmulB := by decide  
  f := ![![![4961, -347, -2503, 592, -2476]], ![![481, 11, -216, 62, -148]], ![![-323, -198, 31, -62, -296]], ![![1225, -414, -814, 113, -1286]], ![![4683, -67, -2207, 586, -1799]]]
  g := ![![![4133, 3583, -3099, -1132, -4664], ![13339, 11384, -10001, -3662, -15032], ![43425, 37297, -32560, -11910, -48964], ![63765, 54623, -47811, -17495, -71882], ![-22241, -19060, 16676, 6102, 25073]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI467N2 : Nat.card (O ⧸ I467N2) = 467 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI467N2)

lemma isPrimeI467N2 : Ideal.IsPrime I467N2 := prime_ideal_of_norm_prime hp467.out _ NI467N2
def MulI467N0 : IdealMulLeCertificate' Table 
  ![![136, 38, -36, -13, -53]] ![![-44, 73, 63, -11, 127]]
  ![![-4961, 347, 2503, -592, 2476]] where
 M := ![![![-4961, 347, 2503, -592, 2476]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI467N1 : IdealMulLeCertificate' Table 
  ![![-4961, 347, 2503, -592, 2476]] ![![10543, 3583, -3099, -1132, -4664]]
  ![![467, 0, 0, 0, 0]] where
 M := ![![![-467, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC467 : ContainsPrimesAboveP 467 ![I467N0, I467N1, I467N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI467N0
    exact isPrimeI467N1
    exact isPrimeI467N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 467 (by decide) (𝕀 ⊙ MulI467N0 ⊙ MulI467N1)
instance hp479 : Fact (Nat.Prime 479) := {out := by norm_num}

def I479N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![392, 134, -118, -43, -177]] i)))

def SI479N0: IdealEqSpanCertificate' Table ![![392, 134, -118, -43, -177]] 
 ![![479, 0, 0, 0, 0], ![0, 479, 0, 0, 0], ![108, 256, 1, 0, 0], ![67, 98, 0, 1, 0], ![80, 254, 0, 0, 1]] where
  M :=![![![392, 134, -118, -43, -177], ![1320, 423, -382, -140, -572], ![4272, 1406, -1257, -460, -1888], ![6384, 2082, -1866, -679, -2790], ![-2199, -716, 644, 235, 966]]]
  hmulB := by decide  
  f := ![![![-128, -34, 26, 11, 39]], ![![-300, -115, 98, 40, 184]], ![![-192, -70, 59, 24, 108]], ![![-82, -30, 24, 10, 43]], ![![-179, -66, 56, 23, 104]]]
  g := ![![![63, 166, -118, -43, -177], ![204, 537, -382, -140, -572], ![672, 1770, -1257, -460, -1888], ![995, 2620, -1866, -679, -2790], ![-344, -906, 644, 235, 966]]]
  hle1 := by decide   
  hle2 := by decide  


def P479P0 : CertificateIrreducibleZModOfList' 479 2 2 8 [83, 318, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [161, 478], [0, 1]]
 g := ![![[50, 55], [388, 167], [368, 69], [130, 60], [3, 252], [11], [377, 305], [161, 1]], ![[283, 424], [451, 312], [460, 410], [210, 419], [339, 227], [11], [145, 174], [322, 478]]]
 h' := ![![[161, 478], [368, 318], [112, 149], [227, 353], [230, 73], [431, 228], [323, 421], [49, 451], [0, 1]], ![[0, 1], [313, 161], [151, 330], [59, 126], [8, 406], [256, 251], [86, 58], [331, 28], [161, 478]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [147]]
 b := ![[], [430, 313]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI479N0 : CertifiedPrimeIdeal' SI479N0 479 where
  n := 2
  hpos := by decide
  P := [83, 318, 1]
  hirr := P479P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-27, 136, 816, 74, 6063]
  a := ![4, -12, -8, -8, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1207, -3666, 816, 74, 6063]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI479N0 : Ideal.IsPrime I479N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI479N0 B_one_repr
lemma NI479N0 : Nat.card (O ⧸ I479N0) = 229441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI479N0

def I479N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-35360, -12582, 9580, 3515, 14695]] i)))

def SI479N1: IdealEqSpanCertificate' Table ![![-35360, -12582, 9580, 3515, 14695]] 
 ![![479, 0, 0, 0, 0], ![153, 1, 0, 0, 0], ![62, 0, 1, 0, 0], ![210, 0, 0, 1, 0], ![398, 0, 0, 0, 1]] where
  M :=![![![-35360, -12582, 9580, 3515, 14695], ![-109260, -38865, 29598, 10860, 45400], ![-337560, -120082, 91455, 33556, 140280], ![-466878, -166066, 126496, 46413, 194024], ![174147, 61948, -47180, -17311, -72368]]]
  hmulB := by decide  
  f := ![![![-2008, -886, 440, -347, -1041]], ![![-624, -287, 130, -109, -347]], ![![-184, -26, 75, -26, 22]], ![![-1416, -530, 356, -235, -560]], ![![-1585, -768, 308, -281, -960]]]
  g := ![![![-11046, -12582, 9580, 3515, 14695], ![-34129, -38865, 29598, 10860, 45400], ![-105456, -120082, 91455, 33556, 140280], ![-145866, -166066, 126496, 46413, 194024], ![54403, 61948, -47180, -17311, -72368]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI479N1 : Nat.card (O ⧸ I479N1) = 479 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI479N1)

lemma isPrimeI479N1 : Ideal.IsPrime I479N1 := prime_ideal_of_norm_prime hp479.out _ NI479N1

def I479N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-176, -35, 63, 1, 67]] i)))

def SI479N2: IdealEqSpanCertificate' Table ![![-176, -35, 63, 1, 67]] 
 ![![479, 0, 0, 0, 0], ![270, 1, 0, 0, 0], ![387, 0, 1, 0, 0], ![310, 0, 0, 1, 0], ![206, 0, 0, 0, 1]] where
  M :=![![![-176, -35, 63, 1, 67], ![-408, -368, -23, -2, -364], ![2196, 999, -392, 670, 2108], ![-8130, 1225, 4531, -489, 6588], ![-261, -1344, -696, -319, -3100]]]
  hmulB := by decide  
  f := ![![![10468592, -4718741, 1169999, 258015, 2124251]], ![![5871036, -2646272, 656111, 144684, 1191246]], ![![8499276, -3830878, 949813, 209449, 1724499]], ![![6762292, -3047777, 755611, 166615, 1371920]], ![![4505279, -2030890, 503582, 111059, 914292]]]
  g := ![![![-61, -35, 63, 1, 67], ![383, -368, -23, -2, -364], ![-1582, 999, -392, 670, 2108], ![-6885, 1225, 4531, -489, 6588], ![2859, -1344, -696, -319, -3100]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI479N2 : Nat.card (O ⧸ I479N2) = 479 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI479N2)

lemma isPrimeI479N2 : Ideal.IsPrime I479N2 := prime_ideal_of_norm_prime hp479.out _ NI479N2

def I479N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![16, 4, -6, -7, -23]] i)))

def SI479N3: IdealEqSpanCertificate' Table ![![16, 4, -6, -7, -23]] 
 ![![479, 0, 0, 0, 0], ![279, 1, 0, 0, 0], ![236, 0, 1, 0, 0], ![229, 0, 0, 1, 0], ![104, 0, 0, 0, 1]] where
  M :=![![![16, 4, -6, -7, -23], ![180, 11, -80, -8, -128], ![816, 508, -85, 48, 464], ![-1626, -256, 582, -401, -416], ![69, -244, -172, 39, -376]]]
  hmulB := by decide  
  f := ![![![19501496, -8812604, 2190086, 484063, 3974225]], ![![11303064, -5107785, 1269374, 280563, 2303461]], ![![9684848, -4376524, 1087643, 240396, 1973684]], ![![9298648, -4202004, 1044272, 230810, 1894981]], ![![4240265, -1916148, 476196, 105251, 864126]]]
  g := ![![![9, 4, -6, -7, -23], ![65, 11, -80, -8, -128], ![-376, 508, -85, 48, 464], ![141, -256, 582, -401, -416], ![290, -244, -172, 39, -376]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI479N3 : Nat.card (O ⧸ I479N3) = 479 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI479N3)

lemma isPrimeI479N3 : Ideal.IsPrime I479N3 := prime_ideal_of_norm_prime hp479.out _ NI479N3
def MulI479N0 : IdealMulLeCertificate' Table 
  ![![392, 134, -118, -43, -177]] ![![-35360, -12582, 9580, 3515, 14695]]
  ![![581855, 205664, -158666, -58200, -242896]] where
 M := ![![![581855, 205664, -158666, -58200, -242896]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI479N1 : IdealMulLeCertificate' Table 
  ![![581855, 205664, -158666, -58200, -242896]] ![![-176, -35, 63, 1, 67]]
  ![![1813928, 600613, -524919, -192069, -789339]] where
 M := ![![![1813928, 600613, -524919, -192069, -789339]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI479N2 : IdealMulLeCertificate' Table 
  ![![1813928, 600613, -524919, -192069, -789339]] ![![16, 4, -6, -7, -23]]
  ![![479, 0, 0, 0, 0]] where
 M := ![![![-33360913, -11028017, 9667657, 3536936, 14530944]]]
 hmul := by decide  
 g := ![![![![-69647, -23023, 20183, 7384, 30336]]]]
 hle2 := by decide  


def PBC479 : ContainsPrimesAboveP 479 ![I479N0, I479N1, I479N2, I479N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI479N0
    exact isPrimeI479N1
    exact isPrimeI479N2
    exact isPrimeI479N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 479 (by decide) (𝕀 ⊙ MulI479N0 ⊙ MulI479N1 ⊙ MulI479N2)
instance hp487 : Fact (Nat.Prime 487) := {out := by norm_num}

def I487N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-43414, -14342, 12622, 4617, 18961]] i)))

def SI487N0: IdealEqSpanCertificate' Table ![![-43414, -14342, 12622, 4617, 18961]] 
 ![![487, 0, 0, 0, 0], ![0, 487, 0, 0, 0], ![0, 0, 487, 0, 0], ![0, 0, 0, 487, 0], ![474, 296, 123, 84, 1]] where
  M :=![![![-43414, -14342, 12622, 4617, 18961], ![-141468, -46615, 41062, 15024, 61680], ![-460224, -151814, 133673, 48908, 200832], ![-678486, -223730, 197010, 72053, 295916], ![235905, 77780, -68508, -25061, -102922]]]
  hmulB := by decide  
  f := ![![![14, 2, -2, -1, -3]], ![![24, 11, -10, -4, -20]], ![![144, 42, -37, -4, -32]], ![![96, 86, 2, -15, 30]], ![![81, 34, -17, -7, -18]]]
  g := ![![![-18544, -11554, -4763, -3261, 18961], ![-60324, -37585, -15494, -10608, 61680], ![-196416, -122378, -50449, -34540, 200832], ![-289410, -180318, -74334, -50893, 295916], ![100659, 62716, 25854, 17701, -102922]]]
  hle1 := by decide   
  hle2 := by decide  


def P487P0 : CertificateIrreducibleZModOfList' 487 4 2 8 [298, 307, 246, 164, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [124, 473, 271, 475], [160, 405, 474, 14], [39, 95, 229, 485], [0, 1]]
 g := ![![[29, 358, 168, 85], [184, 257, 354, 161], [33, 302, 355, 215], [176, 111, 31], [36, 340, 288], [2, 445, 63, 142], [328, 352, 323, 1], []], ![[181, 0, 22, 474, 154, 282], [392, 61, 84, 443, 257, 161], [376, 296, 13, 8, 107, 259], [294, 404, 336], [94, 372, 240], [74, 159, 116, 480, 271, 41], [90, 245, 21, 135, 374, 39], [399, 172, 153, 17, 150, 220]], ![[182, 195, 102, 200, 428, 302], [412, 465, 409, 143, 66, 416], [65, 208, 422, 235, 296, 306], [332, 85, 58], [83, 6, 84], [228, 244, 397, 2, 398, 208], [292, 361, 76, 475, 423, 229], [85, 214, 169, 35, 120, 309]], ![[158, 321, 143, 217, 197, 416], [282, 236, 19, 230, 239, 183], [482, 202, 468, 325, 357, 79], [202, 173, 166], [298, 368, 135], [144, 32, 482, 199, 403, 176], [479, 208, 388, 319, 387, 478], [59, 448, 380, 31, 164, 479]]]
 h' := ![![[124, 473, 271, 475], [199, 434, 193, 410], [393, 456, 95, 310], [47, 391, 154, 152], [179, 341, 108, 121], [378, 209, 53, 118], [143, 409, 376, 248], [0, 0, 0, 1], [0, 1]], ![[160, 405, 474, 14], [79, 245, 153, 41], [474, 318, 256, 325], [328, 473, 390, 301], [188, 182, 445, 290], [466, 426, 45, 409], [75, 355, 279, 191], [432, 80, 430, 228], [124, 473, 271, 475]], ![[39, 95, 229, 485], [469, 138, 482, 399], [223, 430, 438, 90], [375, 345, 391, 310], [96, 33, 427, 127], [207, 113, 155, 145], [174, 379, 9, 199], [324, 25, 485, 151], [160, 405, 474, 14]], ![[0, 1], [171, 157, 146, 124], [19, 257, 185, 249], [193, 252, 39, 211], [1, 418, 481, 436], [71, 226, 234, 302], [303, 318, 310, 336], [342, 382, 59, 107], [39, 95, 229, 485]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [283, 9, 33], []]
 b := ![[], [], [383, 132, 438, 102], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI487N0 : CertifiedPrimeIdeal' SI487N0 487 where
  n := 4
  hpos := by decide
  P := [298, 307, 246, 164, 1]
  hirr := P487P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-61962707182, -21920040282768, -13038807028778, -2001005119044, -44469746391428]
  a := ![-53, 134, 111, 72, 336]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![43282541738870, 26983829346160, 11204804926318, 7666237560084, -44469746391428]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI487N0 : Ideal.IsPrime I487N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI487N0 B_one_repr
lemma NI487N0 : Nat.card (O ⧸ I487N0) = 56249134561 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI487N0

def I487N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-14, -2, 2, 1, 3]] i)))

def SI487N1: IdealEqSpanCertificate' Table ![![-14, -2, 2, 1, 3]] 
 ![![487, 0, 0, 0, 0], ![223, 1, 0, 0, 0], ![432, 0, 1, 0, 0], ![177, 0, 0, 1, 0], ![284, 0, 0, 0, 1]] where
  M :=![![![-14, -2, 2, 1, 3], ![-24, -11, 10, 4, 20], ![-144, -42, 37, 4, 32], ![-96, -86, -2, 15, -30], ![69, 36, -12, -1, 8]]]
  hmulB := by decide  
  f := ![![![43414, 14342, -12622, -4617, -18961]], ![![20170, 6663, -5864, -2145, -8809]], ![![39456, 13034, -11471, -4196, -17232]], ![![17172, 5672, -4992, -1826, -7499]], ![![24833, 8204, -7220, -2641, -10846]]]
  g := ![![![-3, -2, 2, 1, 3], ![-17, -11, 10, 4, 20], ![-34, -42, 37, 4, 32], ![53, -86, -2, 15, -30], ![-10, 36, -12, -1, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI487N1 : Nat.card (O ⧸ I487N1) = 487 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI487N1)

lemma isPrimeI487N1 : Ideal.IsPrime I487N1 := prime_ideal_of_norm_prime hp487.out _ NI487N1
def MulI487N0 : IdealMulLeCertificate' Table 
  ![![-43414, -14342, 12622, 4617, 18961]] ![![-14, -2, 2, 1, 3]]
  ![![487, 0, 0, 0, 0]] where
 M := ![![![-487, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC487 : ContainsPrimesAboveP 487 ![I487N0, I487N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI487N0
    exact isPrimeI487N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 487 (by decide) (𝕀 ⊙ MulI487N0)
instance hp491 : Fact (Nat.Prime 491) := {out := by norm_num}

def I491N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11, -23, 135, -18, 196]] i)))

def SI491N0: IdealEqSpanCertificate' Table ![![-11, -23, 135, -18, 196]] 
 ![![491, 0, 0, 0, 0], ![0, 491, 0, 0, 0], ![0, 0, 491, 0, 0], ![0, 0, 0, 491, 0], ![273, 303, 399, 45, 1]] where
  M :=![![![-11, -23, 135, -18, 196], ![-1068, -894, -239, -230, -1860], ![12540, 3143, -3654, 1862, 2420], ![-12312, 12153, 12863, -373, 29048], ![-6180, -5780, -572, -1364, -9643]]]
  hmulB := by decide  
  f := ![![![2879, 963, -825, -302, -1244]], ![![9276, 3104, -2661, -974, -4012]], ![![29916, 10001, -8584, -3142, -12940]], ![![43608, 14571, -12521, -4583, -18872]], ![![35601, 11903, -10215, -3739, -15399]]]
  g := ![![![-109, -121, -159, -18, 196], ![1032, 1146, 1511, 170, -1860], ![-1320, -1487, -1974, -218, 2420], ![-16176, -17901, -23579, -2663, 29048], ![5349, 5939, 7835, 881, -9643]]]
  hle1 := by decide   
  hle2 := by decide  


def P491P0 : CertificateIrreducibleZModOfList' 491 4 2 8 [444, 433, 305, 343, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [292, 264, 384, 54], [250, 489, 191, 292], [97, 228, 407, 145], [0, 1]]
 g := ![![[48, 11, 132, 272], [407, 266, 7, 409], [117, 247, 147], [264, 33, 11, 131], [145, 251, 168], [362, 32, 280, 413], [332, 486, 148, 1], []], ![[12, 40, 69, 485, 275, 322], [455, 375, 28, 118, 375, 475], [182, 56, 134], [182, 483, 0, 76, 239, 268], [144, 313, 108], [191, 72, 67, 110, 468, 353], [213, 100, 170, 286, 207, 353], [325, 475, 268, 150, 149, 344]], ![[462, 27, 255, 450, 465, 66], [335, 62, 467, 157, 444, 471], [286, 412, 208], [373, 288, 11, 154, 323, 95], [228, 182, 418], [82, 168, 308, 404, 205, 2], [1, 310, 88, 46, 45, 474], [52, 287, 446, 475, 412, 442]], ![[221, 396, 187, 490, 191, 250], [116, 44, 415, 153, 458, 278], [127, 124, 132], [1, 268, 104, 117, 268, 186], [177, 269, 424], [288, 292, 205, 392, 264, 23], [171, 347, 463, 231, 99, 307], [380, 221, 40, 3, 478, 6]]]
 h' := ![![[292, 264, 384, 54], [471, 311, 370, 320], [111, 366, 96, 30], [133, 366, 127, 300], [213, 315, 358, 71], [320, 285, 12, 427], [383, 363, 169, 372], [0, 0, 0, 1], [0, 1]], ![[250, 489, 191, 292], [322, 479, 379, 130], [385, 207, 207, 40], [81, 129, 449, 25], [319, 225, 79, 423], [400, 228, 185, 304], [126, 217, 369, 266], [5, 316, 311, 266], [292, 264, 384, 54]], ![[97, 228, 407, 145], [403, 165, 40, 132], [310, 103, 178, 11], [247, 489, 71, 450], [318, 466, 226, 192], [366, 317, 391, 58], [110, 317, 66, 414], [387, 426, 140, 321], [250, 489, 191, 292]], ![[0, 1], [182, 27, 193, 400], [148, 306, 10, 410], [276, 489, 335, 207], [164, 467, 319, 296], [78, 152, 394, 193], [119, 85, 378, 421], [88, 240, 40, 394], [97, 228, 407, 145]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [376, 271, 209], []]
 b := ![[], [], [163, 93, 449, 307], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI491N0 : CertifiedPrimeIdeal' SI491N0 491 where
  n := 4
  hpos := by decide
  P := [444, 433, 305, 343, 1]
  hirr := P491P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![118061247303118, 41830023533020, -29604083561834, 19400066004834, 44842596170564]
  a := ![59, -126, -123, -55, -374]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-24692398181794, -27587528749792, -36500610907570, -4070298903606, 44842596170564]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI491N0 : Ideal.IsPrime I491N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI491N0 B_one_repr
lemma NI491N0 : Nat.card (O ⧸ I491N0) = 58120048561 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI491N0

def I491N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2879, 963, -825, -302, -1244]] i)))

def SI491N1: IdealEqSpanCertificate' Table ![![2879, 963, -825, -302, -1244]] 
 ![![491, 0, 0, 0, 0], ![260, 1, 0, 0, 0], ![158, 0, 1, 0, 0], ![443, 0, 0, 1, 0], ![197, 0, 0, 0, 1]] where
  M :=![![![2879, 963, -825, -302, -1244], ![9276, 3104, -2661, -974, -4012], ![29916, 10001, -8584, -3142, -12940], ![43608, 14571, -12521, -4583, -18872], ![-15348, -5132, 4404, 1612, 6639]]]
  hmulB := by decide  
  f := ![![![-11, -23, 135, -18, 196]], ![![-8, -14, 71, -10, 100]], ![![22, -1, 36, -2, 68]], ![![-35, 4, 148, -17, 236]], ![![-17, -21, 53, -10, 59]]]
  g := ![![![533, 963, -825, -302, -1244], ![1720, 3104, -2661, -974, -4012], ![5554, 10001, -8584, -3142, -12940], ![8109, 14571, -12521, -4583, -18872], ![-2849, -5132, 4404, 1612, 6639]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI491N1 : Nat.card (O ⧸ I491N1) = 491 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI491N1)

lemma isPrimeI491N1 : Ideal.IsPrime I491N1 := prime_ideal_of_norm_prime hp491.out _ NI491N1
def MulI491N0 : IdealMulLeCertificate' Table 
  ![![-11, -23, 135, -18, 196]] ![![2879, 963, -825, -302, -1244]]
  ![![491, 0, 0, 0, 0]] where
 M := ![![![491, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC491 : ContainsPrimesAboveP 491 ![I491N0, I491N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI491N0
    exact isPrimeI491N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 491 (by decide) (𝕀 ⊙ MulI491N0)
instance hp499 : Fact (Nat.Prime 499) := {out := by norm_num}

def I499N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-308, -100, 94, 71, 247]] i)))

def SI499N0: IdealEqSpanCertificate' Table ![![-308, -100, 94, 71, 247]] 
 ![![499, 0, 0, 0, 0], ![0, 499, 0, 0, 0], ![0, 0, 499, 0, 0], ![389, 427, 376, 1, 0], ![93, 91, 62, 0, 1]] where
  M :=![![![-308, -100, 94, 71, 247], ![-1908, -279, 752, 120, 1216], ![-8016, -4460, 1161, -208, -2736], ![9786, 832, -3854, 3213, 3648], ![507, 2228, 1036, -359, 2548]]]
  hmulB := by decide  
  f := ![![![-4772, -2708, 1770, 629, 2755]], ![![-20304, -5845, 4840, 1804, 7372]], ![![-55056, -21500, 15803, 5760, 24320]], ![![-62740, -23369, 17472, 6390, 26847]], ![![-11373, -4221, 3160, 1156, 4855]]]
  g := ![![![-102, -106, -84, 71, 247], ![-324, -325, -240, 120, 1216], ![656, 668, 499, -208, -2736], ![-3165, -3413, -2882, 3213, 3648], ![-194, -153, -44, -359, 2548]]]
  hle1 := by decide   
  hle2 := by decide  


def P499P0 : CertificateIrreducibleZModOfList' 499 3 2 8 [58, 221, 25, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [263, 481, 4], [211, 17, 495], [0, 1]]
 g := ![![[331, 239, 184], [439, 151, 77], [129, 268], [172, 251], [5, 324, 476], [252, 285, 110], [47, 415, 126], [1]], ![[106, 210, 362, 440], [33, 59, 484, 449], [414, 263], [25, 400], [227, 126, 83, 122], [231, 196, 172, 270], [485, 248, 35, 159], [323, 96, 31, 64]], ![[40, 60, 177, 168], [403, 434, 134, 465], [382, 33], [83, 43], [489, 5, 322, 128], [223, 85, 423, 141], [61, 477, 292, 11], [259, 324, 420, 435]]]
 h' := ![![[263, 481, 4], [486, 272, 41], [135, 168, 24], [272, 273, 209], [209, 130, 115], [354, 101, 436], [268, 344, 288], [441, 278, 474], [0, 1]], ![[211, 17, 495], [3, 66, 288], [56, 124, 82], [90, 128, 154], [95, 186, 479], [331, 148, 331], [201, 147, 284], [131, 283, 188], [263, 481, 4]], ![[0, 1], [175, 161, 170], [406, 207, 393], [439, 98, 136], [154, 183, 404], [295, 250, 231], [28, 8, 426], [204, 437, 336], [211, 17, 495]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [408, 212], []]
 b := ![[], [428, 442, 446], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI499N0 : CertifiedPrimeIdeal' SI499N0 499 where
  n := 3
  hpos := by decide
  P := [58, 221, 25, 1]
  hirr := P499P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6399991948, -1274812382, -3721344764, 685610784, -4875613066]
  a := ![-42, 82, 88, 24, 266]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![387032890, 299900144, 81717456, 685610784, -4875613066]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI499N0 : Ideal.IsPrime I499N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI499N0 B_one_repr
lemma NI499N0 : Nat.card (O ⧸ I499N0) = 124251499 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI499N0

def I499N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-64, 26, -6, -1, -11]] i)))

def SI499N1: IdealEqSpanCertificate' Table ![![-64, 26, -6, -1, -11]] 
 ![![499, 0, 0, 0, 0], ![104, 1, 0, 0, 0], ![162, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![208, 0, 0, 0, 1]] where
  M :=![![![-64, 26, -6, -1, -11], ![72, -39, 14, 4, 28], ![-192, 26, 9, -4, -16], ![24, -66, -18, 11, -42], ![27, 28, -4, 1, 18]]]
  hmulB := by decide  
  f := ![![![288776, 102874, -78126, -28667, -119887]], ![![61972, 22077, -16766, -6152, -25728]], ![![99264, 35362, -26855, -9854, -41210]], ![![11666, 4156, -3156, -1158, -4843]], ![![117527, 41868, -31796, -11667, -48792]]]
  g := ![![![1, 26, -6, -1, -11], ![-8, -39, 14, 4, 28], ![-2, 26, 9, -4, -16], ![37, -66, -18, 11, -42], ![-12, 28, -4, 1, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI499N1 : Nat.card (O ⧸ I499N1) = 499 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI499N1)

lemma isPrimeI499N1 : Ideal.IsPrime I499N1 := prime_ideal_of_norm_prime hp499.out _ NI499N1

def I499N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![247646, 81778, -71826, -26279, -107935]] i)))

def SI499N2: IdealEqSpanCertificate' Table ![![247646, 81778, -71826, -26279, -107935]] 
 ![![499, 0, 0, 0, 0], ![142, 1, 0, 0, 0], ![295, 0, 1, 0, 0], ![441, 0, 0, 1, 0], ![84, 0, 0, 0, 1]] where
  M :=![![![247646, 81778, -71826, -26279, -107935], ![805284, 265933, -233570, -85456, -350992], ![2618688, 864754, -759539, -277892, -1141376], ![3855162, 1273062, -1118190, -409111, -1680324], ![-1342143, -443212, 389284, 142427, 584986]]]
  hmulB := by decide  
  f := ![![![6866, 3986, -762, 1283, 5857]], ![![1868, 1133, -178, 354, 1694]], ![![3962, 2056, -585, 715, 2877]], ![![7998, 4296, -1104, 1460, 6093]], ![![717, 700, 92, 163, 1200]]]
  g := ![![![61081, 81778, -71826, -26279, -107935], ![198628, 265933, -233570, -85456, -350992], ![645919, 864754, -759539, -277892, -1141376], ![950925, 1273062, -1118190, -409111, -1680324], ![-331050, -443212, 389284, 142427, 584986]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI499N2 : Nat.card (O ⧸ I499N2) = 499 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI499N2)

lemma isPrimeI499N2 : Ideal.IsPrime I499N2 := prime_ideal_of_norm_prime hp499.out _ NI499N2
def MulI499N0 : IdealMulLeCertificate' Table 
  ![![-308, -100, 94, 71, 247]] ![![-64, 26, -6, -1, -11]]
  ![![2837, 566, -972, 560, 548]] where
 M := ![![![2837, 566, -972, 560, 548]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI499N1 : IdealMulLeCertificate' Table 
  ![![2837, 566, -972, 560, 548]] ![![247646, 81778, -71826, -26279, -107935]]
  ![![499, 0, 0, 0, 0]] where
 M := ![![![36394066, 12015920, -10557842, -3862759, -15864707]]]
 hmul := by decide  
 g := ![![![![72934, 24080, -21158, -7741, -31793]]]]
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

def I503N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-27922, 12247, -2945, -631, -5387]] i)))

def SI503N0: IdealEqSpanCertificate' Table ![![-27922, 12247, -2945, -631, -5387]] 
 ![![503, 0, 0, 0, 0], ![0, 503, 0, 0, 0], ![502, 495, 1, 0, 0], ![499, 471, 0, 1, 0], ![450, 332, 0, 0, 1]] where
  M :=![![![-27922, 12247, -2945, -631, -5387], ![36108, -17522, 4675, 1098, 8344], ![-56652, 21681, -4346, -750, -8340], ![9216, -9933, 4003, 1195, 6598], ![-1557, 2712, -1208, -375, -1960]]]
  hmulB := by decide  
  f := ![![![-6902, -2479, 1855, 679, 2809]], ![![-20928, -7456, 5669, 2166, 8948]], ![![-27616, -9857, 7467, 2822, 11666]], ![![-26632, -9512, 7197, 2718, 11229]], ![![-19917, -7114, 5382, 2031, 8392]]]
  g := ![![![8329, 7069, -2945, -631, -5387], ![-13148, -11171, 4675, 1098, 8344], ![12430, 10527, -4346, -750, -8340], ![-11065, -9433, 4003, 1195, 6598], ![3328, 2839, -1208, -375, -1960]]]
  hle1 := by decide   
  hle2 := by decide  


def P503P0 : CertificateIrreducibleZModOfList' 503 2 2 8 [277, 232, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [271, 502], [0, 1]]
 g := ![![[88, 185], [234, 66], [23, 339], [85], [280, 147], [54, 368], [119, 129], [271, 1]], ![[426, 318], [12, 437], [346, 164], [85], [380, 356], [188, 135], [371, 374], [39, 502]]]
 h' := ![![[271, 502], [69, 421], [168, 181], [143, 210], [405, 273], [132, 115], [235, 353], [383, 229], [0, 1]], ![[0, 1], [482, 82], [428, 322], [214, 293], [447, 230], [111, 388], [328, 150], [70, 274], [271, 502]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [249]]
 b := ![[], [358, 376]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI503N0 : CertifiedPrimeIdeal' SI503N0 503 where
  n := 2
  hpos := by decide
  P := [277, 232, 1]
  hirr := P503P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2292882, -716, 1089596, -92096, 1252096]
  a := ![-65, 150, 140, 80, 416]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2120790, -1812464, 1089596, -92096, 1252096]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI503N0 : Ideal.IsPrime I503N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI503N0 B_one_repr
lemma NI503N0 : Nat.card (O ⧸ I503N0) = 253009 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI503N0

def I503N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![231044, -105384, 26410, 5885, 47833]] i)))

def SI503N1: IdealEqSpanCertificate' Table ![![231044, -105384, 26410, 5885, 47833]] 
 ![![503, 0, 0, 0, 0], ![0, 503, 0, 0, 0], ![339, 152, 1, 0, 0], ![392, 187, 0, 1, 0], ![82, 72, 0, 0, 1]] where
  M :=![![![231044, -105384, 26410, 5885, 47833], ![-322308, 142627, -34764, -7536, -63368], ![425424, -201568, 52195, 11992, 93840], ![-156342, 57764, -11450, -1901, -21988], ![40857, -13652, 2308, 275, 4640]]]
  hmulB := by decide  
  f := ![![![-5588, -1736, 1686, 603, 2657]], ![![-19560, -6691, 5500, 1676, 6972]], ![![-9780, -3232, 2825, 927, 3941]], ![![-11780, -3867, 3418, 1117, 4794]], ![![-3667, -1228, 1048, 329, 1396]]]
  g := ![![![-29724, -17225, 26410, 5885, 47833], ![38992, 22661, -34764, -7536, -63368], ![-58975, -34064, 52195, 11992, 93840], ![12472, 7429, -11450, -1901, -21988], ![-2445, -1491, 2308, 275, 4640]]]
  hle1 := by decide   
  hle2 := by decide  


def P503P1 : CertificateIrreducibleZModOfList' 503 2 2 8 [38, 274, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [229, 502], [0, 1]]
 g := ![![[219, 81], [260, 207], [139, 128], [389], [336, 219], [489, 344], [222, 233], [229, 1]], ![[157, 422], [381, 296], [277, 375], [389], [187, 284], [294, 159], [261, 270], [458, 502]]]
 h' := ![![[229, 502], [180, 494], [251, 364], [335, 250], [310, 49], [29, 468], [115, 401], [352, 91], [0, 1]], ![[0, 1], [131, 9], [109, 139], [243, 253], [465, 454], [62, 35], [398, 102], [65, 412], [229, 502]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [197]]
 b := ![[], [165, 350]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI503N1 : CertifiedPrimeIdeal' SI503N1 503 where
  n := 2
  hpos := by decide
  P := [38, 274, 1]
  hirr := P503P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-137983, -49030, 36473, -20268, -43664]
  a := ![-13, 24, 27, 8, 82]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1942, 2666, 36473, -20268, -43664]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI503N1 : Ideal.IsPrime I503N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI503N1 B_one_repr
lemma NI503N1 : Nat.card (O ⧸ I503N1) = 253009 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI503N1

def I503N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![221, -108, 30, 4, 46]] i)))

def SI503N2: IdealEqSpanCertificate' Table ![![221, -108, 30, 4, 46]] 
 ![![503, 0, 0, 0, 0], ![359, 1, 0, 0, 0], ![390, 0, 1, 0, 0], ![487, 0, 0, 1, 0], ![212, 0, 0, 0, 1]] where
  M :=![![![221, -108, 30, 4, 46], ![-300, 119, -60, -8, -124], ![792, 32, 23, 80, 440], ![-1410, -12, 526, -173, 262], ![96, -176, -120, -8, -345]]]
  hmulB := by decide  
  f := ![![![-3020165, -999668, 874242, 319884, 1314514]], ![![-2175041, -719933, 629606, 230372, 946678]], ![![-2404986, -796040, 696171, 254728, 1046764]], ![![-3017143, -998656, 873376, 319567, 1313208]], ![![-1240460, -410592, 359072, 131384, 539903]]]
  g := ![![![31, -108, 30, 4, 46], ![21, 119, -60, -8, -124], ![-302, 32, 23, 80, 440], ![-345, -12, 526, -173, 262], ![372, -176, -120, -8, -345]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI503N2 : Nat.card (O ⧸ I503N2) = 503 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI503N2)

lemma isPrimeI503N2 : Ideal.IsPrime I503N2 := prime_ideal_of_norm_prime hp503.out _ NI503N2
def MulI503N0 : IdealMulLeCertificate' Table 
  ![![-27922, 12247, -2945, -631, -5387]] ![![231044, -105384, 26410, 5885, 47833]]
  ![![-11772835181, 5319996917, -1322097249, -292212696, -2399140974]] where
 M := ![![![-11772835181, 5319996917, -1322097249, -292212696, -2399140974]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI503N1 : IdealMulLeCertificate' Table 
  ![![-11772835181, 5319996917, -1322097249, -292212696, -2399140974]] ![![221, -108, 30, 4, 46]]
  ![![503, 0, 0, 0, 0]] where
 M := ![![![-5063194303453, 2287994084479, -568600068393, -125673171780, -1031808915916]]]
 hmul := by decide  
 g := ![![![![-10065992651, 4548695993, -1130417631, -249847260, -2051309972]]]]
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

def I509N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![20256515, -9201129, 2297359, 510092, 4164418]] i)))

def SI509N0: IdealEqSpanCertificate' Table ![![20256515, -9201129, 2297359, 510092, 4164418]] 
 ![![509, 0, 0, 0, 0], ![0, 509, 0, 0, 0], ![0, 0, 509, 0, 0], ![0, 0, 0, 509, 0], ![320, 83, 457, 430, 1]] where
  M :=![![![20256515, -9201129, 2297359, 510092, 4164418], ![-28047060, 12527398, -3080025, -673566, -5603012], ![37659468, -17471395, 4444606, 1004578, 8022564], ![-13057896, 5272967, -1168217, -227441, -2179204], ![3342750, -1276580, 264268, 46946, 501647]]]
  hmulB := by decide  
  f := ![![![-1037, -125, 405, -144, 110]], ![![204, -2944, -1853, -274, -6132]], ![![38436, 19317, -6232, 6914, 26380]], ![![-99984, 9755, 52069, -11733, 55292]], ![![-50582, 24991, 38327, -3844, 69395]]]
  g := ![![![-2578305, -697147, -3734463, -3517072, 4164418], ![3467420, 938266, 5024551, 4732066, -5603012], ![-4969668, -1342523, -7194238, -6775438, 8022564], ![1344376, 365711, 1954279, 1840531, -2179204], ![-308810, -84309, -449879, -423696, 501647]]]
  hle1 := by decide   
  hle2 := by decide  


def P509P0 : CertificateIrreducibleZModOfList' 509 4 2 8 [426, 43, 345, 70, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [378, 222, 36, 372], [252, 250, 281, 458], [318, 36, 192, 188], [0, 1]]
 g := ![![[164, 102, 137, 187], [505, 19, 452], [324, 46, 388, 222], [117, 118, 21, 473], [160, 39, 95, 123], [220, 506, 200, 56], [477, 483, 439, 1], []], ![[227, 83, 277, 359, 222, 104], [164, 55, 388], [32, 255, 338, 136, 222, 30], [85, 422, 264, 401, 205, 91], [135, 352, 443, 428, 260, 386], [322, 76, 23, 296, 375, 17], [215, 246, 207, 43, 259, 49], [353, 43, 261, 244, 308, 115]], ![[351, 347, 337, 447, 346, 204], [369, 122, 54], [116, 279, 293, 462, 38, 475], [236, 251, 347, 357, 441, 468], [129, 177, 450, 199, 167, 227], [261, 338, 274, 76, 138, 399], [332, 81, 493, 465, 370, 437], [483, 4, 323, 154, 263, 198]], ![[19, 443, 2, 228, 36, 140], [216, 387, 355], [27, 215, 104, 32, 485, 491], [185, 142, 186, 189, 275, 341], [313, 191, 461, 291, 239, 444], [299, 6, 186, 350, 381, 230], [269, 199, 176, 368, 92, 343], [422, 307, 188, 204, 394, 186]]]
 h' := ![![[378, 222, 36, 372], [276, 6, 230, 291], [424, 139, 486, 31], [40, 262, 16, 116], [46, 453, 458, 279], [445, 67, 417, 387], [398, 236, 240, 51], [0, 0, 0, 1], [0, 1]], ![[252, 250, 281, 458], [374, 295, 190, 52], [93, 108, 353, 257], [260, 134, 178, 395], [162, 87, 281, 77], [309, 15, 466, 460], [201, 195, 184, 411], [448, 237, 313, 16], [378, 222, 36, 372]], ![[318, 36, 192, 188], [397, 200, 319, 93], [451, 234, 471, 96], [32, 201, 405, 159], [30, 294, 285, 135], [383, 206, 61, 28], [123, 98, 67, 453], [435, 284, 322, 138], [252, 250, 281, 458]], ![[0, 1], [489, 8, 279, 73], [365, 28, 217, 125], [412, 421, 419, 348], [262, 184, 503, 18], [499, 221, 74, 143], [124, 489, 18, 103], [244, 497, 383, 354], [318, 36, 192, 188]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [376, 256, 403], []]
 b := ![[], [], [445, 43, 197, 467], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI509N0 : CertifiedPrimeIdeal' SI509N0 509 where
  n := 4
  hpos := by decide
  P := [426, 43, 345, 70, 1]
  hirr := P509P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![463278374788173, 94806697185826, -157569579282740, 69211599587615, 33616403073066]
  a := ![-87, 190, 184, 89, 552]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-20223910822383, -5295392451628, -30491681303878, -28262950337585, 33616403073066]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI509N0 : Ideal.IsPrime I509N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI509N0 B_one_repr
lemma NI509N0 : Nat.card (O ⧸ I509N0) = 67122964561 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI509N0

def I509N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1037, -125, 405, -144, 110]] i)))

def SI509N1: IdealEqSpanCertificate' Table ![![-1037, -125, 405, -144, 110]] 
 ![![509, 0, 0, 0, 0], ![463, 1, 0, 0, 0], ![429, 0, 1, 0, 0], ![219, 0, 0, 1, 0], ![191, 0, 0, 0, 1]] where
  M :=![![![-1037, -125, 405, -144, 110], ![204, -2944, -1853, -274, -6132], ![38436, 19317, -6232, 6914, 26380], ![-99984, 9755, 52069, -11733, 55292], ![-3462, -17748, -9004, -2282, -35409]]]
  hmulB := by decide  
  f := ![![![20256515, -9201129, 2297359, 510092, 4164418]], ![![18370765, -8344981, 2083688, 462670, 3777058]], ![![17146767, -7789304, 1945013, 431894, 3525654]], ![![8689821, -3948476, 986156, 219023, 1787482]], ![![7607735, -3455191, 862593, 191502, 1563665]]]
  g := ![![![-209, -125, 405, -144, 110], ![6659, -2944, -1853, -274, -6132], ![-25117, 19317, -6232, 6914, 26380], ![-68655, 9755, 52069, -11733, 55292], ![37995, -17748, -9004, -2282, -35409]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI509N1 : Nat.card (O ⧸ I509N1) = 509 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI509N1)

lemma isPrimeI509N1 : Ideal.IsPrime I509N1 := prime_ideal_of_norm_prime hp509.out _ NI509N1
def MulI509N0 : IdealMulLeCertificate' Table 
  ![![20256515, -9201129, 2297359, 510092, 4164418]] ![![-1037, -125, 405, -144, 110]]
  ![![509, 0, 0, 0, 0]] where
 M := ![![![509, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I521N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![133390, 46890, -35466, -13035, -54483]] i)))

def SI521N0: IdealEqSpanCertificate' Table ![![133390, 46890, -35466, -13035, -54483]] 
 ![![521, 0, 0, 0, 0], ![0, 521, 0, 0, 0], ![0, 0, 521, 0, 0], ![0, 0, 0, 521, 0], ![47, 0, 319, 413, 1]] where
  M :=![![![133390, 46890, -35466, -13035, -54483], ![405108, 146401, -109530, -40176, -168432], ![1251648, 447018, -335711, -123252, -516096], ![1715490, 615822, -461238, -169283, -709284], ![-644931, -231324, 173460, 63663, 266698]]]
  hmulB := by decide  
  f := ![![![-10, -18, -6, -3, -33]], ![![216, 77, -54, 36, 84]], ![![-720, 294, 509, -60, 864]], ![![-2520, -2262, -186, -553, -3774]], ![![-2437, -1614, 163, -475, -2465]]]
  g := ![![![5171, 90, 33291, 43164, -54483], ![15972, 281, 102918, 133440, -168432], ![48960, 858, 315353, 408876, -516096], ![67278, 1182, 433398, 561929, -709284], ![-25297, -444, -162962, -211291, 266698]]]
  hle1 := by decide   
  hle2 := by decide  


def P521P0 : CertificateIrreducibleZModOfList' 521 4 2 9 [251, 60, 485, 440, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 425, 104, 144], [285, 452, 422, 202], [304, 164, 516, 175], [0, 1]]
 g := ![![[303, 392, 49, 151], [475, 159, 283], [208, 274, 64], [103, 170, 473, 508], [439, 418, 383], [121, 290, 11], [78, 122, 309], [1], []], ![[205, 221, 311, 372, 38, 110], [8, 255, 226], [186, 378, 469], [77, 274, 202, 70, 338, 128], [117, 126, 201], [324, 10, 4], [399, 269, 440], [480, 303, 176], [245, 167, 417]], ![[422, 190, 355, 336, 22, 32], [124, 284, 464], [96, 374, 196], [307, 520, 477, 75, 153, 55], [48, 48, 210], [265, 230, 405], [274, 235, 49], [281, 220, 169], [22, 21, 166]], ![[250, 426, 96, 441, 226, 367], [119, 147, 180], [474, 424, 21], [145, 151, 95, 56, 454, 369], [141, 272, 99], [68, 174, 183], [375, 240, 286], [196, 263, 279], [343, 478, 407]]]
 h' := ![![[13, 425, 104, 144], [332, 164, 382, 190], [147, 274, 396, 437], [197, 318, 149, 8], [162, 1, 12, 107], [466, 365, 518, 325], [180, 28, 363, 330], [270, 461, 36, 81], [0, 0, 1], [0, 1]], ![[285, 452, 422, 202], [401, 287, 198, 23], [164, 153, 86, 98], [251, 142, 354, 214], [355, 216, 177, 355], [5, 135, 397, 479], [400, 363, 339, 519], [51, 369, 310, 490], [152, 281, 354, 243], [13, 425, 104, 144]], ![[304, 164, 516, 175], [107, 122, 111, 125], [407, 326, 263, 355], [517, 9, 442, 507], [111, 229, 93, 405], [278, 180, 467, 186], [288, 300, 421, 228], [281, 195, 490, 514], [158, 448, 498, 508], [285, 452, 422, 202]], ![[0, 1], [26, 469, 351, 183], [77, 289, 297, 152], [493, 52, 97, 313], [484, 75, 239, 175], [268, 362, 181, 52], [404, 351, 440, 486], [130, 17, 206, 478], [71, 313, 189, 291], [304, 164, 516, 175]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [272, 212, 502], []]
 b := ![[], [], [265, 35, 87, 111], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI521N0 : CertifiedPrimeIdeal' SI521N0 521 where
  n := 4
  hpos := by decide
  P := [251, 60, 485, 440, 1]
  hirr := P521P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![13564045323937, 3148428414380, -4390588051054, 2066011102292, 1755497688924]
  a := ![-35, 76, 73, 34, 222]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-132330798571, 6043048780, -1083290500610, -1387628664920, 1755497688924]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI521N0 : Ideal.IsPrime I521N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI521N0 B_one_repr
lemma NI521N0 : Nat.card (O ⧸ I521N0) = 73680216481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI521N0

def I521N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10, -18, -6, -3, -33]] i)))

def SI521N1: IdealEqSpanCertificate' Table ![![-10, -18, -6, -3, -33]] 
 ![![521, 0, 0, 0, 0], ![463, 1, 0, 0, 0], ![283, 0, 1, 0, 0], ![421, 0, 0, 1, 0], ![479, 0, 0, 0, 1]] where
  M :=![![![-10, -18, -6, -3, -33], ![216, 77, -54, 36, 84], ![-720, 294, 509, -60, 864], ![-2520, -2262, -186, -553, -3774], ![1233, 372, -348, 195, 332]]]
  hmulB := by decide  
  f := ![![![133390, 46890, -35466, -13035, -54483]], ![![119318, 41951, -31728, -11661, -48741]], ![![74858, 26328, -19909, -7317, -30585]], ![![111080, 39072, -29544, -10858, -45387]], ![![121399, 42666, -32274, -11862, -49579]]]
  g := ![![![52, -18, -6, -3, -33], ![-145, 77, -54, 36, 84], ![-1285, 294, 509, -60, 864], ![6023, -2262, -186, -553, -3774], ![-602, 372, -348, 195, 332]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI521N1 : Nat.card (O ⧸ I521N1) = 521 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI521N1)

lemma isPrimeI521N1 : Ideal.IsPrime I521N1 := prime_ideal_of_norm_prime hp521.out _ NI521N1
def MulI521N0 : IdealMulLeCertificate' Table 
  ![![133390, 46890, -35466, -13035, -54483]] ![![-10, -18, -6, -3, -33]]
  ![![521, 0, 0, 0, 0]] where
 M := ![![![521, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC521 : ContainsPrimesAboveP 521 ![I521N0, I521N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI521N0
    exact isPrimeI521N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 521 (by decide) (𝕀 ⊙ MulI521N0)
instance hp523 : Fact (Nat.Prime 523) := {out := by norm_num}

def I523N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43508, 30133, -18829, -6609, -29431]] i)))

def SI523N0: IdealEqSpanCertificate' Table ![![43508, 30133, -18829, -6609, -29431]] 
 ![![523, 0, 0, 0, 0], ![0, 523, 0, 0, 0], ![0, 0, 523, 0, 0], ![0, 0, 0, 523, 0], ![120, 422, 395, 262, 1]] where
  M :=![![![43508, 30133, -18829, -6609, -29431], ![216240, 56486, -49175, -18450, -74556], ![558036, 225439, -164914, -59938, -253764], ![832986, 286249, -222321, -81739, -340252], ![-308223, -107032, 82752, 30403, 126704]]]
  hmulB := by decide  
  f := ![![![44, -1, -21, 5, -19]], ![![84, 164, 59, 26, 304]], ![![-1980, -735, 476, -334, -836]], ![![3468, -1333, -2401, 297, -3990]], ![![321, -1089, -800, -81, -2386]]]
  g := ![![![6836, 23805, 22192, 14731, -29431], ![17520, 60266, 56215, 37314, -74556], ![59292, 205189, 191342, 127010, -253764], ![79662, 275091, 256553, 170295, -340252], ![-29661, -102440, -95536, -63415, 126704]]]
  hle1 := by decide   
  hle2 := by decide  


def P523P0 : CertificateIrreducibleZModOfList' 523 4 2 9 [407, 339, 179, 112, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [84, 209, 93, 253], [432, 482, 112, 214], [418, 354, 318, 56], [0, 1]]
 g := ![![[145, 500, 327, 428], [405, 441, 190, 201], [183, 502, 451], [490, 39, 326, 295], [212, 225, 331], [446, 90, 456], [415, 198, 515], [1], []], ![[378, 259, 487, 230, 323, 53], [411, 15, 212, 52, 214, 505], [301, 425, 425], [251, 134, 288, 133, 102, 66], [69, 401, 42], [17, 40, 341], [125, 393, 289], [351, 497, 395], [382, 264, 203]], ![[328, 115, 65, 140, 278, 311], [179, 281, 136, 441, 81, 33], [202, 93, 187], [289, 314, 177, 11, 262, 372], [0, 177, 176], [303, 108, 345], [204, 393, 78], [493, 465, 272], [262, 252, 295]], ![[207, 60, 216, 78, 330, 199], [473, 277, 415, 229, 401, 83], [457, 210, 502], [162, 414, 296, 41, 368, 447], [302, 353, 356], [267, 10, 172], [240, 218, 378], [316, 68, 174], [388, 276, 521]]]
 h' := ![![[84, 209, 93, 253], [433, 89, 42, 394], [478, 172, 352, 215], [356, 497, 37, 336], [171, 255, 120, 309], [285, 89, 457, 78], [405, 283, 94, 478], [116, 184, 344, 411], [0, 0, 1], [0, 1]], ![[432, 482, 112, 214], [456, 359, 300, 316], [318, 19, 423, 403], [388, 223, 341, 131], [154, 188, 278, 76], [426, 466, 287, 418], [447, 399, 92, 276], [366, 472, 467, 506], [114, 44, 291, 448], [84, 209, 93, 253]], ![[418, 354, 318, 56], [82, 215, 362, 490], [120, 112, 108, 253], [359, 165, 306, 254], [28, 154, 513, 144], [282, 77, 438, 446], [182, 475, 294, 226], [499, 33, 199, 337], [494, 176, 343, 209], [432, 482, 112, 214]], ![[0, 1], [50, 383, 342, 369], [306, 220, 163, 175], [476, 161, 362, 325], [506, 449, 135, 517], [112, 414, 387, 104], [121, 412, 43, 66], [0, 357, 36, 315], [72, 303, 411, 389], [418, 354, 318, 56]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [99, 72, 43], []]
 b := ![[], [], [483, 261, 135, 100], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI523N0 : CertifiedPrimeIdeal' SI523N0 523 where
  n := 4
  hpos := by decide
  P := [407, 339, 179, 112, 1]
  hirr := P523P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1090469532558, -357036689163, -717059417765, 107491927456, -1105558805383]
  a := ![-23, 53, 49, 28, 147]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![255750528066, 891374338781, 833611221240, 554041871774, -1105558805383]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI523N0 : Ideal.IsPrime I523N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI523N0 B_one_repr
lemma NI523N0 : Nat.card (O ⧸ I523N0) = 74818113841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI523N0

def I523N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-44, 1, 21, -5, 19]] i)))

def SI523N1: IdealEqSpanCertificate' Table ![![-44, 1, 21, -5, 19]] 
 ![![523, 0, 0, 0, 0], ![510, 1, 0, 0, 0], ![354, 0, 1, 0, 0], ![477, 0, 0, 1, 0], ![118, 0, 0, 0, 1]] where
  M :=![![![-44, 1, 21, -5, 19], ![-84, -164, -59, -26, -304], ![1980, 735, -476, 334, 836], ![-3468, 1333, 2401, -297, 3990], ![-639, -936, -264, -181, -1714]]]
  hmulB := by decide  
  f := ![![![-43508, -30133, 18829, 6609, 29431]], ![![-42840, -29492, 18455, 6480, 28842]], ![![-30516, -20827, 13060, 4588, 20406]], ![![-41274, -28030, 17598, 6184, 27493]], ![![-9227, -6594, 4090, 1433, 6398]]]
  g := ![![![-15, 1, 21, -5, 19], ![292, -164, -59, -26, -304], ![-884, 735, -476, 334, 836], ![-3561, 1333, 2401, -297, 3990], ![1642, -936, -264, -181, -1714]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI523N1 : Nat.card (O ⧸ I523N1) = 523 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI523N1)

lemma isPrimeI523N1 : Ideal.IsPrime I523N1 := prime_ideal_of_norm_prime hp523.out _ NI523N1
def MulI523N0 : IdealMulLeCertificate' Table 
  ![![43508, 30133, -18829, -6609, -29431]] ![![-44, 1, 21, -5, 19]]
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


lemma PB1705I10_primes (p : ℕ) :
  p ∈ Set.range ![467, 479, 487, 491, 499, 503, 509, 521, 523] ↔ Nat.Prime p ∧ 463 < p ∧ p ≤ 523 := by
  rw [← List.mem_ofFn']
  convert primes_range 463 523 (by omega)

def PB1705I10 : PrimesBelowBoundCertificateInterval O 463 523 1705 where
  m := 9
  g := ![3, 4, 2, 2, 3, 3, 2, 2, 2]
  P := ![467, 479, 487, 491, 499, 503, 509, 521, 523]
  hP := PB1705I10_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I467N0, I467N1, I467N2]
    · exact ![I479N0, I479N1, I479N2, I479N3]
    · exact ![I487N0, I487N1]
    · exact ![I491N0, I491N1]
    · exact ![I499N0, I499N1, I499N2]
    · exact ![I503N0, I503N1, I503N2]
    · exact ![I509N0, I509N1]
    · exact ![I521N0, I521N1]
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
    · exact ![218089, 218089, 467]
    · exact ![229441, 479, 479, 479]
    · exact ![56249134561, 487]
    · exact ![58120048561, 491]
    · exact ![124251499, 499, 499]
    · exact ![253009, 253009, 503]
    · exact ![67122964561, 509]
    · exact ![73680216481, 521]
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
    · dsimp ; intro j
      fin_cases j
      exact NI479N0
      exact NI479N1
      exact NI479N2
      exact NI479N3
    · dsimp ; intro j
      fin_cases j
      exact NI487N0
      exact NI487N1
    · dsimp ; intro j
      fin_cases j
      exact NI491N0
      exact NI491N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI523N0
      exact NI523N1
  β := ![I467N2, I479N1, I479N2, I479N3, I487N1, I491N1, I499N1, I499N2, I503N2, I509N1, I521N1, I523N1]
  Il := ![[I467N2], [I479N1, I479N2, I479N3], [I487N1], [I491N1], [I499N1, I499N2], [I503N2], [I509N1], [I521N1], [I523N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
