
import IdealArithmetic.Examples.NF5_3_2025000000_1.RI5_3_2025000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp541 : Fact (Nat.Prime 541) := {out := by norm_num}

def I541N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-161, -432, -158, 24, 258]] i)))

def SI541N0: IdealEqSpanCertificate' Table ![![-161, -432, -158, 24, 258]] 
 ![![541, 0, 0, 0, 0], ![0, 541, 0, 0, 0], ![355, 439, 1, 0, 0], ![504, 230, 0, 1, 0], ![302, 229, 0, 0, 1]] where
  M :=![![![-161, -432, -158, 24, 258], ![180, 679, 318, -62, -216], ![436, -188, 93, 70, -1244], ![-3468, -5100, -3990, 373, 7356], ![676, 1252, 970, -120, -1339]]]
  hmulB := by decide  
  f := ![![![102707, 108928, 18214, -4364, -38678]], ![![-16260, -17093, -2742, 758, 6336]], ![![54205, 57613, 9729, -2248, -20238]], ![![88764, 94214, 15810, -3739, -33324]], ![![50522, 53647, 9020, -2118, -18935]]]
  g := ![![![-63, 8, -158, 24, 258], ![-30, -139, 318, -62, -216], ![569, 421, 93, 70, -1244], ![-1842, -44, -3990, 373, 7356], ![224, -167, 970, -120, -1339]]]
  hle1 := by decide   
  hle2 := by decide  


def P541P0 : CertificateIrreducibleZModOfList' 541 2 2 9 [344, 68, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [473, 540], [0, 1]]
 g := ![![[472, 359], [513], [329, 304], [170, 205], [358, 475], [290], [510], [296], [1]], ![[405, 182], [513], [215, 237], [296, 336], [518, 66], [290], [510], [296], [1]]]
 h' := ![![[473, 540], [523, 511], [434, 186], [489, 157], [196, 105], [179, 61], [382, 79], [282, 147], [197, 473], [0, 1]], ![[0, 1], [399, 30], [229, 355], [92, 384], [89, 436], [359, 480], [420, 462], [24, 394], [493, 68], [473, 540]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [539]]
 b := ![[], [507, 540]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI541N0 : CertifiedPrimeIdeal' SI541N0 541 where
  n := 2
  hpos := by decide
  P := [344, 68, 1]
  hirr := P541P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-24183, 40586, 64391, 28077, 78319]
  a := ![35, 19, 2, -11, -85]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-112174, -97264, 64391, 28077, 78319]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI541N0 : Ideal.IsPrime I541N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI541N0 B_one_repr
lemma NI541N0 : Nat.card (O ⧸ I541N0) = 292681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI541N0

def I541N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![805067, 853728, 142442, -34400, -303890]] i)))

def SI541N1: IdealEqSpanCertificate' Table ![![805067, 853728, 142442, -34400, -303890]] 
 ![![541, 0, 0, 0, 0], ![0, 541, 0, 0, 0], ![435, 75, 1, 0, 0], ![376, 220, 0, 1, 0], ![479, 377, 0, 0, 1]] where
  M :=![![![805067, 853728, 142442, -34400, -303890], ![-126180, -135293, -23542, 4842, 45960], ![24132, 18924, -2255, -4174, -19212], ![20012, -19324, -34538, -18951, -65068], ![304140, 319924, 51358, -14164, -118523]]]
  hmulB := by decide  
  f := ![![![58663, 211024, 147118, -26948, -77634]], ![![222004, -36289, 5070, 39326, -605696]], ![![74689, 159997, 115497, -15916, -139442]], ![![140748, 154048, 120210, -5035, -317860]], ![![205461, 157711, 131098, 4018, -489097]]]
  g := ![![![179927, 207588, 142442, -34400, -303890], ![-25362, -30983, -23542, 4842, 45960], ![21769, 15433, -2255, -4174, -19212], ![98590, 57802, -34538, -18951, -65068], ![74051, 81825, 51358, -14164, -118523]]]
  hle1 := by decide   
  hle2 := by decide  


def P541P1 : CertificateIrreducibleZModOfList' 541 2 2 9 [116, 266, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [275, 540], [0, 1]]
 g := ![![[478, 441], [74], [254, 309], [44, 142], [460, 312], [45], [401], [426], [1]], ![[28, 100], [74], [292, 232], [142, 399], [241, 229], [45], [401], [426], [1]]]
 h' := ![![[275, 540], [357, 21], [291, 507], [306, 64], [199, 356], [159, 225], [147, 47], [287, 332], [425, 275], [0, 1]], ![[0, 1], [181, 520], [138, 34], [53, 477], [178, 185], [360, 316], [88, 494], [158, 209], [310, 266], [275, 540]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [114]]
 b := ![[], [7, 57]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI541N1 : CertifiedPrimeIdeal' SI541N1 541 where
  n := 2
  hpos := by decide
  P := [116, 266, 1]
  hirr := P541P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-23935, -21068, 17516, 14346, 61638]
  a := ![-27, -79, -1, 8, 66]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-78673, -51254, 17516, 14346, 61638]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI541N1 : Ideal.IsPrime I541N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI541N1 B_one_repr
lemma NI541N1 : Nat.card (O ⧸ I541N1) = 292681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI541N1

def I541N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-119, -176, -132, 12, 252]] i)))

def SI541N2: IdealEqSpanCertificate' Table ![![-119, -176, -132, 12, 252]] 
 ![![541, 0, 0, 0, 0], ![27, 1, 0, 0, 0], ![353, 0, 1, 0, 0], ![207, 0, 0, 1, 0], ![114, 0, 0, 0, 1]] where
  M :=![![![-119, -176, -132, 12, 252], ![336, 793, 568, -84, -600], ![-24, -1392, -923, 232, -456], ![-4160, -3704, -2992, 5, 9712], ![1088, 1528, 1152, -96, -2331]]]
  hmulB := by decide  
  f := ![![![29525, 82992, 14724, -2988, -33500]], ![![1427, 3993, 708, -144, -1612]], ![![19313, 54304, 9633, -1956, -21924]], ![![11255, 31592, 5596, -1143, -12772]], ![![6242, 17544, 3112, -632, -7083]]]
  g := ![![![37, -176, -132, 12, 252], ![-251, 793, 568, -84, -600], ![679, -1392, -923, 232, -456], ![81, -3704, -2992, 5, 9712], ![-298, 1528, 1152, -96, -2331]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI541N2 : Nat.card (O ⧸ I541N2) = 541 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI541N2)

lemma isPrimeI541N2 : Ideal.IsPrime I541N2 := prime_ideal_of_norm_prime hp541.out _ NI541N2
def MulI541N0 : IdealMulLeCertificate' Table 
  ![![-161, -432, -158, 24, 258]] ![![805067, 853728, 142442, -34400, -303890]]
  ![![29525, 82992, 14724, -2988, -33500]] where
 M := ![![![29525, 82992, 14724, -2988, -33500]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI541N1 : IdealMulLeCertificate' Table 
  ![![29525, 82992, 14724, -2988, -33500]] ![![-119, -176, -132, 12, 252]]
  ![![541, 0, 0, 0, 0]] where
 M := ![![![541, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC541 : ContainsPrimesAboveP 541 ![I541N0, I541N1, I541N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI541N0
    exact isPrimeI541N1
    exact isPrimeI541N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 541 (by decide) (𝕀 ⊙ MulI541N0 ⊙ MulI541N1)
instance hp547 : Fact (Nat.Prime 547) := {out := by norm_num}

def I547N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-99656443, -145783761, -109372863, 9778490, 211346148]] i)))

def SI547N0: IdealEqSpanCertificate' Table ![![-99656443, -145783761, -109372863, 9778490, 211346148]] 
 ![![547, 0, 0, 0, 0], ![0, 547, 0, 0, 0], ![0, 0, 547, 0, 0], ![0, 0, 0, 547, 0], ![354, 79, 447, 157, 1]] where
  M :=![![![-99656443, -145783761, -109372863, 9778490, 211346148], ![285793436, 667500229, 478476193, -70258903, -512915932], ![-42207222, -1203799068, -800988664, 197440581, -337138974], ![-3438446082, -2970287766, -2412656571, -11226340, 8061535650], ![908322778, 1260996718, 952110959, -77658481, -1951635327]]]
  hmulB := by decide  
  f := ![![![-31156687, -101956419, -18211017, 3614092, 41495970]], ![![32394652, 105914457, 18917399, -3754649, -43104752]], ![![-33644418, -109987164, -19645150, 3898803, 44760942]], ![![34938642, 114208926, 20396859, -4049938, -46484466]], ![![-32971392, -107853769, -19264989, 3822697, 43893101]]]
  g := ![![![-136958305, -30789999, -172908777, -60642718, 211346148], ![332464412, 75297731, 420021751, 147088743, -512915932], ![218107842, 46490274, 274040462, 97126617, -337138974], ![-5223440706, -1169710428, -6592173843, -2313843370, 8061535650], ![1264693288, 284168533, 1596587024, 560016614, -1951635327]]]
  hle1 := by decide   
  hle2 := by decide  


def P547P0 : CertificateIrreducibleZModOfList' 547 4 2 9 [283, 128, 494, 397, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [133, 404, 45, 428], [343, 383, 210, 486], [221, 306, 292, 180], [0, 1]]
 g := ![![[533, 194, 410, 360], [389, 291, 40, 435], [485, 168, 273], [264, 440, 395], [133, 119, 9], [55, 52, 304, 273], [490, 47, 73], [1], []], ![[258, 395, 513, 160, 118, 366], [529, 54, 483, 99, 343, 421], [262, 199, 35], [120, 540, 458], [285, 480, 74], [22, 446, 201, 151, 382, 513], [500, 342, 73], [352, 475, 464], [515, 379, 486]], ![[292, 142, 407, 423, 109, 400], [474, 285, 480, 532, 328, 131], [91, 288, 165], [373, 72, 209], [4, 321, 76], [385, 144, 195, 425, 2, 115], [534, 81, 100], [190, 264, 484], [398, 299, 439]], ![[11, 355, 428, 48, 317, 281], [444, 128, 88, 334, 446, 23], [47, 506, 110], [444, 367, 504], [19, 64, 189], [488, 170, 309, 211, 470, 72], [151, 426, 100], [161, 271, 249], [462, 1, 127]]]
 h' := ![![[133, 404, 45, 428], [407, 172, 258, 123], [417, 327, 113, 394], [237, 487, 111, 452], [294, 351, 223, 214], [298, 93, 114, 544], [495, 256, 450, 452], [264, 419, 53, 150], [0, 0, 1], [0, 1]], ![[343, 383, 210, 486], [400, 263, 160, 279], [496, 307, 36, 101], [376, 213, 380, 305], [382, 350, 354, 460], [538, 314, 292, 53], [26, 294, 386, 173], [20, 198, 101, 397], [489, 474, 21, 451], [133, 404, 45, 428]], ![[221, 306, 292, 180], [385, 296, 374, 230], [161, 120, 140, 129], [321, 26, 161, 240], [422, 95, 38, 265], [303, 456, 417, 91], [123, 271, 257, 309], [95, 430, 266, 10], [92, 273, 3, 525], [343, 383, 210, 486]], ![[0, 1], [149, 363, 302, 462], [176, 340, 258, 470], [389, 368, 442, 97], [418, 298, 479, 155], [83, 231, 271, 406], [392, 273, 1, 160], [77, 47, 127, 537], [145, 347, 522, 118], [221, 306, 292, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [370, 418, 51], []]
 b := ![[], [], [280, 119, 268, 503], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI547N0 : CertifiedPrimeIdeal' SI547N0 547 where
  n := 4
  hpos := by decide
  P := [283, 128, 494, 397, 1]
  hirr := P547P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3347654361, 2409244940, 5050467406, 2772899864, 9610235714]
  a := ![12, 4, 1, -4, -29]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6225541311, -1383545478, -7844104016, -2753261622, 9610235714]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI547N0 : Ideal.IsPrime I547N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI547N0 B_one_repr
lemma NI547N0 : Nat.card (O ⧸ I547N0) = 89526025681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI547N0

def I547N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-31156687, -101956419, -18211017, 3614092, 41495970]] i)))

def SI547N1: IdealEqSpanCertificate' Table ![![-31156687, -101956419, -18211017, 3614092, 41495970]] 
 ![![547, 0, 0, 0, 0], ![136, 1, 0, 0, 0], ![102, 0, 1, 0, 0], ![350, 0, 0, 1, 0], ![524, 0, 0, 0, 1]] where
  M :=![![![-31156687, -101956419, -18211017, 3614092, 41495970], ![32394652, 105914457, 18917399, -3754649, -43104752], ![-33644418, -109987164, -19645150, 3898803, 44760942], ![34938642, 114208926, 20396859, -4049938, -46484466], ![-11373682, -37220494, -6648299, 1319287, 15148363]]]
  hmulB := by decide  
  f := ![![![-99656443, -145783761, -109372863, 9778490, 211346148]], ![![-24254996, -35025761, -26318525, 2302771, 51609068]], ![![-18660264, -29385270, -21859270, 2184363, 38793726]], ![![-70051556, -98710428, -74393343, 6236280, 149968350]], ![![-93805582, -137348618, -103033399, 9225357, 198891675]]]
  g := ![![![-13375467, -101956419, -18211017, 3614092, 41495970], ![13893000, 105914457, 18917399, -3754649, -43104752], ![-14425776, -109987164, -19645150, 3898803, 44760942], ![14986076, 114208926, 20396859, -4049938, -46484466], ![-4882546, -37220494, -6648299, 1319287, 15148363]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI547N1 : Nat.card (O ⧸ I547N1) = 547 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI547N1)

lemma isPrimeI547N1 : Ideal.IsPrime I547N1 := prime_ideal_of_norm_prime hp547.out _ NI547N1
def MulI547N0 : IdealMulLeCertificate' Table 
  ![![-99656443, -145783761, -109372863, 9778490, 211346148]] ![![-31156687, -101956419, -18211017, 3614092, 41495970]]
  ![![547, 0, 0, 0, 0]] where
 M := ![![![547, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC547 : ContainsPrimesAboveP 547 ![I547N0, I547N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI547N0
    exact isPrimeI547N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 547 (by decide) (𝕀 ⊙ MulI547N0)
instance hp557 : Fact (Nat.Prime 557) := {out := by norm_num}

def I557N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14943, 15830, 2644, -636, -5626]] i)))

def SI557N0: IdealEqSpanCertificate' Table ![![14943, 15830, 2644, -636, -5626]] 
 ![![557, 0, 0, 0, 0], ![0, 557, 0, 0, 0], ![61, 444, 1, 0, 0], ![209, 103, 0, 1, 0], ![349, 513, 0, 0, 1]] where
  M :=![![![14943, 15830, 2644, -636, -5626], ![-2348, -2473, -412, 100, 880], ![360, 372, 67, -12, -120], ![-72, -24, 24, 19, 72], ![5616, 5952, 996, -238, -2111]]]
  hmulB := by decide  
  f := ![![![91, 50, 76, 0, -226]], ![![-452, -813, -628, 76, 904]], ![![-349, -638, -489, 60, 694]], ![![-45, -133, -88, 15, 70]], ![![-361, -719, -532, 70, 695]]]
  g := ![![![3501, 3220, 2644, -636, -5626], ![-548, -505, -412, 100, 880], ![73, 60, 67, -12, -120], ![-55, -89, 24, 19, 72], ![1313, 1205, 996, -238, -2111]]]
  hle1 := by decide   
  hle2 := by decide  


def P557P0 : CertificateIrreducibleZModOfList' 557 2 2 9 [75, 498, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [59, 556], [0, 1]]
 g := ![![[274, 7], [404], [113, 297], [145, 341], [285], [144, 378], [109], [139], [1]], ![[130, 550], [404], [369, 260], [212, 216], [285], [166, 179], [109], [139], [1]]]
 h' := ![![[59, 556], [253, 243], [437, 31], [265, 356], [92, 176], [340, 227], [432, 102], [213, 465], [482, 59], [0, 1]], ![[0, 1], [108, 314], [38, 526], [103, 201], [450, 381], [365, 330], [323, 455], [355, 92], [64, 498], [59, 556]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45]]
 b := ![[], [311, 301]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI557N0 : CertifiedPrimeIdeal' SI557N0 557 where
  n := 2
  hpos := by decide
  P := [75, 498, 1]
  hirr := P557P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-64072, 81080, 127843, 59692, 192922]
  a := ![-51, -10, -3, 14, 124]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-157393, -290482, 127843, 59692, 192922]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI557N0 : Ideal.IsPrime I557N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI557N0 B_one_repr
lemma NI557N0 : Nat.card (O ⧸ I557N0) = 310249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI557N0

def I557N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![106781, 349057, 62345, -12374, -142056]] i)))

def SI557N1: IdealEqSpanCertificate' Table ![![106781, 349057, 62345, -12374, -142056]] 
 ![![557, 0, 0, 0, 0], ![0, 557, 0, 0, 0], ![406, 126, 1, 0, 0], ![88, 126, 0, 1, 0], ![528, 540, 0, 0, 1]] where
  M :=![![![106781, 349057, 62345, -12374, -142056], ![-110876, -362451, -64737, 12849, 147508], ![115130, 376364, 67224, -13341, -153166], ![-119558, -390806, -69793, 13860, 159070], ![38982, 127430, 22761, -4517, -51859]]]
  hmulB := by decide  
  f := ![![![383, 581, 269, -44, -326]], ![![-36, -569, -353, 93, -192]], ![![268, 292, 114, -11, -274]], ![![66, -12, -19, 12, -122]], ![![326, -6, -91, 49, -491]]]
  g := ![![![91363, 127043, 62345, -12374, -142056], ![-94870, -131919, -64737, 12849, 147508], ![98506, 136978, 67224, -13341, -153166], ![-102320, -142264, -69793, 13860, 159070], ![33352, 46378, 22761, -4517, -51859]]]
  hle1 := by decide   
  hle2 := by decide  


def P557P1 : CertificateIrreducibleZModOfList' 557 2 2 9 [264, 520, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 556], [0, 1]]
 g := ![![[137, 402], [494], [505, 135], [488, 487], [389], [105, 515], [55], [255], [1]], ![[529, 155], [494], [487, 422], [126, 70], [389], [222, 42], [55], [255], [1]]]
 h' := ![![[37, 556], [298, 122], [360, 244], [392, 98], [539, 193], [130, 331], [143, 444], [148, 482], [293, 37], [0, 1]], ![[0, 1], [356, 435], [476, 313], [119, 459], [439, 364], [123, 226], [418, 113], [158, 75], [548, 520], [37, 556]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [347]]
 b := ![[], [550, 452]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI557N1 : CertifiedPrimeIdeal' SI557N1 557 where
  n := 2
  hpos := by decide
  P := [264, 520, 1]
  hirr := P557P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-21715, 134658, 181287, 66900, 103572]
  a := ![65, 37, 5, -17, -158]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-240929, -156312, 181287, 66900, 103572]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI557N1 : Ideal.IsPrime I557N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI557N1 B_one_repr
lemma NI557N1 : Nat.card (O ⧸ I557N1) = 310249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI557N1

def I557N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1193, -1668, -1258, 104, 2558]] i)))

def SI557N2: IdealEqSpanCertificate' Table ![![-1193, -1668, -1258, 104, 2558]] 
 ![![557, 0, 0, 0, 0], ![544, 1, 0, 0, 0], ![388, 0, 1, 0, 0], ![31, 0, 0, 1, 0], ![524, 0, 0, 0, 1]] where
  M :=![![![-1193, -1668, -1258, 104, 2558], ![3660, 8207, 5902, -842, -6696], ![-1604, -16388, -11039, 2534, -1844], ![-39164, -29252, -24454, -903, 93532], ![10804, 14268, 10842, -800, -23487]]]
  hmulB := by decide  
  f := ![![![96683, 326084, 59842, -10556, -129170]], ![![94228, 317871, 58354, -10278, -125872]], ![![67472, 227828, 41901, -7318, -90036]], ![![4773, 17760, 3804, -231, -5762]], ![![90992, 306996, 56374, -9916, -121527]]]
  g := ![![![91, -1668, -1258, 104, 2558], ![-5774, 8207, 5902, -842, -6696], ![25286, -16388, -11039, 2534, -1844], ![-42407, -29252, -24454, -903, 93532], ![672, 14268, 10842, -800, -23487]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI557N2 : Nat.card (O ⧸ I557N2) = 557 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI557N2)

lemma isPrimeI557N2 : Ideal.IsPrime I557N2 := prime_ideal_of_norm_prime hp557.out _ NI557N2
def MulI557N0 : IdealMulLeCertificate' Table 
  ![![14943, 15830, 2644, -636, -5626]] ![![106781, 349057, 62345, -12374, -142056]]
  ![![1591279, 5097273, 909843, -180934, -2071858]] where
 M := ![![![1591279, 5097273, 909843, -180934, -2071858]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI557N1 : IdealMulLeCertificate' Table 
  ![![1591279, 5097273, 909843, -180934, -2071858]] ![![-1193, -1668, -1258, 104, 2558]]
  ![![557, 0, 0, 0, 0]] where
 M := ![![![-19495, -29521, -5013, 1114, 11140]]]
 hmul := by decide  
 g := ![![![![-35, -53, -9, 2, 20]]]]
 hle2 := by decide  


def PBC557 : ContainsPrimesAboveP 557 ![I557N0, I557N1, I557N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI557N0
    exact isPrimeI557N1
    exact isPrimeI557N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 557 (by decide) (𝕀 ⊙ MulI557N0 ⊙ MulI557N1)
instance hp563 : Fact (Nat.Prime 563) := {out := by norm_num}

def I563N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-86579, -91805, -15335, 3688, 32634]] i)))

def SI563N0: IdealEqSpanCertificate' Table ![![-86579, -91805, -15335, 3688, 32634]] 
 ![![563, 0, 0, 0, 0], ![0, 563, 0, 0, 0], ![0, 0, 563, 0, 0], ![50, 449, 287, 1, 0], ![234, 149, 289, 0, 1]] where
  M :=![![![-86579, -91805, -15335, 3688, 32634], ![13636, 14453, 2409, -583, -5144], ![-2126, -2276, -396, 77, 754], ![430, 274, -91, -88, -398], ![-32542, -34514, -5773, 1381, 12255]]]
  hmulB := by decide  
  f := ![![![505, 1641, 295, -58, -676]], ![![-540, -1735, -329, 63, 732]], ![![582, 1884, 398, -77, -786]], ![![-90, -281, -34, 6, 124]], ![![366, 1191, 240, -47, -491]]]
  g := ![![![-14045, -11741, -18659, 3688, 32634], ![2214, 1852, 2942, -583, -5144], ![-324, -265, -427, 77, 754], ![174, 176, 249, -88, -398], ![-5274, -4406, -7005, 1381, 12255]]]
  hle1 := by decide   
  hle2 := by decide  


def P563P0 : CertificateIrreducibleZModOfList' 563 3 2 9 [291, 409, 469, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 542, 226], [79, 20, 337], [0, 1]]
 g := ![![[354, 57, 121], [86, 149, 280], [500, 365], [188, 360], [43, 304, 33], [397, 195, 99], [35, 324], [94, 1], []], ![[506, 43, 340, 261], [393, 462, 65, 34], [159, 470], [269, 484], [434, 182, 351, 140], [402, 18, 217, 538], [443, 231], [223, 400], [522, 406]], ![[52, 561, 445, 108], [345, 306, 422, 280], [523, 210], [206, 258], [347, 61, 172, 208], [439, 461, 91, 537], [263, 213], [491, 441], [411, 406]]]
 h' := ![![[15, 542, 226], [309, 23, 11], [77, 441, 308], [268, 257, 127], [436, 514, 217], [451, 520, 98], [190, 87, 35], [233, 110, 545], [0, 0, 1], [0, 1]], ![[79, 20, 337], [376, 62, 351], [34, 369, 545], [248, 537, 381], [461, 418, 22], [349, 282, 124], [201, 163, 94], [393, 125, 291], [333, 459, 20], [15, 542, 226]], ![[0, 1], [522, 478, 201], [138, 316, 273], [56, 332, 55], [545, 194, 324], [268, 324, 341], [168, 313, 434], [83, 328, 290], [366, 104, 542], [79, 20, 337]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [506, 280], []]
 b := ![[], [130, 404, 213], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI563N0 : CertifiedPrimeIdeal' SI563N0 563 where
  n := 3
  hpos := by decide
  P := [291, 409, 469, 1]
  hirr := P563P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-21096275, 18838072, 28373346, 11197134, 62256754]
  a := ![-42, -24, -2, 2, 102]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-26907697, -25372880, -37615286, 11197134, 62256754]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI563N0 : Ideal.IsPrime I563N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI563N0 B_one_repr
lemma NI563N0 : Nat.card (O ⧸ I563N0) = 178453547 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI563N0

def I563N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![505, 1641, 295, -58, -676]] i)))

def SI563N1: IdealEqSpanCertificate' Table ![![505, 1641, 295, -58, -676]] 
 ![![563, 0, 0, 0, 0], ![0, 563, 0, 0, 0], ![270, 276, 1, 0, 0], ![359, 99, 0, 1, 0], ![272, 147, 0, 0, 1]] where
  M :=![![![505, 1641, 295, -58, -676], ![-540, -1735, -329, 63, 732], ![582, 1884, 398, -77, -786], ![-494, -1946, -397, 90, 526], ![150, 578, 89, -23, -163]]]
  hmulB := by decide  
  f := ![![![-86579, -91805, -15335, 3688, 32634]], ![![13636, 14453, 2409, -583, -5144]], ![![-34840, -36946, -6174, 1483, 13130]], ![![-52809, -55998, -9355, 2249, 19904]], ![![-38326, -40641, -6790, 1632, 14445]]]
  g := ![![![223, 45, 295, -58, -676], ![-237, -44, -329, 63, 732], ![239, 27, 398, -77, -786], ![-122, 38, -397, 90, 526], ![51, 4, 89, -23, -163]]]
  hle1 := by decide   
  hle2 := by decide  


def P563P1 : CertificateIrreducibleZModOfList' 563 2 2 9 [122, 382, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [181, 562], [0, 1]]
 g := ![![[400, 258], [325, 19], [467], [82], [85, 503], [289, 439], [62], [107], [1]], ![[369, 305], [386, 544], [467], [82], [485, 60], [365, 124], [62], [107], [1]]]
 h' := ![![[181, 562], [323, 324], [491, 92], [89, 212], [327, 229], [211, 134], [494, 231], [141, 538], [441, 181], [0, 1]], ![[0, 1], [415, 239], [253, 471], [177, 351], [114, 334], [256, 429], [80, 332], [120, 25], [548, 382], [181, 562]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [365]]
 b := ![[], [233, 464]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI563N1 : CertifiedPrimeIdeal' SI563N1 563 where
  n := 2
  hpos := by decide
  P := [122, 382, 1]
  hirr := P563P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![15477, 5864, 3728, 1796, -38012]
  a := ![23, 14, 4, 0, -54]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![15459, 7792, 3728, 1796, -38012]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI563N1 : Ideal.IsPrime I563N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI563N1 B_one_repr
lemma NI563N1 : Nat.card (O ⧸ I563N1) = 316969 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI563N1
def MulI563N0 : IdealMulLeCertificate' Table 
  ![![-86579, -91805, -15335, 3688, 32634]] ![![505, 1641, 295, -58, -676]]
  ![![563, 0, 0, 0, 0]] where
 M := ![![![563, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC563 : ContainsPrimesAboveP 563 ![I563N0, I563N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI563N0
    exact isPrimeI563N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 563 (by decide) (𝕀 ⊙ MulI563N0)
instance hp569 : Fact (Nat.Prime 569) := {out := by norm_num}

def I569N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73507, 204025, 36214, -7331, -82198]] i)))

def SI569N0: IdealEqSpanCertificate' Table ![![73507, 204025, 36214, -7331, -82198]] 
 ![![569, 0, 0, 0, 0], ![0, 569, 0, 0, 0], ![0, 0, 569, 0, 0], ![238, 45, 523, 1, 0], ![394, 464, 480, 0, 1]] where
  M :=![![![73507, 204025, 36214, -7331, -82198], ![-61762, -196637, -35238, 6890, 79538], ![62616, 201270, 35087, -7678, -83892], ![-60292, -211528, -42728, 4375, 74516], ![27252, 74512, 12904, -2880, -30757]]]
  hmulB := by decide  
  f := ![![![-5235, -13007, -9280, 1419, 9104]], ![![-1658, 19829, 12886, -3604, 11830]], ![![74116, 74494, 58923, -1530, -169856]], ![![65244, 63557, 50535, -1005, -150278]], ![![57638, 70222, 53944, -3270, -127501]]]
  g := ![![![60113, 67968, 76143, -7331, -82198], ![-58066, -65751, -73492, 6890, 79538], ![61412, 69372, 77889, -7678, -83892], ![-53534, -61483, -66957, 4375, 74516], ![22550, 25440, 28616, -2880, -30757]]]
  hle1 := by decide   
  hle2 := by decide  


def P569P0 : CertificateIrreducibleZModOfList' 569 3 2 9 [189, 123, 34, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [243, 44, 159], [292, 524, 410], [0, 1]]
 g := ![![[80, 216, 468], [454, 238], [387, 285], [50, 66, 208], [484, 398, 242], [34, 343, 238], [297, 214], [535, 1], []], ![[446, 92, 202, 242], [452, 512], [437, 497], [253, 87, 375, 241], [74, 279, 539, 98], [479, 535, 517, 34], [218, 291], [36, 318], [541, 245]], ![[345, 77, 385, 180], [419, 425], [9, 107], [45, 193, 214, 26], [238, 375, 134, 98], [509, 58, 95, 26], [147, 125], [507, 229], [290, 245]]]
 h' := ![![[243, 44, 159], [510, 433, 175], [484, 452, 265], [223, 203, 385], [133, 107, 496], [402, 170, 504], [206, 333, 304], [167, 10, 464], [0, 0, 1], [0, 1]], ![[292, 524, 410], [198, 45, 89], [214, 275, 198], [488, 460, 158], [162, 382, 383], [160, 331, 367], [47, 125, 6], [253, 9, 56], [44, 145, 524], [243, 44, 159]], ![[0, 1], [255, 91, 305], [74, 411, 106], [299, 475, 26], [23, 80, 259], [11, 68, 267], [529, 111, 259], [352, 550, 49], [297, 424, 44], [292, 524, 410]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [202, 296], []]
 b := ![[], [63, 401, 356], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI569N0 : CertifiedPrimeIdeal' SI569N0 569 where
  n := 3
  hpos := by decide
  P := [189, 123, 34, 1]
  hirr := P569P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8526065, 4262096, 10530346, 6343286, 23838116]
  a := ![-19, -14, -1, 4, 46]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-19174773, -19933342, -25921448, 6343286, 23838116]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI569N0 : Ideal.IsPrime I569N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI569N0 B_one_repr
lemma NI569N0 : Nat.card (O ⧸ I569N0) = 184220009 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI569N0

def I569N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 64, 11, -1, -48]] i)))

def SI569N1: IdealEqSpanCertificate' Table ![![71, 64, 11, -1, -48]] 
 ![![569, 0, 0, 0, 0], ![78, 1, 0, 0, 0], ![175, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![427, 0, 0, 0, 1]] where
  M :=![![![71, 64, 11, -1, -48], ![-82, -113, -79, 7, 158], ![218, 494, 354, -51, -394], ![-74, -950, -637, 150, -158], ![-46, 70, 25, -19, 193]]]
  hmulB := by decide  
  f := ![![![-611573, -1999244, -357075, 70879, 813660]], ![![-82720, -270413, -48297, 9587, 110054]], ![![-189253, -618670, -110497, 21934, 251790]], ![![-5248, -17146, -3059, 610, 6986]], ![![-459341, -1501594, -268192, 53236, 611125]]]
  g := ![![![24, 64, 11, -1, -48], ![-79, -113, -79, 7, 158], ![120, 494, 354, -51, -394], ![443, -950, -637, 150, -158], ![-162, 70, 25, -19, 193]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI569N1 : Nat.card (O ⧸ I569N1) = 569 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI569N1)

lemma isPrimeI569N1 : Ideal.IsPrime I569N1 := prime_ideal_of_norm_prime hp569.out _ NI569N1

def I569N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, 23, 25, -4, -16]] i)))

def SI569N2: IdealEqSpanCertificate' Table ![![9, 23, 25, -4, -16]] 
 ![![569, 0, 0, 0, 0], ![537, 1, 0, 0, 0], ![114, 0, 1, 0, 0], ![234, 0, 0, 1, 0], ![322, 0, 0, 0, 1]] where
  M :=![![![9, 23, 25, -4, -16], ![24, -23, -21, 9, -72], ![-270, -336, -248, 15, 594], ![978, 1986, 1431, -188, -1866], ![-146, -386, -271, 43, 245]]]
  hmulB := by decide  
  f := ![![![-707201, -749929, -125255, 30134, 266618]], ![![-667233, -707546, -118176, 28431, 251550]], ![![-141720, -150282, -25100, 6039, 53430]], ![![-290832, -308400, -51507, 12394, 109650]], ![![-400676, -424884, -70965, 17073, 151057]]]
  g := ![![![-16, 23, 25, -4, -16], ![63, -23, -21, 9, -72], ![24, -336, -248, 15, 594], ![-1026, 1986, 1431, -188, -1866], ![262, -386, -271, 43, 245]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI569N2 : Nat.card (O ⧸ I569N2) = 569 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI569N2)

lemma isPrimeI569N2 : Ideal.IsPrime I569N2 := prime_ideal_of_norm_prime hp569.out _ NI569N2
def MulI569N0 : IdealMulLeCertificate' Table 
  ![![73507, 204025, 36214, -7331, -82198]] ![![71, 64, 11, -1, -48]]
  ![![707201, 749929, 125255, -30134, -266618]] where
 M := ![![![707201, 749929, 125255, -30134, -266618]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI569N1 : IdealMulLeCertificate' Table 
  ![![707201, 749929, 125255, -30134, -266618]] ![![9, 23, 25, -4, -16]]
  ![![569, 0, 0, 0, 0]] where
 M := ![![![-569, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC569 : ContainsPrimesAboveP 569 ![I569N0, I569N1, I569N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI569N0
    exact isPrimeI569N1
    exact isPrimeI569N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 569 (by decide) (𝕀 ⊙ MulI569N0 ⊙ MulI569N1)
instance hp571 : Fact (Nat.Prime 571) := {out := by norm_num}

def I571N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![399, 488, 81, -19, -178]] i)))

def SI571N0: IdealEqSpanCertificate' Table ![![399, 488, 81, -19, -178]] 
 ![![571, 0, 0, 0, 0], ![0, 571, 0, 0, 0], ![0, 0, 571, 0, 0], ![25, 213, 375, 1, 0], ![40, 414, 75, 0, 1]] where
  M :=![![![399, 488, 81, -19, -178], ![-90, -161, -27, 5, 66], ![62, 134, 32, -7, -94], ![-90, -258, -141, 4, 138], ![162, 210, 49, -11, -89]]]
  hmulB := by decide  
  f := ![![![9, 20, 5, -1, -10]], ![![-6, -23, -9, 1, 6]], ![![-2, 10, -6, -5, 10]], ![![-3, -1, -7, -3, 8]], ![![-4, -14, -7, 0, 5]]]
  g := ![![![14, 137, 36, -19, -178], ![-5, -50, -12, 5, 66], ![7, 71, 17, -7, -94], ![-10, -102, -21, 4, 138], ![7, 69, 19, -11, -89]]]
  hle1 := by decide   
  hle2 := by decide  


def P571P0 : CertificateIrreducibleZModOfList' 571 3 2 9 [312, 345, 507, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [94, 88, 7], [541, 482, 564], [0, 1]]
 g := ![![[18, 339, 214], [336, 212, 303], [321, 59], [133, 276, 244], [379, 428, 185], [353, 411, 400], [492, 561], [64, 1], []], ![[229, 57, 292, 447], [393, 374, 313, 88], [382, 204], [307, 454, 502, 548], [162, 34, 393, 307], [194, 277, 337, 343], [13, 271], [370, 498], [371, 49]], ![[19, 246, 513, 453], [449, 500, 540, 136], [387, 407], [424, 176, 510, 504], [369, 308, 390, 116], [562, 485, 166, 530], [399, 258], [508, 321], [385, 49]]]
 h' := ![![[94, 88, 7], [232, 12, 181], [482, 323, 163], [187, 221, 164], [520, 3, 108], [67, 219, 279], [384, 498, 20], [17, 448, 325], [0, 0, 1], [0, 1]], ![[541, 482, 564], [183, 80, 534], [193, 197, 316], [449, 380, 84], [65, 464, 116], [144, 565, 113], [449, 317, 564], [380, 77, 477], [432, 23, 482], [94, 88, 7]], ![[0, 1], [284, 479, 427], [482, 51, 92], [511, 541, 323], [149, 104, 347], [432, 358, 179], [386, 327, 558], [128, 46, 340], [119, 548, 88], [541, 482, 564]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [379, 32], []]
 b := ![[], [206, 505, 77], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI571N0 : CertifiedPrimeIdeal' SI571N0 571 where
  n := 3
  hpos := by decide
  P := [312, 345, 507, 1]
  hirr := P571P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-298486407, 181071816, 413108736, 238802604, 845107668]
  a := ![-55, -31, 0, 13, 134]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-70180137, -701503428, -267111984, 238802604, 845107668]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI571N0 : Ideal.IsPrime I571N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI571N0 B_one_repr
lemma NI571N0 : Nat.card (O ⧸ I571N0) = 186169411 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI571N0

def I571N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9, -20, -5, 1, 10]] i)))

def SI571N1: IdealEqSpanCertificate' Table ![![-9, -20, -5, 1, 10]] 
 ![![571, 0, 0, 0, 0], ![0, 571, 0, 0, 0], ![502, 196, 1, 0, 0], ![391, 343, 0, 1, 0], ![211, 233, 0, 0, 1]] where
  M :=![![![-9, -20, -5, 1, 10], ![6, 23, 9, -1, -6], ![2, -10, 6, 5, -10], ![-90, -78, -45, 26, 210], ![10, 22, 21, -1, -21]]]
  hmulB := by decide  
  f := ![![![-399, -488, -81, 19, 178]], ![![90, 161, 27, -5, -66]], ![![-320, -374, -62, 15, 134]], ![![-219, -237, -39, 10, 82]], ![![-111, -115, -19, 5, 39]]]
  g := ![![![0, -3, -5, 1, 10], ![-5, 0, 9, -1, -6], ![-5, -1, 6, 5, -10], ![-56, -86, -45, 26, 210], ![-10, 2, 21, -1, -21]]]
  hle1 := by decide   
  hle2 := by decide  


def P571P1 : CertificateIrreducibleZModOfList' 571 2 2 9 [271, 316, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [255, 570], [0, 1]]
 g := ![![[372, 59], [89, 31], [396], [88, 525], [134, 96], [443, 332], [374], [502], [1]], ![[0, 512], [0, 540], [396], [349, 46], [61, 475], [24, 239], [374], [502], [1]]]
 h' := ![![[255, 570], [434, 164], [287, 440], [134, 443], [230, 53], [428, 157], [569, 70], [209, 78], [300, 255], [0, 1]], ![[0, 1], [0, 407], [0, 131], [41, 128], [41, 518], [493, 414], [147, 501], [114, 493], [231, 316], [255, 570]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [208]]
 b := ![[], [444, 104]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI571N1 : CertifiedPrimeIdeal' SI571N1 571 where
  n := 2
  hpos := by decide
  P := [271, 316, 1]
  hirr := P571P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-30978, 32848, 59585, 28756, 93146]
  a := ![-37, -20, -3, 10, 90]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-106550, -75678, 59585, 28756, 93146]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI571N1 : Ideal.IsPrime I571N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI571N1 B_one_repr
lemma NI571N1 : Nat.card (O ⧸ I571N1) = 326041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI571N1
def MulI571N0 : IdealMulLeCertificate' Table 
  ![![399, 488, 81, -19, -178]] ![![-9, -20, -5, 1, 10]]
  ![![571, 0, 0, 0, 0]] where
 M := ![![![-571, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC571 : ContainsPrimesAboveP 571 ![I571N0, I571N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI571N0
    exact isPrimeI571N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 571 (by decide) (𝕀 ⊙ MulI571N0)
instance hp577 : Fact (Nat.Prime 577) := {out := by norm_num}

def I577N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2757, -2868, -446, 136, 1094]] i)))

def SI577N0: IdealEqSpanCertificate' Table ![![-2757, -2868, -446, 136, 1094]] 
 ![![577, 0, 0, 0, 0], ![0, 577, 0, 0, 0], ![555, 366, 1, 0, 0], ![551, 463, 0, 1, 0], ![64, 300, 0, 0, 1]] where
  M :=![![![-2757, -2868, -446, 136, 1094], ![284, 531, 278, 98, 248], ![-876, 492, 1177, 670, 2340], ![-4700, 3124, 6842, 3857, 13420], ![-1340, -876, 274, 300, 1277]]]
  hmulB := by decide  
  f := ![![![835, 1412, 1006, -108, -1698]], ![![-1884, -5093, -3574, 574, 3120]], ![![-395, -1862, -1293, 258, 358]], ![![-659, -2675, -1858, 355, 758]], ![![-900, -2512, -1762, 288, 1461]]]
  g := ![![![173, -400, -446, 136, 1094], ![-388, -383, 278, 98, 248], ![-2033, -2500, 1177, 670, 2340], ![-11761, -14407, 6842, 3857, 13420], ![-694, -1080, 274, 300, 1277]]]
  hle1 := by decide   
  hle2 := by decide  


def P577P0 : CertificateIrreducibleZModOfList' 577 2 2 9 [78, 260, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [317, 576], [0, 1]]
 g := ![![[388, 426], [426], [184], [427], [479], [152], [42, 193], [91], [1]], ![[412, 151], [426], [184], [427], [479], [152], [61, 384], [91], [1]]]
 h' := ![![[317, 576], [88, 225], [465, 352], [101, 250], [343, 465], [237, 58], [186, 550], [140, 167], [499, 317], [0, 1]], ![[0, 1], [442, 352], [111, 225], [302, 327], [36, 112], [159, 519], [282, 27], [572, 410], [13, 260], [317, 576]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [188]]
 b := ![[], [103, 94]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI577N0 : CertifiedPrimeIdeal' SI577N0 577 where
  n := 2
  hpos := by decide
  P := [78, 260, 1]
  hirr := P577P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2233, -396, 1242, 2205, 6003]
  a := ![-1, 0, 0, 3, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3970, -5679, 1242, 2205, 6003]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI577N0 : Ideal.IsPrime I577N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI577N0 B_one_repr
lemma NI577N0 : Nat.card (O ⧸ I577N0) = 332929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI577N0

def I577N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![237, 250, 42, -10, -88]] i)))

def SI577N1: IdealEqSpanCertificate' Table ![![237, 250, 42, -10, -88]] 
 ![![577, 0, 0, 0, 0], ![0, 577, 0, 0, 0], ![101, 399, 1, 0, 0], ![91, 152, 0, 1, 0], ![304, 249, 0, 0, 1]] where
  M :=![![![237, 250, 42, -10, -88], ![-36, -35, -4, 2, 12], ![-4, -4, -1, 4, 20], ![-16, 44, 52, 15, 56], ![88, 92, 16, -2, -31]]]
  hmulB := by decide  
  f := ![![![-155, -506, -94, 18, 216]], ![![180, 565, 124, -22, -252]], ![![97, 301, 69, -12, -136]], ![![23, 70, 18, -3, -32]], ![![-4, -23, 4, 0, 5]]]
  g := ![![![41, 12, 42, -10, -88], ![-6, -3, -4, 2, 12], ![-11, -9, -1, 4, 20], ![-41, -64, 52, 15, 56], ![14, 3, 16, -2, -31]]]
  hle1 := by decide   
  hle2 := by decide  


def P577P1 : CertificateIrreducibleZModOfList' 577 2 2 9 [310, 35, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [542, 576], [0, 1]]
 g := ![![[270, 524], [453], [22], [401], [559], [23], [364, 272], [71], [1]], ![[394, 53], [453], [22], [401], [559], [23], [76, 305], [71], [1]]]
 h' := ![![[542, 576], [195, 388], [375, 284], [257, 487], [544, 322], [405, 437], [252, 394], [234, 174], [267, 542], [0, 1]], ![[0, 1], [463, 189], [244, 293], [522, 90], [237, 255], [112, 140], [310, 183], [491, 403], [338, 35], [542, 576]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [308]]
 b := ![[], [387, 154]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI577N1 : CertifiedPrimeIdeal' SI577N1 577 where
  n := 2
  hpos := by decide
  P := [310, 35, 1]
  hirr := P577P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-350212, 556487, 931136, 429119, 1108568]
  a := ![147, 87, -1, -39, -356]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-815337, -1234361, 931136, 429119, 1108568]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI577N1 : Ideal.IsPrime I577N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI577N1 B_one_repr
lemma NI577N1 : Nat.card (O ⧸ I577N1) = 332929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI577N1

def I577N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![105, 202, 168, -22, -206]] i)))

def SI577N2: IdealEqSpanCertificate' Table ![![105, 202, 168, -22, -206]] 
 ![![577, 0, 0, 0, 0], ![389, 1, 0, 0, 0], ![430, 0, 1, 0, 0], ![60, 0, 0, 1, 0], ![123, 0, 0, 0, 1]] where
  M :=![![![105, 202, 168, -22, -206], ![-104, -543, -394, 80, 76], ![-968, -440, -395, -74, 2416], ![5868, 9288, 6882, -691, -12180], ![-1132, -2248, -1626, 210, 2179]]]
  hmulB := by decide  
  f := ![![![454281, 480454, 79300, -19902, -172982]], ![![306149, 323775, 53430, -13418, -116594]], ![![338606, 358044, 59041, -14866, -129036]], ![![47472, 49800, 7902, -2263, -18660]], ![![97151, 102722, 16934, -4268, -37031]]]
  g := ![![![-215, 202, 168, -22, -206], ![635, -543, -394, 80, 76], ![82, -440, -395, -74, 2416], ![-8712, 9288, 6882, -691, -12180], ![2239, -2248, -1626, 210, 2179]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI577N2 : Nat.card (O ⧸ I577N2) = 577 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI577N2)

lemma isPrimeI577N2 : Ideal.IsPrime I577N2 := prime_ideal_of_norm_prime hp577.out _ NI577N2
def MulI577N0 : IdealMulLeCertificate' Table 
  ![![-2757, -2868, -446, 136, 1094]] ![![237, 250, 42, -10, -88]]
  ![![-454281, -480454, -79300, 19902, 172982]] where
 M := ![![![-454281, -480454, -79300, 19902, 172982]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI577N1 : IdealMulLeCertificate' Table 
  ![![-454281, -480454, -79300, 19902, 172982]] ![![105, 202, 168, -22, -206]]
  ![![577, 0, 0, 0, 0]] where
 M := ![![![-577, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC577 : ContainsPrimesAboveP 577 ![I577N0, I577N1, I577N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI577N0
    exact isPrimeI577N1
    exact isPrimeI577N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 577 (by decide) (𝕀 ⊙ MulI577N0 ⊙ MulI577N1)
instance hp587 : Fact (Nat.Prime 587) := {out := by norm_num}

def I587N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-798653, -2614510, -474174, 88118, 1046538]] i)))

def SI587N0: IdealEqSpanCertificate' Table ![![-798653, -2614510, -474174, 88118, 1046538]] 
 ![![587, 0, 0, 0, 0], ![0, 587, 0, 0, 0], ![0, 0, 587, 0, 0], ![0, 0, 0, 587, 0], ![492, 573, 338, 275, 1]] where
  M :=![![![-798653, -2614510, -474174, 88118, 1046538], ![859424, 2682555, 436986, -121702, -1190140], ![-676452, -2927520, -766163, -49822, 622692], ![1942892, 2212892, -1009622, -965451, -4184716], ![-223732, -999828, -271942, -23512, 188397]]]
  hmulB := by decide  
  f := ![![![6257, 362, 1058, 874, -16554]], ![![-45344, -66951, -50174, 4554, 95932]], ![![128108, 301952, 216291, -31958, -228892]], ![![-10372, -531796, -352766, 88459, -171004]], ![![29804, -140297, -88808, 28201, -131907]]]
  g := ![![![-878527, -1026032, -603414, -490136, 1046538], ![998992, 1166325, 686038, 557354, -1190140], ![-523068, -612828, -359857, -291806, 622692], ![3510772, 4088680, 2407878, 1958827, -4184716], ![-158288, -185607, -108944, -88301, 188397]]]
  hle1 := by decide   
  hle2 := by decide  


def P587P0 : CertificateIrreducibleZModOfList' 587 4 2 9 [341, 504, 484, 403, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [304, 472, 147, 287], [543, 528, 397, 50], [511, 173, 43, 250], [0, 1]]
 g := ![![[111, 196, 409, 179], [563, 258, 37, 409], [187, 43, 189], [316, 429, 511, 16], [312, 412, 501], [353, 381, 324], [305, 346, 9, 397], [1], []], ![[281, 542, 493, 334, 266, 45], [57, 537, 242, 454, 431, 255], [210, 325, 149], [156, 19, 494, 520, 586, 373], [14, 570, 416], [338, 40, 546], [570, 501, 326, 504, 435, 583], [241, 52, 462], [193, 580, 189]], ![[32, 2, 253, 126, 393, 200], [224, 566, 5, 63, 317, 415], [307, 276, 324], [190, 416, 435, 496, 90, 288], [279, 40, 84], [138, 30, 26], [449, 109, 234, 275, 228, 586], [291, 391, 225], [125, 163, 152]], ![[139, 71, 39, 471, 243, 199], [497, 242, 383, 207, 24, 563], [13, 118, 100], [161, 322, 240, 60, 212, 530], [338, 73, 579], [35, 435, 332], [575, 550, 302, 253, 547, 379], [41, 45, 170], [387, 451, 278]]]
 h' := ![![[304, 472, 147, 287], [553, 331, 580, 185], [324, 233, 216, 99], [252, 347, 98, 287], [119, 387, 84, 583], [45, 371, 572, 398], [481, 130, 458, 18], [246, 83, 103, 184], [0, 0, 1], [0, 1]], ![[543, 528, 397, 50], [426, 26, 69, 45], [186, 345, 21, 62], [239, 314, 421, 292], [223, 497, 387, 344], [385, 263, 88, 162], [585, 456, 274, 528], [123, 485, 543, 232], [188, 142, 511, 389], [304, 472, 147, 287]], ![[511, 173, 43, 250], [415, 133, 353, 2], [300, 92, 39, 390], [398, 121, 504, 18], [271, 385, 16, 472], [321, 485, 208, 200], [277, 307, 508, 253], [522, 223, 110, 38], [401, 487, 56, 572], [543, 528, 397, 50]], ![[0, 1], [127, 97, 172, 355], [351, 504, 311, 36], [544, 392, 151, 577], [271, 492, 100, 362], [440, 55, 306, 414], [168, 281, 521, 375], [303, 383, 418, 133], [14, 545, 19, 213], [511, 173, 43, 250]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [80, 484, 292], []]
 b := ![[], [], [73, 192, 559, 182], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI587N0 : CertifiedPrimeIdeal' SI587N0 587 where
  n := 4
  hpos := by decide
  P := [341, 504, 484, 403, 1]
  hirr := P587P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1470771067535, 1013150421460, 2177085172670, 1214741940304, 4205925194338]
  a := ![54, 34, 1, -16, -131]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3527744406613, -4103887539922, -2418101585202, -1968338477858, 4205925194338]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI587N0 : Ideal.IsPrime I587N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI587N0 B_one_repr
lemma NI587N0 : Nat.card (O ⧸ I587N0) = 118727795761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI587N0

def I587N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6257, -362, -1058, -874, 16554]] i)))

def SI587N1: IdealEqSpanCertificate' Table ![![-6257, -362, -1058, -874, 16554]] 
 ![![587, 0, 0, 0, 0], ![46, 1, 0, 0, 0], ![232, 0, 1, 0, 0], ![481, 0, 0, 1, 0], ![35, 0, 0, 0, 1]] where
  M :=![![![-6257, -362, -1058, -874, 16554], ![45344, 66951, 50174, -4554, -95932], ![-128108, -301952, -216291, 31958, 228892], ![10372, 531796, 352766, -88459, 171004], ![49588, -14604, -3162, 9884, -137719]]]
  hmulB := by decide  
  f := ![![![798653, 2614510, 474174, -88118, -1046538]], ![![61122, 200315, 36414, -6698, -79984]], ![![316804, 1038320, 188713, -34742, -414684]], ![![651123, 2138614, 390268, -70561, -850426]], ![![48001, 157594, 28736, -5214, -62721]]]
  g := ![![![165, -362, -1058, -874, 16554], ![-15548, 66951, 50174, -4554, -95932], ![69094, -301952, -216291, 31958, 228892], ![-118791, 531796, 352766, -88459, 171004], ![2591, -14604, -3162, 9884, -137719]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI587N1 : Nat.card (O ⧸ I587N1) = 587 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI587N1)

lemma isPrimeI587N1 : Ideal.IsPrime I587N1 := prime_ideal_of_norm_prime hp587.out _ NI587N1
def MulI587N0 : IdealMulLeCertificate' Table 
  ![![-798653, -2614510, -474174, 88118, 1046538]] ![![-6257, -362, -1058, -874, 16554]]
  ![![587, 0, 0, 0, 0]] where
 M := ![![![-587, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC587 : ContainsPrimesAboveP 587 ![I587N0, I587N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI587N0
    exact isPrimeI587N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 587 (by decide) (𝕀 ⊙ MulI587N0)
instance hp593 : Fact (Nat.Prime 593) := {out := by norm_num}

def I593N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![593, 0, 0, 0, 0]] i)))

def SI593N0: IdealEqSpanCertificate' Table ![![593, 0, 0, 0, 0]] 
 ![![593, 0, 0, 0, 0], ![0, 593, 0, 0, 0], ![0, 0, 593, 0, 0], ![0, 0, 0, 593, 0], ![0, 0, 0, 0, 593]] where
  M :=![![![593, 0, 0, 0, 0], ![0, 593, 0, 0, 0], ![0, 0, 593, 0, 0], ![0, 0, 0, 593, 0], ![0, 0, 0, 0, 593]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P593P0 : CertificateIrreducibleZModOfList' 593 5 2 9 [316, 440, 557, 569, 273, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [401, 50, 331, 174, 152], [504, 551, 129, 451, 140], [561, 131, 356, 255, 342], [40, 453, 370, 306, 552], [0, 1]]
 g := ![![[466, 300, 494, 444, 68], [318, 564, 524, 255], [485, 584, 118, 578], [513, 40, 395, 269], [287, 77, 143, 154, 337], [264, 525, 215, 510], [221, 577, 428, 320, 1], [], []], ![[17, 565, 557, 417, 19, 521, 25, 34], [394, 585, 166, 201], [549, 485, 453, 15], [291, 214, 418, 139], [166, 61, 408, 374, 227, 226, 498, 373], [22, 525, 74, 534], [192, 530, 173, 24, 548, 49, 226, 543], [13, 70, 426, 326], [489, 212, 468, 570]], ![[263, 423, 566, 293, 439, 313, 322, 473], [574, 65, 398, 148], [169, 505, 138, 39], [33, 470, 0, 351], [460, 83, 407, 486, 57, 21, 532, 393], [567, 19, 499, 592], [508, 294, 81, 159, 349, 385, 281, 449], [421, 60, 379, 59], [59, 379, 403, 31]], ![[185, 244, 93, 89, 451, 216, 274, 128], [112, 418, 189, 515], [367, 498, 40, 17], [404, 209, 521, 575], [274, 42, 349, 312, 590, 380, 276, 400], [591, 301, 506, 335], [248, 138, 172, 129, 381, 287, 95, 143], [551, 202, 476, 309], [540, 348, 177, 143]], ![[571, 14, 72, 517, 517, 144, 134, 138], [174, 168, 168, 78], [110, 331, 117, 153], [178, 529, 203, 98], [7, 429, 220, 456, 500, 42, 108, 325], [258, 125, 234, 158], [261, 243, 4, 304, 162, 467, 76, 550], [25, 113], [575, 377, 476, 495]]]
 h' := ![![[401, 50, 331, 174, 152], [345, 288, 272, 172, 138], [437, 211, 295, 232, 178], [557, 293, 589, 125, 551], [37, 236, 137, 444, 393], [257, 89, 28, 312, 46], [138, 324, 127, 521, 370], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[504, 551, 129, 451, 140], [498, 235, 425, 341, 346], [339, 101, 245, 167, 511], [65, 269, 412, 18, 324], [204, 66, 525, 466, 519], [375, 136, 53, 449, 519], [164, 326, 245, 284, 499], [73, 390, 235, 456, 175], [347, 485, 516, 480, 360], [401, 50, 331, 174, 152]], ![[561, 131, 356, 255, 342], [198, 322, 57, 208, 67], [280, 304, 5, 553, 335], [275, 579, 115, 27, 35], [544, 297, 362, 196, 488], [398, 113, 331, 50, 120], [571, 404, 163, 194, 77], [418, 418, 291, 384, 450], [544, 514, 515, 122, 471], [504, 551, 129, 451, 140]], ![[40, 453, 370, 306, 552], [588, 127, 452, 521, 339], [20, 164, 348, 536, 388], [188, 451, 497, 64, 69], [188, 361, 166, 104, 187], [453, 369, 94, 472, 17], [40, 256, 302, 562, 554], [550, 444, 151, 445, 350], [575, 441, 455, 127, 355], [561, 131, 356, 255, 342]], ![[0, 1], [107, 214, 573, 537, 296], [287, 406, 293, 291, 367], [55, 187, 166, 359, 207], [146, 226, 589, 569, 192], [34, 479, 87, 496, 484], [96, 469, 349, 218, 279], [336, 527, 509, 494, 210], [172, 339, 292, 457], [40, 453, 370, 306, 552]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [139, 464, 428, 383], [], [], []]
 b := ![[], [516, 485, 417, 162, 56], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI593N0 : CertifiedPrimeIdeal' SI593N0 593 where
  n := 5
  hpos := by decide
  P := [316, 440, 557, 569, 273, 1]
  hirr := P593P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1979779132364076, 1319205111449000, 2880401013989960, 1623153029612184, 5646029560493696]
  a := ![-27, -15, -1, 14, 66]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3338582010732, 2224629193000, 4857337291720, 2737188920088, 9521129107072]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI593N0 : Ideal.IsPrime I593N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI593N0 B_one_repr
lemma NI593N0 : Nat.card (O ⧸ I593N0) = 73328612386193 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI593N0

def PBC593 : ContainsPrimesAboveP 593 ![I593N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI593N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![593, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 593 (by decide) 𝕀



lemma PB2201I11_primes (p : ℕ) :
  p ∈ Set.range ![541, 547, 557, 563, 569, 571, 577, 587, 593] ↔ Nat.Prime p ∧ 523 < p ∧ p ≤ 593 := by
  rw [← List.mem_ofFn']
  convert primes_range 523 593 (by omega)

def PB2201I11 : PrimesBelowBoundCertificateInterval O 523 593 2201 where
  m := 9
  g := ![3, 2, 3, 2, 3, 2, 3, 2, 1]
  P := ![541, 547, 557, 563, 569, 571, 577, 587, 593]
  hP := PB2201I11_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I541N0, I541N1, I541N2]
    · exact ![I547N0, I547N1]
    · exact ![I557N0, I557N1, I557N2]
    · exact ![I563N0, I563N1]
    · exact ![I569N0, I569N1, I569N2]
    · exact ![I571N0, I571N1]
    · exact ![I577N0, I577N1, I577N2]
    · exact ![I587N0, I587N1]
    · exact ![I593N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC541
    · exact PBC547
    · exact PBC557
    · exact PBC563
    · exact PBC569
    · exact PBC571
    · exact PBC577
    · exact PBC587
    · exact PBC593
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![292681, 292681, 541]
    · exact ![89526025681, 547]
    · exact ![310249, 310249, 557]
    · exact ![178453547, 316969]
    · exact ![184220009, 569, 569]
    · exact ![186169411, 326041]
    · exact ![332929, 332929, 577]
    · exact ![118727795761, 587]
    · exact ![73328612386193]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI541N0
      exact NI541N1
      exact NI541N2
    · dsimp ; intro j
      fin_cases j
      exact NI547N0
      exact NI547N1
    · dsimp ; intro j
      fin_cases j
      exact NI557N0
      exact NI557N1
      exact NI557N2
    · dsimp ; intro j
      fin_cases j
      exact NI563N0
      exact NI563N1
    · dsimp ; intro j
      fin_cases j
      exact NI569N0
      exact NI569N1
      exact NI569N2
    · dsimp ; intro j
      fin_cases j
      exact NI571N0
      exact NI571N1
    · dsimp ; intro j
      fin_cases j
      exact NI577N0
      exact NI577N1
      exact NI577N2
    · dsimp ; intro j
      fin_cases j
      exact NI587N0
      exact NI587N1
    · dsimp ; intro j
      fin_cases j
      exact NI593N0
  β := ![I541N2, I547N1, I557N2, I569N1, I569N2, I577N2, I587N1]
  Il := ![[I541N2], [I547N1], [I557N2], [], [I569N1, I569N2], [], [I577N2], [I587N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
