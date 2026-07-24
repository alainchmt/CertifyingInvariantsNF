
import IdealArithmetic.Examples.NF5_3_1687500000_3.RI5_3_1687500000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp599 : Fact (Nat.Prime 599) := {out := by norm_num}

def I599N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![106812, -76154, -40398, -71499, 167199]] i)))

def SI599N0: IdealEqSpanCertificate' Table ![![106812, -76154, -40398, -71499, 167199]] 
 ![![599, 0, 0, 0, 0], ![0, 599, 0, 0, 0], ![0, 0, 599, 0, 0], ![0, 0, 0, 599, 0], ![540, 22, 35, 74, 1]] where
  M :=![![![106812, -76154, -40398, -71499, 167199], ![341022, -243783, -130076, -230418, 539046], ![1103364, -788936, -421263, -746260, 1745892], ![1616949, -1156264, -617442, -1093882, 2559137], ![1253264, -896284, -478724, -848136, 1984261]]]
  hmulB := by decide  
  f := ![![![678, -760, -250, -389, 871]], ![![1082, -1221, -396, -618, 1386]], ![![1764, -1936, -681, -1020, 2292]], ![![959, -1014, -362, -600, 1287]], ![![874, -970, -325, -508, 1131]]]
  g := ![![![-150552, -6268, -9837, -20775, 167199], ![-485382, -20205, -31714, -66978, 539046], ![-1572084, -65440, -102717, -216932, 1745892], ![-2304369, -95922, -150563, -317980, 2559137], ![-1786724, -74374, -116741, -246550, 1984261]]]
  hle1 := by decide   
  hle2 := by decide  


def P599P0 : CertificateIrreducibleZModOfList' 599 4 2 9 [453, 363, 401, 312, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [386, 218, 88, 178], [242, 62, 377, 495], [258, 318, 134, 525], [0, 1]]
 g := ![![[536, 455, 273, 169], [121, 261, 87, 312], [391, 346, 360, 322], [99, 471, 12], [112, 19, 65, 185], [530, 20, 415], [499, 219, 210, 306], [1], []], ![[209, 215, 106, 239, 185, 262], [132, 499, 541, 288, 441, 286], [239, 220, 246, 62, 52, 238], [85, 367, 153], [79, 451, 591, 18, 189, 345], [274, 409, 390], [181, 415, 251, 182, 474, 23], [512, 110, 538], [435, 69, 536]], ![[176, 355, 173, 46, 495, 59], [60, 303, 303, 57, 324, 175], [10, 393, 394, 215, 395, 353], [569, 252, 96], [598, 291, 265, 287, 206, 155], [172, 522, 468], [34, 274, 296, 119, 197, 237], [248, 219, 159], [449, 227, 34]], ![[191, 594, 359, 182, 332, 478], [437, 439, 4, 433, 121, 266], [150, 192, 102, 187, 340, 382], [78, 153, 508], [410, 323, 151, 455, 346, 575], [196, 78, 513], [303, 24, 60, 541, 173, 590], [334, 475, 142], [468, 370, 85]]]
 h' := ![![[386, 218, 88, 178], [295, 588, 58, 586], [181, 245, 414, 415], [372, 299, 295, 378], [179, 217, 145, 376], [568, 88, 241, 571], [375, 339, 275, 181], [146, 236, 198, 287], [0, 0, 1], [0, 1]], ![[242, 62, 377, 495], [458, 548, 54, 533], [105, 405, 305, 399], [466, 133, 316, 224], [6, 14, 510, 460], [574, 574, 329, 526], [50, 535, 383, 315], [30, 352, 69, 253], [460, 99, 224, 522], [386, 218, 88, 178]], ![[258, 318, 134, 525], [456, 445, 10, 428], [89, 226, 579, 34], [203, 497, 437, 143], [315, 101, 18, 240], [570, 408, 179, 160], [246, 528, 435, 470], [319, 534, 483, 372], [125, 196, 107, 342], [242, 62, 377, 495]], ![[0, 1], [267, 216, 477, 250], [261, 322, 499, 350], [111, 269, 150, 453], [549, 267, 525, 122], [192, 128, 449, 540], [370, 395, 105, 232], [157, 76, 448, 286], [117, 304, 267, 334], [258, 318, 134, 525]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [167, 45, 277], []]
 b := ![[], [], [326, 291, 358, 354], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI599N0 : CertifiedPrimeIdeal' SI599N0 599 where
  n := 4
  hpos := by decide
  P := [453, 363, 401, 312, 1]
  hirr := P599P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6277337410304, 5005372204707, 1149396727563, 6809089906391, -10623862200271]
  a := ![-189, -11, 173, 177, -387]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![9566958682364, 398548147931, 622678754152, 1323831206555, -10623862200271]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI599N0 : Ideal.IsPrime I599N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI599N0 B_one_repr
lemma NI599N0 : Nat.card (O ⧸ I599N0) = 128738157601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI599N0

def I599N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-678, 760, 250, 389, -871]] i)))

def SI599N1: IdealEqSpanCertificate' Table ![![-678, 760, 250, 389, -871]] 
 ![![599, 0, 0, 0, 0], ![185, 1, 0, 0, 0], ![517, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![264, 0, 0, 0, 1]] where
  M :=![![![-678, 760, 250, 389, -871], ![-1082, 1221, 396, 618, -1386], ![-1764, 1936, 681, 1020, -2292], ![-959, 1014, 362, 600, -1287], ![-896, 972, 340, 536, -1179]]]
  hmulB := by decide  
  f := ![![![-106812, 76154, 40398, 71499, -167199]], ![![-33558, 23927, 12694, 22467, -52539]], ![![-94032, 67046, 35571, 62957, -147225]], ![![-3591, 2566, 1368, 2423, -5668]], ![![-49168, 35060, 18604, 32928, -77003]]]
  g := ![![![-71, 760, 250, 389, -871], ![-115, 1221, 396, 618, -1386], ![-187, 1936, 681, 1020, -2292], ![-65, 1014, 362, 600, -1287], ![-80, 972, 340, 536, -1179]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI599N1 : Nat.card (O ⧸ I599N1) = 599 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI599N1)

lemma isPrimeI599N1 : Ideal.IsPrime I599N1 := prime_ideal_of_norm_prime hp599.out _ NI599N1
def MulI599N0 : IdealMulLeCertificate' Table 
  ![![106812, -76154, -40398, -71499, 167199]] ![![-678, 760, 250, 389, -871]]
  ![![599, 0, 0, 0, 0]] where
 M := ![![![-599, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC599 : ContainsPrimesAboveP 599 ![I599N0, I599N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI599N0
    exact isPrimeI599N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 599 (by decide) (𝕀 ⊙ MulI599N0)
instance hp601 : Fact (Nat.Prime 601) := {out := by norm_num}

def I601N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![842, -583, -327, -587, 1349]] i)))

def SI601N0: IdealEqSpanCertificate' Table ![![842, -583, -327, -587, 1349]] 
 ![![601, 0, 0, 0, 0], ![0, 601, 0, 0, 0], ![0, 0, 601, 0, 0], ![19, 237, 539, 1, 0], ![470, 137, 527, 0, 1]] where
  M :=![![![842, -583, -327, -587, 1349], ![2326, -2008, -623, -1456, 3478], ![8408, -4687, -4350, -5610, 13904], ![20067, -9529, -10821, -16558, 35111], ![12760, -6912, -6374, -9824, 21669]]]
  hmulB := by decide  
  f := ![![![-589160, 345837, 95905, 146617, -317937]], ![![-200826, 117916, 32703, 49996, -108418]], ![![-68528, 40287, 11178, 17090, -37064]], ![![-159131, 93477, 25929, 39641, -85966]], ![![-566106, 332365, 92175, 140916, -305579]]]
  g := ![![![-1035, -77, -657, -587, 1349], ![-2670, -222, -1745, -1456, 3478], ![-10682, -965, -7168, -5610, 13904], ![-26901, -1490, -15956, -16558, 35111], ![-16614, -1077, -10201, -9824, 21669]]]
  hle1 := by decide   
  hle2 := by decide  


def P601P0 : CertificateIrreducibleZModOfList' 601 3 2 9 [299, 486, 587, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [203, 423, 494], [412, 177, 107], [0, 1]]
 g := ![![[536, 304, 524], [321, 69], [27, 113], [517, 582, 227], [205, 413, 111], [527, 363], [75, 527, 561], [14, 1], []], ![[337, 17, 377, 284], [510, 157], [541, 270], [559, 376, 503, 506], [196, 522, 358, 429], [398, 331], [375, 24, 256, 426], [304, 77], [48, 30]], ![[176, 303, 476, 548], [362, 512], [50, 26], [412, 191, 162, 494], [236, 156, 332, 465], [423, 556], [20, 505, 138, 548], [482, 432], [435, 30]]]
 h' := ![![[203, 423, 494], [281, 33, 112], [591, 482, 182], [475, 277, 519], [7, 446, 210], [375, 471, 187], [413, 541, 63], [21, 109, 311], [0, 0, 1], [0, 1]], ![[412, 177, 107], [348, 431, 66], [515, 401, 473], [2, 522, 321], [581, 422, 266], [131, 596, 131], [429, 366, 142], [341, 515, 112], [413, 8, 177], [203, 423, 494]], ![[0, 1], [308, 137, 423], [206, 319, 547], [545, 403, 362], [179, 334, 125], [331, 135, 283], [552, 295, 396], [291, 578, 178], [13, 593, 423], [412, 177, 107]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [215, 563], []]
 b := ![[], [234, 467, 185], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI601N0 : CertifiedPrimeIdeal' SI601N0 601 where
  n := 3
  hpos := by decide
  P := [299, 486, 587, 1]
  hirr := P601P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![26904266611, 26121109550, -45601300572, -28682464510, 67725169954]
  a := ![171, -54, -156, -226, 350]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-52011578679, -4083998478, -33738631440, -28682464510, 67725169954]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI601N0 : Ideal.IsPrime I601N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI601N0 B_one_repr
lemma NI601N0 : Nat.card (O ⧸ I601N0) = 217081801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI601N0

def I601N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-46, 49, 17, 27, -61]] i)))

def SI601N1: IdealEqSpanCertificate' Table ![![-46, 49, 17, 27, -61]] 
 ![![601, 0, 0, 0, 0], ![294, 1, 0, 0, 0], ![108, 0, 1, 0, 0], ![204, 0, 0, 1, 0], ![111, 0, 0, 0, 1]] where
  M :=![![![-46, 49, 17, 27, -61], ![-86, 86, 33, 52, -118], ![-176, 169, 64, 110, -248], ![-127, 135, 31, 70, -171], ![-120, 116, 38, 72, -169]]]
  hmulB := by decide  
  f := ![![![-47628, 27965, 7761, 11863, -25727]], ![![-23326, 13696, 3801, 5810, -12600]], ![![-8568, 5031, 1396, 2134, -4628]], ![![-16155, 9485, 2633, 4024, -8727]], ![![-8756, 5141, 1427, 2181, -4730]]]
  g := ![![![-25, 49, 17, 27, -61], ![-44, 86, 33, 52, -118], ![-86, 169, 64, 110, -248], ![-64, 135, 31, 70, -171], ![-57, 116, 38, 72, -169]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI601N1 : Nat.card (O ⧸ I601N1) = 601 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI601N1)

lemma isPrimeI601N1 : Ideal.IsPrime I601N1 := prime_ideal_of_norm_prime hp601.out _ NI601N1

def I601N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-22161, 13589, 4561, 7372, -16486]] i)))

def SI601N2: IdealEqSpanCertificate' Table ![![-22161, 13589, 4561, 7372, -16486]] 
 ![![601, 0, 0, 0, 0], ![431, 1, 0, 0, 0], ![549, 0, 1, 0, 0], ![473, 0, 0, 1, 0], ![451, 0, 0, 0, 1]] where
  M :=![![![-22161, 13589, 4561, 7372, -16486], ![-20096, 13630, 6343, 10990, -25448], ![-47380, 33675, 17636, 31150, -72780], ![-63602, 45853, 24871, 44161, -103426], ![-42264, 31424, 18142, 32496, -76411]]]
  hmulB := by decide  
  f := ![![![12123, 37631, -42671, -12612, 42566]], ![![9229, 26823, -30924, -9622, 31554]], ![![7387, 32404, -34103, -7578, 30354]], ![![6781, 38500, -38794, -6855, 31944]], ![![7257, 31447, -33173, -7448, 29639]]]
  g := ![![![-7379, 13589, 4561, 7372, -16486], ![-5155, 13630, 6343, 10990, -25448], ![-10239, 33675, 17636, 31150, -72780], ![-12851, 45853, 24871, 44161, -103426], ![-7413, 31424, 18142, 32496, -76411]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI601N2 : Nat.card (O ⧸ I601N2) = 601 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI601N2)

lemma isPrimeI601N2 : Ideal.IsPrime I601N2 := prime_ideal_of_norm_prime hp601.out _ NI601N2
def MulI601N0 : IdealMulLeCertificate' Table 
  ![![842, -583, -327, -587, 1349]] ![![-46, 49, 17, 27, -61]]
  ![![-18373, 13096, 7212, 12486, -29076]] where
 M := ![![![-18373, 13096, 7212, 12486, -29076]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI601N1 : IdealMulLeCertificate' Table 
  ![![-18373, 13096, 7212, 12486, -29076]] ![![-22161, 13589, 4561, 7372, -16486]]
  ![![601, 0, 0, 0, 0]] where
 M := ![![![237015769, -169471783, -90497979, -160326366, 375090110]]]
 hmul := by decide  
 g := ![![![![394369, -281983, -150579, -266766, 624110]]]]
 hle2 := by decide  


def PBC601 : ContainsPrimesAboveP 601 ![I601N0, I601N1, I601N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI601N0
    exact isPrimeI601N1
    exact isPrimeI601N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 601 (by decide) (𝕀 ⊙ MulI601N0 ⊙ MulI601N1)
instance hp607 : Fact (Nat.Prime 607) := {out := by norm_num}

def I607N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-29, 9, -5, -20, 42]] i)))

def SI607N0: IdealEqSpanCertificate' Table ![![-29, 9, -5, -20, 42]] 
 ![![607, 0, 0, 0, 0], ![0, 607, 0, 0, 0], ![0, 0, 607, 0, 0], ![176, 132, 285, 1, 0], ![271, 540, 468, 0, 1]] where
  M :=![![![-29, 9, -5, -20, 42], ![0, -116, 75, 34, -40], ![628, 183, -762, -490, 1324], ![2950, -1161, -1645, -2895, 5430], ![1520, -574, -884, -1388, 2737]]]
  hmulB := by decide  
  f := ![![![-7087, 7937, 2613, 4060, -9094]], ![![-11360, 12740, 4195, 6518, -14600]], ![![-18244, 20471, 6738, 10470, -23452]], ![![-13106, 14700, 4839, 7519, -16842]], ![![-27351, 30677, 10099, 15692, -35149]]]
  g := ![![![-13, -33, -23, -20, 42], ![8, 28, 15, 34, -40], ![-448, -1071, -792, -490, 1324], ![-1580, -4203, -2830, -2895, 5430], ![-817, -2134, -1460, -1388, 2737]]]
  hle1 := by decide   
  hle2 := by decide  


def P607P0 : CertificateIrreducibleZModOfList' 607 3 2 9 [428, 96, 181, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [193, 399, 541], [233, 207, 66], [0, 1]]
 g := ![![[486, 470, 553], [367, 358, 98], [530, 204, 446], [259, 283, 389], [23, 228, 541], [290, 488], [515, 189, 22], [426, 1], []], ![[430, 449, 211, 389], [240, 576, 143, 357], [52, 23, 286, 301], [604, 566, 277, 574], [577, 309, 124, 475], [378, 370], [394, 601, 106, 439], [602, 359], [198, 107]], ![[347, 596, 192, 465], [305, 438, 506, 374], [178, 274, 241, 323], [325, 119, 334, 462], [180, 297, 519, 409], [603, 416], [10, 389, 200, 452], [110, 167], [66, 107]]]
 h' := ![![[193, 399, 541], [137, 441, 401], [178, 443, 463], [229, 120, 59], [475, 436, 379], [486, 459, 380], [528, 562, 54], [379, 559, 494], [0, 0, 1], [0, 1]], ![[233, 207, 66], [7, 201, 485], [301, 428, 440], [30, 20, 44], [230, 445, 510], [282, 498, 413], [186, 443, 187], [61, 598, 415], [458, 588, 207], [193, 399, 541]], ![[0, 1], [527, 572, 328], [349, 343, 311], [369, 467, 504], [413, 333, 325], [260, 257, 421], [157, 209, 366], [224, 57, 305], [547, 19, 399], [233, 207, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [176, 361], []]
 b := ![[], [28, 48, 217], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI607N0 : CertifiedPrimeIdeal' SI607N0 607 where
  n := 3
  hpos := by decide
  P := [428, 96, 181, 1]
  hirr := P607P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9418769, 49330630, -50353448, -9497171, 42412311]
  a := ![-62, -6, 57, 55, -127]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-16166088, -35584334, -28323923, -9497171, 42412311]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI607N0 : Ideal.IsPrime I607N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI607N0 B_one_repr
lemma NI607N0 : Nat.card (O ⧸ I607N0) = 223648543 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI607N0

def I607N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7087, -7937, -2613, -4060, 9094]] i)))

def SI607N1: IdealEqSpanCertificate' Table ![![7087, -7937, -2613, -4060, 9094]] 
 ![![607, 0, 0, 0, 0], ![0, 607, 0, 0, 0], ![524, 37, 1, 0, 0], ![18, 185, 0, 1, 0], ![178, 574, 0, 0, 1]] where
  M :=![![![7087, -7937, -2613, -4060, 9094], ![11360, -12740, -4195, -6518, 14600], ![18244, -20471, -6738, -10470, 23452], ![8970, -10073, -3315, -5147, 11530], ![8888, -9984, -3286, -5104, 11433]]]
  hmulB := by decide  
  f := ![![![29, -9, 5, 20, -42]], ![![0, 116, -75, -34, 40]], ![![24, -1, 1, 16, -36]], ![![-4, 37, -20, -5, 2]], ![![6, 108, -68, -24, 21]]]
  g := ![![![-279, -7216, -2613, -4060, 9094], ![-448, -11585, -4195, -6518, 14600], ![-720, -18609, -6738, -10470, 23452], ![-352, -9149, -3315, -5147, 11530], ![-350, -9072, -3286, -5104, 11433]]]
  hle1 := by decide   
  hle2 := by decide  


def P607P1 : CertificateIrreducibleZModOfList' 607 2 2 9 [523, 135, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [472, 606], [0, 1]]
 g := ![![[497, 224], [328, 524], [520, 200], [550, 497], [382, 112], [214], [551, 346], [15], [1]], ![[0, 383], [0, 83], [228, 407], [225, 110], [437, 495], [214], [580, 261], [15], [1]]]
 h' := ![![[472, 606], [237, 312], [583, 391], [68, 488], [524, 503], [411, 521], [152, 550], [425, 182], [84, 472], [0, 1]], ![[0, 1], [0, 295], [0, 216], [351, 119], [603, 104], [488, 86], [563, 57], [135, 425], [99, 135], [472, 606]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [313]]
 b := ![[], [93, 460]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI607N1 : CertifiedPrimeIdeal' SI607N1 607 where
  n := 2
  hpos := by decide
  P := [523, 135, 1]
  hirr := P607P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1352810, -332740, -901882, -1385923, 2610159]
  a := ![295, 33, -270, -263, 604]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![56470, -1991431, -901882, -1385923, 2610159]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI607N1 : Ideal.IsPrime I607N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI607N1 B_one_repr
lemma NI607N1 : Nat.card (O ⧸ I607N1) = 368449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI607N1
def MulI607N0 : IdealMulLeCertificate' Table 
  ![![-29, 9, -5, -20, 42]] ![![7087, -7937, -2613, -4060, 9094]]
  ![![607, 0, 0, 0, 0]] where
 M := ![![![-607, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC607 : ContainsPrimesAboveP 607 ![I607N0, I607N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI607N0
    exact isPrimeI607N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 607 (by decide) (𝕀 ⊙ MulI607N0)
instance hp613 : Fact (Nat.Prime 613) := {out := by norm_num}

def I613N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-52, 61, 19, 31, -69]] i)))

def SI613N0: IdealEqSpanCertificate' Table ![![-52, 61, 19, 31, -69]] 
 ![![613, 0, 0, 0, 0], ![0, 613, 0, 0, 0], ![174, 498, 1, 0, 0], ![197, 218, 0, 1, 0], ![457, 172, 0, 0, 1]] where
  M :=![![![-52, 61, 19, 31, -69], ![-78, 98, 25, 40, -94], ![-200, 121, 136, 142, -320], ![-179, 221, -1, 156, -247], ![-128, 130, 32, 100, -183]]]
  hmulB := by decide  
  f := ![![![466, -247, -41, -49, 89]], ![![-278, 238, 151, 276, -654]], ![![-96, 125, 112, 212, -510]], ![![47, 8, 42, 85, -210]], ![![266, -115, 13, 43, -122]]]
  g := ![![![36, -7, 19, 31, -69], ![50, -8, 25, 40, -94], ![154, -71, 136, 142, -320], ![134, 15, -1, 156, -247], ![95, -10, 32, 100, -183]]]
  hle1 := by decide   
  hle2 := by decide  


def P613P0 : CertificateIrreducibleZModOfList' 613 2 2 9 [122, 419, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [194, 612], [0, 1]]
 g := ![![[119, 427], [336], [441, 181], [524], [359], [200, 469], [338, 243], [243], [1]], ![[202, 186], [336], [1, 432], [524], [359], [462, 144], [279, 370], [243], [1]]]
 h' := ![![[194, 612], [14, 264], [142, 229], [500, 346], [26, 433], [120, 225], [448, 420], [563, 419], [491, 194], [0, 1]], ![[0, 1], [351, 349], [432, 384], [194, 267], [47, 180], [247, 388], [399, 193], [320, 194], [121, 419], [194, 612]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [593]]
 b := ![[], [357, 603]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI613N0 : CertifiedPrimeIdeal' SI613N0 613 where
  n := 2
  hpos := by decide
  P := [122, 419, 1]
  hirr := P613P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![681140, -1915839, 1042103, -742932, 507766]
  a := ![-421, -19, 386, 404, -862]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-434480, -727993, 1042103, -742932, 507766]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI613N0 : Ideal.IsPrime I613N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI613N0 B_one_repr
lemma NI613N0 : Nat.card (O ⧸ I613N0) = 375769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI613N0

def I613N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11989, -13303, -4373, -6794, 15214]] i)))

def SI613N1: IdealEqSpanCertificate' Table ![![11989, -13303, -4373, -6794, 15214]] 
 ![![613, 0, 0, 0, 0], ![0, 613, 0, 0, 0], ![285, 104, 1, 0, 0], ![505, 252, 0, 1, 0], ![449, 115, 0, 0, 1]] where
  M :=![![![11989, -13303, -4373, -6794, 15214], ![18932, -21186, -6975, -10838, 24276], ![30324, -33995, -11196, -17398, 38972], ![14896, -16727, -5511, -8565, 19188], ![14664, -16520, -5446, -8464, 18963]]]
  hmulB := by decide  
  f := ![![![89, -13, -73, -62, 158]], ![![556, -266, -281, -510, 988]], ![![133, -54, -77, -112, 234]], ![![301, -112, -182, -259, 538]], ![![169, -57, -108, -140, 301]]]
  g := ![![![-3494, 659, -4373, -6794, 15214], ![-5579, 1050, -6975, -10838, 24276], ![-8958, 1685, -11196, -17398, 38972], ![-4412, 829, -5511, -8565, 19188], ![-4361, 819, -5446, -8464, 18963]]]
  hle1 := by decide   
  hle2 := by decide  


def P613P1 : CertificateIrreducibleZModOfList' 613 2 2 9 [604, 116, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [497, 612], [0, 1]]
 g := ![![[532, 68], [524], [220, 363], [369], [313], [257, 363], [77, 584], [583], [1]], ![[0, 545], [524], [409, 250], [369], [313], [446, 250], [376, 29], [583], [1]]]
 h' := ![![[497, 612], [77, 397], [141, 180], [252, 444], [70, 414], [474, 84], [80, 169], [424, 166], [9, 497], [0, 1]], ![[0, 1], [0, 216], [103, 433], [240, 169], [473, 199], [538, 529], [92, 444], [171, 447], [592, 116], [497, 612]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [408]]
 b := ![[], [185, 204]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI613N1 : CertifiedPrimeIdeal' SI613N1 613 where
  n := 2
  hpos := by decide
  P := [604, 116, 1]
  hirr := P613P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-660440, -850924, 1298740, 701960, -1761452]
  a := ![210, 0, -192, -220, 430]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![107016, -179848, 1298740, 701960, -1761452]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI613N1 : Ideal.IsPrime I613N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI613N1 B_one_repr
lemma NI613N1 : Nat.card (O ⧸ I613N1) = 375769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI613N1

def I613N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-46, 34, 18, 33, -77]] i)))

def SI613N2: IdealEqSpanCertificate' Table ![![-46, 34, 18, 33, -77]] 
 ![![613, 0, 0, 0, 0], ![11, 1, 0, 0, 0], ![492, 0, 1, 0, 0], ![47, 0, 0, 1, 0], ![61, 0, 0, 0, 1]] where
  M :=![![![-46, 34, 18, 33, -77], ![-154, 115, 56, 102, -242], ![-556, 348, 251, 388, -908], ![-855, 632, 298, 612, -1355], ![-640, 456, 240, 448, -1017]]]
  hmulB := by decide  
  f := ![![![557540, -625152, -205870, -319891, 716557]], ![![11466, -12857, -4234, -6579, 14737]], ![![449836, -504388, -166101, -258096, 578136]], ![![43905, -49230, -16212, -25191, 56428]], ![![56628, -63496, -20910, -32491, 72780]]]
  g := ![![![-10, 34, 18, 33, -77], ![-31, 115, 56, 102, -242], ![-148, 348, 251, 388, -908], ![-164, 632, 298, 612, -1355], ![-135, 456, 240, 448, -1017]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI613N2 : Nat.card (O ⧸ I613N2) = 613 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI613N2)

lemma isPrimeI613N2 : Ideal.IsPrime I613N2 := prime_ideal_of_norm_prime hp613.out _ NI613N2
def MulI613N0 : IdealMulLeCertificate' Table 
  ![![-52, 61, 19, 31, -69]] ![![11989, -13303, -4373, -6794, 15214]]
  ![![557540, -625152, -205870, -319891, 716557]] where
 M := ![![![557540, -625152, -205870, -319891, 716557]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI613N1 : IdealMulLeCertificate' Table 
  ![![557540, -625152, -205870, -319891, 716557]] ![![-46, 34, 18, 33, -77]]
  ![![613, 0, 0, 0, 0]] where
 M := ![![![613, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC613 : ContainsPrimesAboveP 613 ![I613N0, I613N1, I613N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI613N0
    exact isPrimeI613N1
    exact isPrimeI613N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 613 (by decide) (𝕀 ⊙ MulI613N0 ⊙ MulI613N1)
instance hp617 : Fact (Nat.Prime 617) := {out := by norm_num}

def I617N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![950, -1065, -351, -545, 1221]] i)))

def SI617N0: IdealEqSpanCertificate' Table ![![950, -1065, -351, -545, 1221]] 
 ![![617, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![517, 0, 1, 0, 0], ![495, 0, 0, 1, 0], ![515, 0, 0, 0, 1]] where
  M :=![![![950, -1065, -351, -545, 1221], ![1530, -1712, -567, -880, 1970], ![2440, -2767, -882, -1394, 3120], ![1161, -1319, -437, -642, 1473], ![1176, -1332, -434, -664, 1501]]]
  hmulB := by decide  
  f := ![![![43504, -30793, -16071, -28373, 66275]], ![![922, -654, -343, -606, 1416]], ![![37152, -26302, -13733, -24247, 56639]], ![![35925, -25436, -13284, -23455, 54790]], ![![37104, -26269, -13717, -24219, 56574]]]
  g := ![![![-269, -1065, -351, -545, 1221], ![-433, -1712, -567, -880, 1970], ![-698, -2767, -882, -1394, 3120], ![-325, -1319, -437, -642, 1473], ![-333, -1332, -434, -664, 1501]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI617N0 : Nat.card (O ⧸ I617N0) = 617 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI617N0)

lemma isPrimeI617N0 : Ideal.IsPrime I617N0 := prime_ideal_of_norm_prime hp617.out _ NI617N0

def I617N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![446, -412, -130, -201, 447]] i)))

def SI617N1: IdealEqSpanCertificate' Table ![![446, -412, -130, -201, 447]] 
 ![![617, 0, 0, 0, 0], ![60, 1, 0, 0, 0], ![102, 0, 1, 0, 0], ![612, 0, 0, 1, 0], ![190, 0, 0, 0, 1]] where
  M :=![![![446, -412, -130, -201, 447], ![498, -533, -172, -266, 594], ![708, -800, -257, -396, 884], ![275, -346, -106, -160, 355], ![224, -316, -100, -152, 339]]]
  hmulB := by decide  
  f := ![![![68, 246, -266, -65, 241]], ![![10, 23, -28, -10, 30]], ![![-12, 28, -13, 14, -14]], ![![47, 300, -294, -42, 223]], ![![8, 96, -88, -6, 57]]]
  g := ![![![124, -412, -130, -201, 447], ![162, -533, -172, -266, 594], ![242, -800, -257, -396, 884], ![101, -346, -106, -160, 355], ![94, -316, -100, -152, 339]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI617N1 : Nat.card (O ⧸ I617N1) = 617 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI617N1)

lemma isPrimeI617N1 : Ideal.IsPrime I617N1 := prime_ideal_of_norm_prime hp617.out _ NI617N1

def I617N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![62, -39, -11, -17, 37]] i)))

def SI617N2: IdealEqSpanCertificate' Table ![![62, -39, -11, -17, 37]] 
 ![![617, 0, 0, 0, 0], ![139, 1, 0, 0, 0], ![423, 0, 1, 0, 0], ![148, 0, 0, 1, 0], ![442, 0, 0, 0, 1]] where
  M :=![![![62, -39, -11, -17, 37], ![26, -20, -5, -8, 18], ![24, -13, -14, -14, 32], ![13, -15, -3, -18, 29], ![-16, 6, 0, -4, 5]]]
  hmulB := by decide  
  f := ![![![1712, -1291, -643, -1125, 2619]], ![![394, -297, -148, -259, 603]], ![![1200, -904, -451, -789, 1837]], ![![449, -337, -169, -296, 689]], ![![1256, -946, -472, -826, 1923]]]
  g := ![![![-6, -39, -11, -17, 37], ![-3, -20, -5, -8, 18], ![-7, -13, -14, -14, 32], ![-11, -15, -3, -18, 29], ![-4, 6, 0, -4, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI617N2 : Nat.card (O ⧸ I617N2) = 617 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI617N2)

lemma isPrimeI617N2 : Ideal.IsPrime I617N2 := prime_ideal_of_norm_prime hp617.out _ NI617N2

def I617N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1418, -835, -235, -361, 785]] i)))

def SI617N3: IdealEqSpanCertificate' Table ![![1418, -835, -235, -361, 785]] 
 ![![617, 0, 0, 0, 0], ![444, 1, 0, 0, 0], ![304, 0, 1, 0, 0], ![160, 0, 0, 1, 0], ![553, 0, 0, 0, 1]] where
  M :=![![![1418, -835, -235, -361, 785], ![538, -324, -101, -160, 354], ![360, -237, -102, -174, 400], ![77, -83, -75, -142, 341], ![-496, 262, 32, 28, -35]]]
  hmulB := by decide  
  f := ![![![1588, -1655, -643, -965, 2127]], ![![1146, -1196, -463, -696, 1534]], ![![784, -819, -318, -474, 1048]], ![![441, -425, -197, -280, 613]], ![![1436, -1483, -589, -877, 1932]]]
  g := ![![![109, -835, -235, -361, 785], ![8, -324, -101, -160, 354], ![-92, -237, -102, -174, 400], ![-172, -83, -75, -142, 341], ![-181, 262, 32, 28, -35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI617N3 : Nat.card (O ⧸ I617N3) = 617 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI617N3)

lemma isPrimeI617N3 : Ideal.IsPrime I617N3 := prime_ideal_of_norm_prime hp617.out _ NI617N3

def I617N4 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![465, -321, -185, -322, 744]] i)))

def SI617N4: IdealEqSpanCertificate' Table ![![465, -321, -185, -322, 744]] 
 ![![617, 0, 0, 0, 0], ![581, 1, 0, 0, 0], ![555, 0, 1, 0, 0], ![136, 0, 0, 1, 0], ![36, 0, 0, 0, 1]] where
  M :=![![![465, -321, -185, -322, 744], ![1356, -1108, -411, -882, 2068], ![4316, -2887, -1866, -2766, 6868], ![9916, -4421, -5679, -7917, 17388], ![6488, -3520, -3286, -4848, 10961]]]
  hmulB := by decide  
  f := ![![![-1366671, 558953, 128455, 192162, -398016]], ![![-1286751, 525601, 120686, 180520, -373812]], ![![-1227777, 500850, 114899, 171844, -355756]], ![![-299860, 121891, 27895, 41707, -86284]], ![![-77292, 30678, 6904, 10300, -21207]]]
  g := ![![![497, -321, -185, -322, 744], ![1489, -1108, -411, -882, 2068], ![4613, -2887, -1866, -2766, 6868], ![10018, -4421, -5679, -7917, 17388], ![6710, -3520, -3286, -4848, 10961]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI617N4 : Nat.card (O ⧸ I617N4) = 617 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI617N4)

lemma isPrimeI617N4 : Ideal.IsPrime I617N4 := prime_ideal_of_norm_prime hp617.out _ NI617N4
def MulI617N0 : IdealMulLeCertificate' Table 
  ![![950, -1065, -351, -545, 1221]] ![![446, -412, -130, -201, 447]]
  ![![-231549, 259779, 85557, 132944, -297800]] where
 M := ![![![-231549, 259779, 85557, 132944, -297800]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI617N1 : IdealMulLeCertificate' Table 
  ![![-231549, 259779, 85557, 132944, -297800]] ![![62, -39, -11, -17, 37]]
  ![![944656, -1058370, -348486, -541489, 1212909]] where
 M := ![![![944656, -1058370, -348486, -541489, 1212909]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI617N2 : IdealMulLeCertificate' Table 
  ![![944656, -1058370, -348486, -541489, 1212909]] ![![1418, -835, -235, -361, 785]]
  ![![1366671, -558953, -128455, -192162, 398016]] where
 M := ![![![1366671, -558953, -128455, -192162, 398016]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI617N3 : IdealMulLeCertificate' Table 
  ![![1366671, -558953, -128455, -192162, 398016]] ![![465, -321, -185, -322, 744]]
  ![![617, 0, 0, 0, 0]] where
 M := ![![![-617, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC617 : ContainsPrimesAboveP 617 ![I617N0, I617N1, I617N2, I617N3, I617N4] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI617N0
    exact isPrimeI617N1
    exact isPrimeI617N2
    exact isPrimeI617N3
    exact isPrimeI617N4
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 617 (by decide) (𝕀 ⊙ MulI617N0 ⊙ MulI617N1 ⊙ MulI617N2 ⊙ MulI617N3)
instance hp619 : Fact (Nat.Prime 619) := {out := by norm_num}

def I619N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![20995, -11362, -3046, -4640, 9988]] i)))

def SI619N0: IdealEqSpanCertificate' Table ![![20995, -11362, -3046, -4640, 9988]] 
 ![![619, 0, 0, 0, 0], ![0, 619, 0, 0, 0], ![0, 0, 619, 0, 0], ![589, 243, 341, 1, 0], ![354, 97, 451, 0, 1]] where
  M :=![![![20995, -11362, -3046, -4640, 9988], ![4880, -1319, -198, -276, 480], ![-1992, 3650, 1285, 2004, -4536], ![-5716, 4578, 1402, 2167, -4788], ![-13984, 9420, 2744, 4216, -9233]]]
  hmulB := by decide  
  f := ![![![73, -50, -30, -48, 116]], ![![304, -169, -150, -228, 512]], ![![664, -814, 19, -396, 872]], ![![555, -563, -77, -353, 792]], ![![574, -649, -27, -352, 783]]]
  g := ![![![-1263, 238, -4726, -4640, 9988], ![-4, 31, -198, -276, 480], ![684, -70, 2203, 2004, -4536], ![667, -93, 2297, 2167, -4788], ![1246, -193, 4409, 4216, -9233]]]
  hle1 := by decide   
  hle2 := by decide  


def P619P0 : CertificateIrreducibleZModOfList' 619 3 2 9 [380, 128, 372, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [70, 28, 523], [177, 590, 96], [0, 1]]
 g := ![![[179, 75, 37], [353, 43, 182], [424, 508], [219, 149, 474], [462, 41], [437, 295, 342], [125, 476, 298], [247, 1], []], ![[131, 165, 376, 392], [412, 573, 519, 176], [258, 136], [58, 170, 423, 250], [597, 552], [311, 23, 99, 15], [611, 579, 425, 593], [219, 222], [484, 550]], ![[394, 222, 348, 569], [297, 499, 115, 365], [213, 379], [520, 317, 186, 196], [115, 31], [228, 277, 568, 143], [41, 575, 7, 553], [510, 165], [292, 550]]]
 h' := ![![[70, 28, 523], [183, 385, 395], [616, 165, 406], [345, 347, 462], [605, 85, 481], [451, 284, 56], [163, 569, 588], [228, 192, 219], [0, 0, 1], [0, 1]], ![[177, 590, 96], [319, 217, 486], [27, 50, 241], [320, 204, 334], [216, 12, 175], [108, 534, 205], [43, 562, 128], [273, 441, 596], [490, 376, 590], [70, 28, 523]], ![[0, 1], [478, 17, 357], [293, 404, 591], [607, 68, 442], [146, 522, 582], [520, 420, 358], [587, 107, 522], [65, 605, 423], [220, 243, 28], [177, 590, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [400, 67], []]
 b := ![[], [225, 454, 149], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI619N0 : CertifiedPrimeIdeal' SI619N0 619 where
  n := 3
  hpos := by decide
  P := [380, 128, 372, 1]
  hirr := P619P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-280378082, -227093741, 435941469, 302492884, -685815229]
  a := ![-29, 11, 29, 41, -60]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![103925532, -11645860, 333745616, 302492884, -685815229]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI619N0 : Ideal.IsPrime I619N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI619N0 B_one_repr
lemma NI619N0 : Nat.card (O ⧸ I619N0) = 237176659 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI619N0

def I619N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-73, 50, 30, 48, -116]] i)))

def SI619N1: IdealEqSpanCertificate' Table ![![-73, 50, 30, 48, -116]] 
 ![![619, 0, 0, 0, 0], ![0, 619, 0, 0, 0], ![414, 556, 1, 0, 0], ![42, 80, 0, 1, 0], ![600, 550, 0, 0, 1]] where
  M :=![![![-73, 50, 30, 48, -116], ![-304, 169, 150, 228, -512], ![-664, 814, -19, 396, -872], ![-252, 406, 22, -205, -156], ![-512, 524, 112, 184, -677]]]
  hmulB := by decide  
  f := ![![![-20995, 11362, 3046, 4640, -9988]], ![![-4880, 1319, 198, 276, -480]], ![![-18422, 8778, 2213, 3348, -7104]], ![![-2046, 934, 230, 347, -732]], ![![-24664, 12170, 3124, 4736, -10093]]]
  g := ![![![89, 70, 30, 48, -116], ![380, 291, 150, 228, -512], ![830, 742, -19, 396, -872], ![150, 146, 22, -205, -156], ![568, 478, 112, 184, -677]]]
  hle1 := by decide   
  hle2 := by decide  


def P619P1 : CertificateIrreducibleZModOfList' 619 2 2 9 [40, 360, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [259, 618], [0, 1]]
 g := ![![[9, 343], [35, 163], [309], [403, 611], [269], [499, 438], [191, 182], [229], [1]], ![[329, 276], [160, 456], [309], [188, 8], [269], [45, 181], [285, 437], [229], [1]]]
 h' := ![![[259, 618], [457, 427], [77, 120], [593, 144], [583, 43], [467, 58], [407, 189], [487, 213], [579, 259], [0, 1]], ![[0, 1], [249, 192], [207, 499], [130, 475], [578, 576], [14, 561], [457, 430], [563, 406], [189, 360], [259, 618]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [601]]
 b := ![[], [237, 610]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI619N1 : CertifiedPrimeIdeal' SI619N1 619 where
  n := 2
  hpos := by decide
  P := [40, 360, 1]
  hirr := P619P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-32802, -116755, 126508, 35474, -122493]
  a := ![83, -1, -76, -85, 170]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![31662, -9567, 126508, 35474, -122493]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI619N1 : Ideal.IsPrime I619N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI619N1 B_one_repr
lemma NI619N1 : Nat.card (O ⧸ I619N1) = 383161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI619N1
def MulI619N0 : IdealMulLeCertificate' Table 
  ![![20995, -11362, -3046, -4640, 9988]] ![![-73, 50, 30, 48, -116]]
  ![![619, 0, 0, 0, 0]] where
 M := ![![![-619, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC619 : ContainsPrimesAboveP 619 ![I619N0, I619N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI619N0
    exact isPrimeI619N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 619 (by decide) (𝕀 ⊙ MulI619N0)
instance hp631 : Fact (Nat.Prime 631) := {out := by norm_num}

def I631N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![631, 0, 0, 0, 0]] i)))

def SI631N0: IdealEqSpanCertificate' Table ![![631, 0, 0, 0, 0]] 
 ![![631, 0, 0, 0, 0], ![0, 631, 0, 0, 0], ![0, 0, 631, 0, 0], ![0, 0, 0, 631, 0], ![0, 0, 0, 0, 631]] where
  M :=![![![631, 0, 0, 0, 0], ![0, 631, 0, 0, 0], ![0, 0, 631, 0, 0], ![0, 0, 0, 631, 0], ![0, 0, 0, 0, 631]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P631P0 : CertificateIrreducibleZModOfList' 631 5 2 9 [141, 413, 162, 220, 283, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [41, 262, 200, 68, 231], [225, 451, 353, 118, 616], [31, 147, 356, 342, 365], [51, 401, 353, 103, 50], [0, 1]]
 g := ![![[398, 357, 223, 264, 616], [588, 539, 451, 238, 85], [611, 293, 353, 299, 394], [392, 481, 58, 77], [272, 321, 515, 463, 338], [198, 352, 469, 396, 484], [138, 384, 363, 348, 1], [], []], ![[425, 437, 196, 158, 398, 396, 77, 7], [480, 472, 613, 39, 476, 594, 366, 585], [543, 273, 162, 612, 294, 536, 513, 187], [308, 233, 268, 256], [52, 522, 321, 511, 610, 316, 278, 622], [23, 101, 82, 160, 387, 439, 319, 44], [598, 405, 576, 609, 494, 191, 141, 185], [344, 71, 124, 170], [238, 148, 426, 357]], ![[417, 125, 617, 21, 300, 130, 252, 202], [342, 626, 129, 179, 120, 122, 127, 18], [138, 10, 25, 606, 491, 256, 318, 194], [561, 21, 351, 124], [387, 170, 376, 116, 273, 262, 433, 458], [0, 268, 24, 539, 8, 69, 588, 576], [561, 593, 292, 50, 431, 225, 257, 183], [200, 198, 260, 133], [471, 247, 302, 225]], ![[390, 435, 200, 370, 32, 259, 577, 291], [231, 13, 418, 487, 215, 292, 90, 367], [70, 180, 548, 335, 256, 248, 312, 11], [482, 150, 417, 557], [266, 568, 54, 630, 163, 351, 461, 26], [589, 18, 215, 258, 302, 359, 187, 87], [157, 338, 209, 200, 484, 414, 452, 73], [495, 332, 178, 568], [240, 262, 621, 84]], ![[425, 438, 118, 346, 305, 218, 550, 349], [315, 427, 175, 588, 344, 326, 25, 78], [103, 263, 539, 460, 435, 5, 127, 78], [357, 573, 59, 330], [576, 502, 593, 131, 293, 72, 340, 337], [329, 194, 363, 356, 213, 78, 242, 62], [109, 501, 158, 116, 398, 298, 110, 525], [141, 405, 523, 538], [386, 288, 55, 607]]]
 h' := ![![[41, 262, 200, 68, 231], [384, 350, 347, 484, 123], [296, 15, 62, 187, 151], [16, 584, 215, 312, 164], [139, 522, 447, 307, 51], [477, 355, 130, 589, 591], [103, 549, 77, 598, 22], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[225, 451, 353, 118, 616], [219, 199, 324, 286, 603], [203, 122, 525, 563, 401], [511, 196, 504, 513, 11], [611, 458, 50, 15, 615], [350, 469, 626, 526, 410], [285, 154, 28, 386, 408], [373, 222, 605, 284, 90], [304, 127, 387, 220, 319], [41, 262, 200, 68, 231]], ![[31, 147, 356, 342, 365], [15, 118, 42, 254, 73], [542, 630, 481, 264, 167], [425, 309, 177, 112, 607], [193, 594, 334, 629, 131], [219, 380, 269, 296, 523], [619, 578, 348, 197, 308], [316, 187, 19, 194, 138], [620, 102, 12, 118, 190], [225, 451, 353, 118, 616]], ![[51, 401, 353, 103, 50], [626, 89, 250, 214, 5], [79, 453, 47, 97, 515], [535, 93, 359, 544, 452], [542, 276, 578, 485, 496], [607, 432, 16, 630, 121], [615, 200, 153, 135, 474], [318, 425, 208, 237, 461], [564, 514, 227, 194, 418], [31, 147, 356, 342, 365]], ![[0, 1], [144, 506, 299, 24, 458], [438, 42, 147, 151, 28], [593, 80, 7, 412, 28], [483, 43, 484, 457, 600], [44, 257, 221, 483, 248], [255, 412, 25, 577, 50], [259, 428, 430, 547, 572], [548, 519, 4, 99, 335], [51, 401, 353, 103, 50]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [192, 160, 87, 498], [], [], []]
 b := ![[], [494, 327, 211, 394, 383], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI631N0 : CertifiedPrimeIdeal' SI631N0 631 where
  n := 5
  hpos := by decide
  P := [141, 413, 162, 220, 283, 1]
  hirr := P631P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![130306799253253412, -18163215736619598, -97200253184353854, -140356837189323368, 260496106832402416]
  a := ![213, 9, -193, -208, 436]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![206508398182652, -28784810993058, -154041605680434, -222435558144728, 412830597198736]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI631N0 : Ideal.IsPrime I631N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI631N0 B_one_repr
lemma NI631N0 : Nat.card (O ⧸ I631N0) = 100033806792151 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI631N0

def PBC631 : ContainsPrimesAboveP 631 ![I631N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI631N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![631, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 631 (by decide) 𝕀

instance hp641 : Fact (Nat.Prime 641) := {out := by norm_num}

def I641N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6952, 1842, -7592, -7463, 15219]] i)))

def SI641N0: IdealEqSpanCertificate' Table ![![6952, 1842, -7592, -7463, 15219]] 
 ![![641, 0, 0, 0, 0], ![0, 641, 0, 0, 0], ![0, 0, 641, 0, 0], ![0, 0, 0, 641, 0], ![257, 152, 485, 53, 1]] where
  M :=![![![6952, 1842, -7592, -7463, 15219], ![-9066, -30785, 34176, 9394, -33058], ![-266612, 76956, 164835, 287636, -514436], ![900529, 509358, -1214806, -962658, 2096157], ![312104, 221210, -459242, -333116, 747301]]]
  hmulB := by decide  
  f := ![![![-3194, 3484, 1128, 1745, -3899]], ![![-4690, 5323, 1712, 2638, -5890]], ![![-7004, 8188, 2571, 3924, -8732]], ![![-2571, 3412, 942, 1360, -2963]], ![![-7909, 9142, 2883, 4409, -9817]]]
  g := ![![![-6091, -3606, -11527, -1270, 15219], ![13240, 7791, 25066, 2748, -33058], ![205840, 122108, 389495, 42984, -514436], ![-839020, -496266, -1587911, -174819, 2096157], ![-299133, -176862, -566147, -62309, 747301]]]
  hle1 := by decide   
  hle2 := by decide  


def P641P0 : CertificateIrreducibleZModOfList' 641 4 2 9 [305, 172, 415, 203, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [602, 226, 82, 352], [107, 39, 36, 103], [370, 375, 523, 186], [0, 1]]
 g := ![![[349, 307, 556, 511], [514, 474, 45], [379, 97, 93], [586, 166, 542], [612, 621, 241], [291, 591, 359], [208, 487, 338], [438, 1], []], ![[47, 613, 506, 255, 425, 159], [189, 514, 26], [237, 58, 154], [418, 450, 548], [589, 559, 28], [131, 485, 413], [91, 417, 98], [415, 188, 87, 82, 338, 26], [86, 366, 191]], ![[236, 328, 336, 638, 314, 146], [567, 328, 114], [496, 269, 623], [455, 379, 472], [332, 274, 296], [442, 146, 500], [556, 84, 399], [438, 316, 502, 594, 432, 323], [193, 498, 353]], ![[311, 532, 58, 193, 355, 356], [299, 529, 57], [231, 307, 445], [62, 371, 129], [471, 243, 564], [501, 166, 1], [95, 458, 289], [248, 566, 365, 373, 626, 639], [225, 141, 623]]]
 h' := ![![[602, 226, 82, 352], [634, 91, 309, 315], [128, 317, 496, 252], [109, 495, 568, 432], [0, 194, 144, 347], [351, 578, 111, 125], [76, 587, 297, 128], [379, 638, 102, 411], [0, 0, 1], [0, 1]], ![[107, 39, 36, 103], [31, 235, 368, 191], [225, 75, 126, 257], [243, 404, 592, 256], [85, 290, 565, 505], [577, 263, 87, 489], [467, 202, 584, 70], [440, 105, 46, 172], [290, 175, 599, 349], [602, 226, 82, 352]], ![[370, 375, 523, 186], [613, 370, 170, 183], [592, 21, 321, 394], [348, 386, 289, 186], [257, 15, 621, 79], [39, 382, 112, 424], [602, 126, 537, 442], [433, 303, 168, 41], [18, 176, 542, 325], [107, 39, 36, 103]], ![[0, 1], [208, 586, 435, 593], [593, 228, 339, 379], [276, 638, 474, 408], [445, 142, 593, 351], [61, 59, 331, 244], [486, 367, 505, 1], [129, 236, 325, 17], [329, 290, 140, 608], [370, 375, 523, 186]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [464, 563, 577], []]
 b := ![[], [], [211, 384, 110, 262], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI641N0 : CertifiedPrimeIdeal' SI641N0 641 where
  n := 4
  hpos := by decide
  P := [305, 172, 415, 203, 1]
  hirr := P641P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-13287765171263, 23316530089253, -8449402500134, 14562662038720, -16560079658441]
  a := ![253, 13, -232, -241, 518]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![6618802975114, 3963258405885, 12516675868711, 1391960817373, -16560079658441]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI641N0 : Ideal.IsPrime I641N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI641N0 B_one_repr
lemma NI641N0 : Nat.card (O ⧸ I641N0) = 168823196161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI641N0

def I641N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3194, 3484, 1128, 1745, -3899]] i)))

def SI641N1: IdealEqSpanCertificate' Table ![![-3194, 3484, 1128, 1745, -3899]] 
 ![![641, 0, 0, 0, 0], ![530, 1, 0, 0, 0], ![499, 0, 1, 0, 0], ![187, 0, 0, 1, 0], ![349, 0, 0, 0, 1]] where
  M :=![![![-3194, 3484, 1128, 1745, -3899], ![-4690, 5323, 1712, 2638, -5890], ![-7004, 8188, 2571, 3924, -8732], ![-2571, 3412, 942, 1360, -2963], ![-2728, 3522, 1022, 1508, -3315]]]
  hmulB := by decide  
  f := ![![![6952, 1842, -7592, -7463, 15219]], ![![5734, 1475, -6224, -6156, 12532]], ![![4996, 1554, -5653, -5361, 11045]], ![![3433, 1332, -4110, -3679, 7710]], ![![4272, 1348, -4850, -4583, 9452]]]
  g := ![![![-2150, 3484, 1128, 1745, -3899], ![-3304, 5323, 1712, 2638, -5890], ![-5173, 8188, 2571, 3924, -8732], ![-2342, 3412, 942, 1360, -2963], ![-2347, 3522, 1022, 1508, -3315]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI641N1 : Nat.card (O ⧸ I641N1) = 641 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI641N1)

lemma isPrimeI641N1 : Ideal.IsPrime I641N1 := prime_ideal_of_norm_prime hp641.out _ NI641N1
def MulI641N0 : IdealMulLeCertificate' Table 
  ![![6952, 1842, -7592, -7463, 15219]] ![![-3194, 3484, 1128, 1745, -3899]]
  ![![641, 0, 0, 0, 0]] where
 M := ![![![641, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC641 : ContainsPrimesAboveP 641 ![I641N0, I641N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI641N0
    exact isPrimeI641N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 641 (by decide) (𝕀 ⊙ MulI641N0)
instance hp643 : Fact (Nat.Prime 643) := {out := by norm_num}

def I643N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7979, -4736, -1318, -2016, 4376]] i)))

def SI643N0: IdealEqSpanCertificate' Table ![![7979, -4736, -1318, -2016, 4376]] 
 ![![643, 0, 0, 0, 0], ![0, 643, 0, 0, 0], ![0, 0, 643, 0, 0], ![133, 196, 238, 1, 0], ![358, 349, 313, 0, 1]] where
  M :=![![![7979, -4736, -1318, -2016, 4376], ![2848, -1747, -504, -764, 1664], ![1192, -848, -239, -400, 856], ![-1264, 522, 352, 439, -912], ![-4008, 2222, 698, 1020, -2197]]]
  hmulB := by decide  
  f := ![![![-519, 368, 198, 352, -824]], ![![-1696, 1207, 648, 1148, -2688]], ![![-5544, 3936, 2131, 3760, -8792]], ![![-2689, 1910, 1032, 1823, -4264]], ![![-3918, 2783, 1503, 2656, -6213]]]
  g := ![![![-2007, -1768, -1386, -2016, 4376], ![-764, -673, -528, -764, 1664], ![-392, -344, -269, -400, 856], ![415, 362, 282, 439, -912], ![1006, 885, 693, 1020, -2197]]]
  hle1 := by decide   
  hle2 := by decide  


def P643P0 : CertificateIrreducibleZModOfList' 643 3 2 9 [538, 124, 536, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [456, 470, 564], [294, 172, 79], [0, 1]]
 g := ![![[482, 99, 143], [232, 407, 228], [596, 626], [578, 129], [45, 60], [212, 314], [26, 385], [394, 107, 1], []], ![[28, 19, 252, 635], [321, 467, 357, 237], [556, 139], [468, 112], [464, 416], [508, 524], [499, 449], [319, 21, 479, 169], [38, 454]], ![[436, 573, 348, 639], [256, 313, 262, 466], [459, 247], [614, 150], [640, 53], [452, 95], [325, 230], [559, 566, 337, 80], [523, 454]]]
 h' := ![![[456, 470, 564], [569, 298, 214], [549, 24, 237], [123, 577, 84], [107, 70, 250], [110, 377, 238], [100, 81, 40], [218, 316, 60], [0, 0, 1], [0, 1]], ![[294, 172, 79], [229, 436, 406], [365, 243, 288], [577, 132, 372], [106, 413, 176], [523, 538, 222], [113, 362, 481], [517, 9, 145], [379, 279, 172], [456, 470, 564]], ![[0, 1], [555, 552, 23], [419, 376, 118], [498, 577, 187], [510, 160, 217], [130, 371, 183], [264, 200, 122], [420, 318, 438], [534, 364, 470], [294, 172, 79]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [497, 30], []]
 b := ![[], [388, 158, 212], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI643N0 : CertifiedPrimeIdeal' SI643N0 643 where
  n := 3
  hpos := by decide
  P := [538, 124, 536, 1]
  hirr := P643P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![81885537, -58818749, -21527206, -85301072, 140365893]
  a := ![67, 8, -61, -58, 137]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-60379567, -50276058, -36787553, -85301072, 140365893]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI643N0 : Ideal.IsPrime I643N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI643N0 B_one_repr
lemma NI643N0 : Nat.card (O ⧸ I643N0) = 265847707 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI643N0

def I643N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![80441, -47192, -13084, -20002, 43372]] i)))

def SI643N1: IdealEqSpanCertificate' Table ![![80441, -47192, -13084, -20002, 43372]] 
 ![![643, 0, 0, 0, 0], ![288, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![67, 0, 0, 1, 0], ![587, 0, 0, 0, 1]] where
  M :=![![![80441, -47192, -13084, -20002, 43372], ![27356, -16019, -4438, -6784, 14708], ![9232, -5358, -1479, -2260, 4896], ![-12178, 7178, 1994, 3049, -6614], ![-41448, 24358, 6758, 10332, -22407]]]
  hmulB := by decide  
  f := ![![![-1273, 1100, 320, 894, -1936]], ![![-572, 497, 142, 400, -868]], ![![-41, 2, 37, 34, -80]], ![![-215, 178, 54, 171, -338]], ![![-1209, 1034, 310, 858, -1847]]]
  g := ![![![-16187, -47192, -13084, -20002, 43372], ![-5482, -16019, -4438, -6784, 14708], ![-1813, -5358, -1479, -2260, 4896], ![2477, 7178, 1994, 3049, -6614], ![8373, 24358, 6758, 10332, -22407]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI643N1 : Nat.card (O ⧸ I643N1) = 643 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI643N1)

lemma isPrimeI643N1 : Ideal.IsPrime I643N1 := prime_ideal_of_norm_prime hp643.out _ NI643N1

def I643N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![861, -865, -5, -936, 1374]] i)))

def SI643N2: IdealEqSpanCertificate' Table ![![861, -865, -5, -936, 1374]] 
 ![![643, 0, 0, 0, 0], ![522, 1, 0, 0, 0], ![148, 0, 1, 0, 0], ![334, 0, 0, 1, 0], ![277, 0, 0, 0, 1]] where
  M :=![![![861, -865, -5, -936, 1374], ![-11832, -2390, 12281, 12698, -25536], ![22596, 51381, -63500, -23710, 70588], ![213886, -78261, -118103, -230941, 404998], ![90984, -21588, -60250, -98104, 177735]]]
  hmulB := by decide  
  f := ![![![-59709, -51729, -28303, -47168, 111750]], ![![-48078, -42452, -23151, -38574, 91364]], ![![-12728, -12893, -6904, -11498, 27188]], ![![-30016, -27703, -15067, -25121, 59478]], ![![-24731, -23093, -12525, -20876, 49417]]]
  g := ![![![599, -865, -5, -936, 1374], ![3500, -2390, 12281, 12698, -25536], ![-45154, 51381, -63500, -23710, 70588], ![36540, -78261, -118103, -230941, 404998], ![5927, -21588, -60250, -98104, 177735]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI643N2 : Nat.card (O ⧸ I643N2) = 643 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI643N2)

lemma isPrimeI643N2 : Ideal.IsPrime I643N2 := prime_ideal_of_norm_prime hp643.out _ NI643N2
def MulI643N0 : IdealMulLeCertificate' Table 
  ![![7979, -4736, -1318, -2016, 4376]] ![![80441, -47192, -13084, -20002, 43372]]
  ![![343287347, -201497380, -55876442, -85422206, 185235964]] where
 M := ![![![343287347, -201497380, -55876442, -85422206, 185235964]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI643N1 : IdealMulLeCertificate' Table 
  ![![343287347, -201497380, -55876442, -85422206, 185235964]] ![![861, -865, -5, -936, 1374]]
  ![![643, 0, 0, 0, 0]] where
 M := ![![![-1681445, 989577, 270703, 415378, -901486]]]
 hmul := by decide  
 g := ![![![![-2615, 1539, 421, 646, -1402]]]]
 hle2 := by decide  


def PBC643 : ContainsPrimesAboveP 643 ![I643N0, I643N1, I643N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI643N0
    exact isPrimeI643N1
    exact isPrimeI643N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 643 (by decide) (𝕀 ⊙ MulI643N0 ⊙ MulI643N1)


lemma PB2009I12_primes (p : ℕ) :
  p ∈ Set.range ![599, 601, 607, 613, 617, 619, 631, 641, 643] ↔ Nat.Prime p ∧ 593 < p ∧ p ≤ 643 := by
  rw [← List.mem_ofFn']
  convert primes_range 593 643 (by omega)

def PB2009I12 : PrimesBelowBoundCertificateInterval O 593 643 2009 where
  m := 9
  g := ![2, 3, 2, 3, 5, 2, 1, 2, 3]
  P := ![599, 601, 607, 613, 617, 619, 631, 641, 643]
  hP := PB2009I12_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I599N0, I599N1]
    · exact ![I601N0, I601N1, I601N2]
    · exact ![I607N0, I607N1]
    · exact ![I613N0, I613N1, I613N2]
    · exact ![I617N0, I617N1, I617N2, I617N3, I617N4]
    · exact ![I619N0, I619N1]
    · exact ![I631N0]
    · exact ![I641N0, I641N1]
    · exact ![I643N0, I643N1, I643N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC599
    · exact PBC601
    · exact PBC607
    · exact PBC613
    · exact PBC617
    · exact PBC619
    · exact PBC631
    · exact PBC641
    · exact PBC643
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![128738157601, 599]
    · exact ![217081801, 601, 601]
    · exact ![223648543, 368449]
    · exact ![375769, 375769, 613]
    · exact ![617, 617, 617, 617, 617]
    · exact ![237176659, 383161]
    · exact ![100033806792151]
    · exact ![168823196161, 641]
    · exact ![265847707, 643, 643]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI599N0
      exact NI599N1
    · dsimp ; intro j
      fin_cases j
      exact NI601N0
      exact NI601N1
      exact NI601N2
    · dsimp ; intro j
      fin_cases j
      exact NI607N0
      exact NI607N1
    · dsimp ; intro j
      fin_cases j
      exact NI613N0
      exact NI613N1
      exact NI613N2
    · dsimp ; intro j
      fin_cases j
      exact NI617N0
      exact NI617N1
      exact NI617N2
      exact NI617N3
      exact NI617N4
    · dsimp ; intro j
      fin_cases j
      exact NI619N0
      exact NI619N1
    · dsimp ; intro j
      fin_cases j
      exact NI631N0
    · dsimp ; intro j
      fin_cases j
      exact NI641N0
      exact NI641N1
    · dsimp ; intro j
      fin_cases j
      exact NI643N0
      exact NI643N1
      exact NI643N2
  β := ![I599N1, I601N1, I601N2, I613N2, I617N0, I617N1, I617N2, I617N3, I617N4, I641N1, I643N1, I643N2]
  Il := ![[I599N1], [I601N1, I601N2], [], [I613N2], [I617N0, I617N1, I617N2, I617N3, I617N4], [], [], [I641N1], [I643N1, I643N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
