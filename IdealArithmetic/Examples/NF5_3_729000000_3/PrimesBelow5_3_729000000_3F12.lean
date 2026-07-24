
import IdealArithmetic.Examples.NF5_3_729000000_3.RI5_3_729000000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp599 : Fact (Nat.Prime 599) := {out := by norm_num}

def I599N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![361, 514, 982, -225, -624]] i)))

def SI599N0: IdealEqSpanCertificate' Table ![![361, 514, 982, -225, -624]] 
 ![![599, 0, 0, 0, 0], ![0, 599, 0, 0, 0], ![0, 0, 599, 0, 0], ![397, 529, 184, 1, 0], ![342, 274, 533, 0, 1]] where
  M :=![![![361, 514, 982, -225, -624], ![2496, 2141, -2716, 3038, -2598], ![5196, 5526, -5653, -4455, 6516], ![-14280, -12270, 26432, -5975, -5550], ![-1892, -2920, 76, 8723, -8809]]]
  hmulB := by decide  
  f := ![![![-124585, -31168, 171418, 37739, 121038]], ![![-484152, -119765, 663892, 146320, 468510]], ![![-937020, -232320, 1285765, 283317, 907470]], ![![-800603, -198441, 1098482, 242056, 775278]], ![![-1128674, -279872, 1548807, 341274, 1093127]]]
  g := ![![![506, 485, 626, -225, -624], ![-526, -1491, 1374, 3038, -2598], ![-759, 963, -4439, -4455, 6516], ![7105, 7795, 6818, -5975, -5550], ![-755, -3679, 5159, 8723, -8809]]]
  hle1 := by decide   
  hle2 := by decide  


def P599P0 : CertificateIrreducibleZModOfList' 599 3 2 9 [360, 275, 493, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [44, 166, 221], [62, 432, 378], [0, 1]]
 g := ![![[326, 301, 434], [56, 519, 120], [28, 505, 254], [533, 402], [550, 109, 47], [148, 49], [145, 598, 294], [106, 1], []], ![[243, 60, 237, 450], [6, 82, 188, 48], [80, 593, 507, 431], [183, 242], [54, 597, 62, 373], [574, 152], [407, 480, 375, 250], [213, 335], [283, 322]], ![[374, 189, 335, 366], [310, 507, 70, 535], [506, 381, 507, 316], [556, 568], [35, 133, 118, 197], [265, 180], [223, 283, 486, 295], [184, 2], [126, 322]]]
 h' := ![![[44, 166, 221], [206, 49, 261], [103, 276, 489], [281, 237, 542], [269, 219, 559], [412, 29, 484], [512, 446, 592], [176, 440, 179], [0, 0, 1], [0, 1]], ![[62, 432, 378], [433, 535, 187], [61, 59, 298], [245, 63, 199], [355, 57, 570], [438, 568, 456], [345, 12, 301], [126, 107, 259], [89, 563, 432], [44, 166, 221]], ![[0, 1], [483, 15, 151], [427, 264, 411], [362, 299, 457], [282, 323, 69], [124, 2, 258], [108, 141, 305], [331, 52, 161], [414, 36, 166], [62, 432, 378]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [454, 393], []]
 b := ![[], [2, 583, 253], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI599N0 : CertifiedPrimeIdeal' SI599N0 599 where
  n := 3
  hpos := by decide
  P := [360, 275, 493, 1]
  hirr := P599P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1431388, -770559, 2643225, -1086769, 1008535]
  a := ![0, -8, -3, 2, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![142065, 497148, -559166, -1086769, 1008535]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI599N0 : Ideal.IsPrime I599N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI599N0 B_one_repr
lemma NI599N0 : Nat.card (O ⧸ I599N0) = 214921799 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI599N0

def I599N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![124585, 31168, -171418, -37739, -121038]] i)))

def SI599N1: IdealEqSpanCertificate' Table ![![124585, 31168, -171418, -37739, -121038]] 
 ![![599, 0, 0, 0, 0], ![0, 599, 0, 0, 0], ![166, 415, 1, 0, 0], ![594, 71, 0, 1, 0], ![63, 85, 0, 0, 1]] where
  M :=![![![124585, 31168, -171418, -37739, -121038], ![484152, 119765, -663892, -146320, -468510], ![937020, 232320, -1285765, -283317, -907470], ![1572864, 389898, -2158144, -475553, -1523166], ![1378348, 341702, -1891284, -416747, -1334827]]]
  hmulB := by decide  
  f := ![![![-361, -514, -982, 225, 624]], ![![-2496, -2141, 2716, -3038, 2598]], ![![-1838, -1635, 1619, -2035, 1962]], ![![-630, -743, -696, -127, 936]], ![![-389, -353, 282, -422, 449]]]
  g := ![![![97867, 140463, -171418, -37739, -121038], ![379166, 543985, -663892, -146320, -468510], ![734282, 1053548, -1285765, -283317, -907470], ![1232492, 1768369, -2158144, -475553, -1523166], ![1080089, 1549706, -1891284, -416747, -1334827]]]
  hle1 := by decide   
  hle2 := by decide  


def P599P1 : CertificateIrreducibleZModOfList' 599 2 2 9 [194, 386, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [213, 598], [0, 1]]
 g := ![![[249, 10], [229, 456], [345, 543], [48], [119, 90], [150], [134, 308], [444], [1]], ![[582, 589], [319, 143], [397, 56], [48], [121, 509], [150], [447, 291], [444], [1]]]
 h' := ![![[213, 598], [499, 252], [158, 317], [423, 331], [275, 153], [467, 442], [360, 299], [19, 547], [405, 213], [0, 1]], ![[0, 1], [265, 347], [591, 282], [244, 268], [518, 446], [570, 157], [553, 300], [324, 52], [250, 386], [213, 598]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [166]]
 b := ![[], [445, 83]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI599N1 : CertifiedPrimeIdeal' SI599N1 599 where
  n := 2
  hpos := by decide
  P := [194, 386, 1]
  hirr := P599P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2825, -5493, -29416, 63157, 351]
  a := ![3, -61, 2, -69, 11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-54510, 12835, -29416, 63157, 351]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI599N1 : Ideal.IsPrime I599N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI599N1 B_one_repr
lemma NI599N1 : Nat.card (O ⧸ I599N1) = 358801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI599N1
def MulI599N0 : IdealMulLeCertificate' Table 
  ![![361, 514, 982, -225, -624]] ![![124585, 31168, -171418, -37739, -121038]]
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

def I601N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-29, -7, 52, -195, 192]] i)))

def SI601N0: IdealEqSpanCertificate' Table ![![-29, -7, 52, -195, 192]] 
 ![![601, 0, 0, 0, 0], ![0, 601, 0, 0, 0], ![255, 290, 1, 0, 0], ![574, 168, 0, 1, 0], ![135, 139, 0, 0, 1]] where
  M :=![![![-29, -7, 52, -195, 192], ![-768, -751, 1138, 302, -786], ![1572, 1273, -3109, 1229, 120], ![144, 716, 1064, -4549, 4200], ![-2496, -2226, 4414, -446, -1487]]]
  hmulB := by decide  
  f := ![![![7999003, -4819865, 339854, -724233, 1562358]], ![![-6249432, 3765675, -265582, 565816, -1220682]], ![![382449, -230434, 16219, -34632, 74676]], ![![5896330, -3552874, 250500, -533859, 1151652]], ![![355605, -214266, 15094, -32199, 69445]]]
  g := ![![![121, -15, 52, -195, 192], ![-596, -453, 1138, 302, -786], ![121, 1131, -3109, 1229, 120], ![2950, -212, 1064, -4549, 4200], ![-1117, -1665, 4414, -446, -1487]]]
  hle1 := by decide   
  hle2 := by decide  


def P601P0 : CertificateIrreducibleZModOfList' 601 2 2 9 [165, 28, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [573, 600], [0, 1]]
 g := ![![[226, 400], [554], [463], [365, 409], [239, 180], [599], [359, 468], [183], [1]], ![[445, 201], [554], [463], [332, 192], [7, 421], [599], [477, 133], [183], [1]]]
 h' := ![![[573, 600], [496, 20], [532, 532], [476, 297], [231, 209], [310, 436], [264, 497], [35, 510], [436, 573], [0, 1]], ![[0, 1], [537, 581], [60, 69], [574, 304], [389, 392], [122, 165], [171, 104], [179, 91], [18, 28], [573, 600]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [252]]
 b := ![[], [562, 126]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI601N0 : CertifiedPrimeIdeal' SI601N0 601 where
  n := 2
  hpos := by decide
  P := [165, 28, 1]
  hirr := P601P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-358, -112, 787, -164, 1020]
  a := ![1, -6, -1, -3, -6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-407, -570, 787, -164, 1020]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI601N0 : Ideal.IsPrime I601N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI601N0 B_one_repr
lemma NI601N0 : Nat.card (O ⧸ I601N0) = 361201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI601N0

def I601N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-163, 27, -6, 194, -212]] i)))

def SI601N1: IdealEqSpanCertificate' Table ![![-163, 27, -6, 194, -212]] 
 ![![601, 0, 0, 0, 0], ![0, 601, 0, 0, 0], ![486, 466, 1, 0, 0], ![101, 349, 0, 1, 0], ![190, 513, 0, 0, 1]] where
  M :=![![![-163, 27, -6, 194, -212], ![848, 643, -1218, -188, 740], ![-1480, -1113, 2863, -1400, 176], ![-776, -1206, 24, 4269, -4394], ![2388, 2146, -4382, 803, 1093]]]
  hmulB := by decide  
  f := ![![![-774915, -192149, 1063060, 234246, 750308]], ![![-3001232, -743979, 4117550, 907320, 2906092]], ![![-2963386, -734641, 4065557, 895860, 2869412]], ![![-1889271, -468342, 2591978, 571153, 1829374]], ![![-2820990, -699315, 3870240, 852823, 2731551]]]
  g := ![![![39, 73, -6, 194, -212], ![784, 423, -1218, -188, 740], ![-2138, -1559, 2863, -1400, 176], ![651, 1251, 24, 4269, -4394], ![3067, 2002, -4382, 803, 1093]]]
  hle1 := by decide   
  hle2 := by decide  


def P601P1 : CertificateIrreducibleZModOfList' 601 2 2 9 [204, 418, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [183, 600], [0, 1]]
 g := ![![[114, 20], [281], [281], [154, 341], [366, 207], [500], [132, 96], [434], [1]], ![[168, 581], [281], [281], [53, 260], [384, 394], [500], [271, 505], [434], [1]]]
 h' := ![![[183, 600], [218, 546], [223, 146], [437, 455], [461, 203], [36, 105], [117, 326], [559, 551], [397, 183], [0, 1]], ![[0, 1], [370, 55], [497, 455], [163, 146], [348, 398], [19, 496], [276, 275], [424, 50], [230, 418], [183, 600]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [472]]
 b := ![[], [42, 236]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI601N1 : CertifiedPrimeIdeal' SI601N1 601 where
  n := 2
  hpos := by decide
  P := [204, 418, 1]
  hirr := P601P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8249, 11093, 15486, 2467, 26605]
  a := ![1, 26, 4, 10, 23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-21362, -36131, 15486, 2467, 26605]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI601N1 : Ideal.IsPrime I601N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI601N1 B_one_repr
lemma NI601N1 : Nat.card (O ⧸ I601N1) = 361201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI601N1

def I601N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 7, 2, -9, 6]] i)))

def SI601N2: IdealEqSpanCertificate' Table ![![5, 7, 2, -9, 6]] 
 ![![601, 0, 0, 0, 0], ![291, 1, 0, 0, 0], ![30, 0, 1, 0, 0], ![598, 0, 0, 1, 0], ![348, 0, 0, 0, 1]] where
  M :=![![![5, 7, 2, -9, 6], ![-24, -23, 50, 16, -42], ![84, 71, -149, 55, 6], ![0, 28, 64, -215, 192], ![-120, -108, 206, -16, -73]]]
  hmulB := by decide  
  f := ![![![-17203, -3427, 22252, 5001, 15540]], ![![-8433, -1686, 10918, 2453, 7626]], ![![-1062, -221, 1389, 311, 972]], ![![-17458, -3494, 22608, 5079, 15792]], ![![-10260, -2058, 13294, 2986, 9287]]]
  g := ![![![2, 7, 2, -9, 6], ![17, -23, 50, 16, -42], ![-85, 71, -149, 55, 6], ![86, 28, 64, -215, 192], ![100, -108, 206, -16, -73]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI601N2 : Nat.card (O ⧸ I601N2) = 601 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI601N2)

lemma isPrimeI601N2 : Ideal.IsPrime I601N2 := prime_ideal_of_norm_prime hp601.out _ NI601N2
def MulI601N0 : IdealMulLeCertificate' Table 
  ![![-29, -7, 52, -195, 192]] ![![-163, 27, -6, 194, -212]]
  ![![531647, 584042, -688448, -755389, 1076806]] where
 M := ![![![531647, 584042, -688448, -755389, 1076806]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI601N1 : IdealMulLeCertificate' Table 
  ![![531647, 584042, -688448, -755389, 1076806]] ![![5, 7, 2, -9, 6]]
  ![![601, 0, 0, 0, 0]] where
 M := ![![![-198405125, -196037185, 306321286, 111874948, -249112096]]]
 hmul := by decide  
 g := ![![![![-330125, -326185, 509686, 186148, -414496]]]]
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

def I607N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-683, -753, 112, -49, 306]] i)))

def SI607N0: IdealEqSpanCertificate' Table ![![-683, -753, 112, -49, 306]] 
 ![![607, 0, 0, 0, 0], ![0, 607, 0, 0, 0], ![420, 598, 1, 0, 0], ![138, 433, 0, 1, 0], ![126, 455, 0, 0, 1]] where
  M :=![![![-683, -753, 112, -49, 306], ![-1224, -1281, 330, 16, 318], ![-636, -749, -327, 155, 366], ![-120, -52, 184, -673, 672], ![-80, -28, 606, -56, -331]]]
  hmulB := by decide  
  f := ![![![-1907333, -472729, 2616938, 576659, 1846956]], ![![-7387824, -1830989, 10136278, 2233602, 7153866]], ![![-8621592, -2136777, 11829059, 2606617, 8348580]], ![![-5743254, -1423405, 7879894, 1736391, 5561382]], ![![-5968418, -1479209, 8188824, 1804466, 5779415]]]
  g := ![![![-131, -306, 112, -49, 306], ![-300, -577, 330, 16, 318], ![114, -64, -327, 155, 366], ![-114, -205, 184, -673, 672], ![-338, -309, 606, -56, -331]]]
  hle1 := by decide   
  hle2 := by decide  


def P607P0 : CertificateIrreducibleZModOfList' 607 2 2 9 [415, 518, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [89, 606], [0, 1]]
 g := ![![[383, 98], [522, 151], [194, 488], [243, 7], [132, 100], [49], [360, 590], [30], [1]], ![[0, 509], [0, 456], [529, 119], [259, 600], [534, 507], [49], [61, 17], [30], [1]]]
 h' := ![![[89, 606], [69, 463], [221, 93], [524, 553], [457, 325], [317, 597], [529, 600], [134, 426], [192, 89], [0, 1]], ![[0, 1], [0, 144], [0, 514], [574, 54], [246, 282], [34, 10], [513, 7], [414, 181], [222, 518], [89, 606]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [286]]
 b := ![[], [10, 143]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI607N0 : CertifiedPrimeIdeal' SI607N0 607 where
  n := 2
  hpos := by decide
  P := [415, 518, 1]
  hirr := P607P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8454, -10233, 11142, 9331, -19129]
  a := ![-1, -6, -4, 13, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5874, -3311, 11142, 9331, -19129]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI607N0 : Ideal.IsPrime I607N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI607N0 B_one_repr
lemma NI607N0 : Nat.card (O ⧸ I607N0) = 368449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI607N0

def I607N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-133, 19, 182, 45, 114]] i)))

def SI607N1: IdealEqSpanCertificate' Table ![![-133, 19, 182, 45, 114]] 
 ![![607, 0, 0, 0, 0], ![149, 1, 0, 0, 0], ![129, 0, 1, 0, 0], ![27, 0, 0, 1, 0], ![604, 0, 0, 0, 1]] where
  M :=![![![-133, 19, 182, 45, 114], ![-456, -89, 722, 160, 498], ![-996, -205, 1405, 313, 978], ![-1728, -416, 2368, 523, 1668], ![-1536, -384, 2078, 458, 1469]]]
  hmulB := by decide  
  f := ![![![-2779, -2605, 4564, 585, -2604]], ![![-665, -626, 1086, 161, -642]], ![![-585, -542, 975, 74, -504]], ![![-231, -217, 380, 48, -216]], ![![-2740, -2578, 4478, 652, -2635]]]
  g := ![![![-159, 19, 182, 45, 114], ![-635, -89, 722, 160, 498], ![-1237, -205, 1405, 313, 978], ![-2087, -416, 2368, 523, 1668], ![-1832, -384, 2078, 458, 1469]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI607N1 : Nat.card (O ⧸ I607N1) = 607 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI607N1)

lemma isPrimeI607N1 : Ideal.IsPrime I607N1 := prime_ideal_of_norm_prime hp607.out _ NI607N1

def I607N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-147, -157, 22, -4, 58]] i)))

def SI607N2: IdealEqSpanCertificate' Table ![![-147, -157, 22, -4, 58]] 
 ![![607, 0, 0, 0, 0], ![520, 1, 0, 0, 0], ![161, 0, 1, 0, 0], ![370, 0, 0, 1, 0], ![459, 0, 0, 0, 1]] where
  M :=![![![-147, -157, 22, -4, 58], ![-232, -249, 34, -6, 92], ![-184, -197, 27, -6, 74], ![-32, -34, 8, -1, 10], ![60, 64, -10, 3, -25]]]
  hmulB := by decide  
  f := ![![![-917, 609, -128, 68, -238]], ![![-784, 521, -110, 58, -204]], ![![-243, 162, -35, 18, -64]], ![![-558, 372, -80, 41, -146]], ![![-693, 461, -98, 51, -181]]]
  g := ![![![87, -157, 22, -4, 58], ![138, -249, 34, -6, 92], ![109, -197, 27, -6, 74], ![20, -34, 8, -1, 10], ![-35, 64, -10, 3, -25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI607N2 : Nat.card (O ⧸ I607N2) = 607 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI607N2)

lemma isPrimeI607N2 : Ideal.IsPrime I607N2 := prime_ideal_of_norm_prime hp607.out _ NI607N2

def I607N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1045, -259, 1434, 316, 1012]] i)))

def SI607N3: IdealEqSpanCertificate' Table ![![-1045, -259, 1434, 316, 1012]] 
 ![![607, 0, 0, 0, 0], ![563, 1, 0, 0, 0], ![246, 0, 1, 0, 0], ![578, 0, 0, 1, 0], ![197, 0, 0, 0, 1]] where
  M :=![![![-1045, -259, 1434, 316, 1012], ![-4048, -1003, 5554, 1224, 3920], ![-7840, -1943, 10757, 2370, 7592], ![-13160, -3262, 18056, 3979, 12742], ![-11532, -2858, 15822, 3487, 11167]]]
  hmulB := by decide  
  f := ![![![4221, -1021, -32, -272, 308]], ![![3913, -942, -30, -252, 284]], ![![1714, -413, -13, -110, 124]], ![![4022, -972, -32, -259, 294]], ![![1371, -333, -10, -89, 101]]]
  g := ![![![-972, -259, 1434, 316, 1012], ![-3765, -1003, 5554, 1224, 3920], ![-7291, -1943, 10757, 2370, 7592], ![-12238, -3262, 18056, 3979, 12742], ![-10725, -2858, 15822, 3487, 11167]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI607N3 : Nat.card (O ⧸ I607N3) = 607 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI607N3)

lemma isPrimeI607N3 : Ideal.IsPrime I607N3 := prime_ideal_of_norm_prime hp607.out _ NI607N3
def MulI607N0 : IdealMulLeCertificate' Table 
  ![![-683, -753, 112, -49, 306]] ![![-133, 19, 182, 45, 114]]
  ![![-62689, -66040, 9224, -1638, 24462]] where
 M := ![![![-62689, -66040, 9224, -1638, 24462]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI607N1 : IdealMulLeCertificate' Table 
  ![![-62689, -66040, 9224, -1638, 24462]] ![![-147, -157, 22, -4, 58]]
  ![![24359483, 26090265, -3633194, 666676, -9656996]] where
 M := ![![![24359483, 26090265, -3633194, 666676, -9656996]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI607N2 : IdealMulLeCertificate' Table 
  ![![24359483, 26090265, -3633194, 666676, -9656996]] ![![-1045, -259, 1434, 316, 1012]]
  ![![607, 0, 0, 0, 0]] where
 M := ![![![6210217, 6651506, -926282, 169960, -2461992]]]
 hmul := by decide  
 g := ![![![![10231, 10958, -1526, 280, -4056]]]]
 hle2 := by decide  


def PBC607 : ContainsPrimesAboveP 607 ![I607N0, I607N1, I607N2, I607N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI607N0
    exact isPrimeI607N1
    exact isPrimeI607N2
    exact isPrimeI607N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 607 (by decide) (𝕀 ⊙ MulI607N0 ⊙ MulI607N1 ⊙ MulI607N2)
instance hp613 : Fact (Nat.Prime 613) := {out := by norm_num}

def I613N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2531, -2708, 368, -71, 996]] i)))

def SI613N0: IdealEqSpanCertificate' Table ![![-2531, -2708, 368, -71, 996]] 
 ![![613, 0, 0, 0, 0], ![0, 613, 0, 0, 0], ![0, 0, 613, 0, 0], ![536, 34, 18, 1, 0], ![232, 513, 318, 0, 1]] where
  M :=![![![-2531, -2708, 368, -71, 996], ![-3984, -4297, 560, -118, 1566], ![-3132, -3396, 401, -105, 1212], ![-432, -534, -40, -41, 114], ![1108, 1124, -264, 7, -487]]]
  hmulB := by decide  
  f := ![![![-47, 34, -8, 3, -6]], ![![24, -37, 32, -16, 6]], ![![-12, 6, -19, 45, -42]], ![![-40, 28, -6, 3, -6]], ![![-4, -15, 14, 11, -19]]]
  g := ![![![-319, -834, -514, -71, 996], ![-496, -1311, -808, -118, 1566], ![-372, -1014, -625, -105, 1212], ![-8, -94, -58, -41, 114], ![180, 409, 252, 7, -487]]]
  hle1 := by decide   
  hle2 := by decide  


def P613P0 : CertificateIrreducibleZModOfList' 613 3 2 9 [54, 307, 88, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [242, 466, 446], [283, 146, 167], [0, 1]]
 g := ![![[495, 107, 323], [230, 466], [137, 260, 141], [406, 601], [557, 196], [383, 62, 118], [310, 297, 431], [525, 1], []], ![[367, 468, 120, 196], [484, 416], [206, 370, 101, 68], [196, 356], [66, 218], [185, 34, 586, 141], [15, 258, 494, 464], [610, 474], [278, 304]], ![[323, 231, 304, 64], [552, 564], [486, 318, 501, 295], [511, 567], [334, 252], [488, 610, 146, 239], [313, 548, 75, 612], [484, 154], [557, 304]]]
 h' := ![![[242, 466, 446], [378, 85, 395], [571, 457, 304], [172, 201, 184], [426, 158, 351], [160, 612, 599], [424, 168, 458], [461, 603, 81], [0, 0, 1], [0, 1]], ![[283, 146, 167], [527, 162, 565], [446, 361, 554], [206, 363, 40], [414, 562, 340], [125, 150, 575], [418, 514, 193], [390, 358, 10], [29, 569, 146], [242, 466, 446]], ![[0, 1], [333, 366, 266], [277, 408, 368], [327, 49, 389], [384, 506, 535], [382, 464, 52], [447, 544, 575], [270, 265, 522], [358, 44, 466], [283, 146, 167]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [304, 532], []]
 b := ![[], [264, 493, 139], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI613N0 : CertifiedPrimeIdeal' SI613N0 613 where
  n := 3
  hpos := by decide
  P := [54, 307, 88, 1]
  hirr := P613P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7244470, 7351650, -10746516, -5576006, 10438730]
  a := ![0, -2, 4, -26, 22]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![936702, -8414572, -5268996, -5576006, 10438730]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI613N0 : Ideal.IsPrime I613N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI613N0 B_one_repr
lemma NI613N0 : Nat.card (O ⧸ I613N0) = 230346397 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI613N0

def I613N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![363, -202, 12, -32, 64]] i)))

def SI613N1: IdealEqSpanCertificate' Table ![![363, -202, 12, -32, 64]] 
 ![![613, 0, 0, 0, 0], ![70, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![508, 0, 0, 1, 0], ![145, 0, 0, 0, 1]] where
  M :=![![![363, -202, 12, -32, 64], ![-256, 183, -20, 24, -64], ![128, -50, -9, -12, 8], ![112, -52, -16, -13, 4], ![120, -68, -12, -14, 11]]]
  hmulB := by decide  
  f := ![![![-401, -318, 812, -384, 32]], ![![-46, -37, 92, -40, 0]], ![![6, 6, -9, -4, 8]], ![![-348, -276, 704, -333, 28]], ![![-101, -82, 200, -82, -5]]]
  g := ![![![35, -202, 12, -32, 64], ![-26, 183, -20, 24, -64], ![14, -50, -9, -12, 8], ![16, -52, -16, -13, 4], ![17, -68, -12, -14, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI613N1 : Nat.card (O ⧸ I613N1) = 613 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI613N1)

lemma isPrimeI613N1 : Ideal.IsPrime I613N1 := prime_ideal_of_norm_prime hp613.out _ NI613N1

def I613N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![35, 38, -2, -1, -14]] i)))

def SI613N2: IdealEqSpanCertificate' Table ![![35, 38, -2, -1, -14]] 
 ![![613, 0, 0, 0, 0], ![507, 1, 0, 0, 0], ![512, 0, 1, 0, 0], ![217, 0, 0, 1, 0], ![59, 0, 0, 0, 1]] where
  M :=![![![35, 38, -2, -1, -14], ![56, 59, -8, 12, -34], ![68, 70, -43, -3, 2], ![-32, -22, 80, -47, 10], ![-36, -38, 32, 21, -29]]]
  hmulB := by decide  
  f := ![![![34239, -20824, 1782, -3051, 6956]], ![![28273, -17197, 1474, -2519, 5746]], ![![28612, -17404, 1493, -2549, 5816]], ![![12131, -7382, 638, -1080, 2470]], ![![3309, -2016, 178, -294, 677]]]
  g := ![![![-28, 38, -2, -1, -14], ![-43, 59, -8, 12, -34], ![-21, 70, -43, -3, 2], ![-33, -22, 80, -47, 10], ![0, -38, 32, 21, -29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI613N2 : Nat.card (O ⧸ I613N2) = 613 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI613N2)

lemma isPrimeI613N2 : Ideal.IsPrime I613N2 := prime_ideal_of_norm_prime hp613.out _ NI613N2
def MulI613N0 : IdealMulLeCertificate' Table 
  ![![-2531, -2708, 368, -71, 996]] ![![363, -202, 12, -32, 64]]
  ![![-66833, -66738, 9660, -1437, 24944]] where
 M := ![![![-66833, -66738, 9660, -1437, 24944]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI613N1 : IdealMulLeCertificate' Table 
  ![![-66833, -66738, 9660, -1437, 24944]] ![![35, 38, -2, -1, -14]]
  ![![613, 0, 0, 0, 0]] where
 M := ![![![-6271603, -6717254, 935438, -171640, 2486328]]]
 hmul := by decide  
 g := ![![![![-10231, -10958, 1526, -280, 4056]]]]
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

def I617N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-505, -424, 948, -298, -110]] i)))

def SI617N0: IdealEqSpanCertificate' Table ![![-505, -424, 948, -298, -110]] 
 ![![617, 0, 0, 0, 0], ![0, 617, 0, 0, 0], ![124, 416, 1, 0, 0], ![244, 75, 0, 1, 0], ![272, 155, 0, 0, 1]] where
  M :=![![![-505, -424, 948, -298, -110], ![440, 67, -1508, 2602, -2008], ![4016, 4076, -5957, -3106, 5798], ![-11816, -9908, 22224, -7051, -2516], ![-2408, -3102, 2092, 6960, -8059]]]
  hmulB := by decide  
  f := ![![![-732177, 440932, -31100, 66270, -142934]], ![![571736, -344869, 24260, -51806, 111752]], ![![237972, -143688, 10091, -21578, 46550]], ![![-220372, 132645, -9364, 19939, -43004]], ![![-179520, 107971, -7632, 16234, -35011]]]
  g := ![![![-25, -576, 948, -298, -110], ![160, 1205, -1508, 2602, -2008], ![-124, 2944, -5957, -3106, 5798], ![-588, -13511, 22224, -7051, -2516], ![376, -237, 2092, 6960, -8059]]]
  hle1 := by decide   
  hle2 := by decide  


def P617P0 : CertificateIrreducibleZModOfList' 617 2 2 9 [548, 157, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [460, 616], [0, 1]]
 g := ![![[418, 152], [15], [334], [137, 305], [242], [420, 288], [466, 473], [586], [1]], ![[0, 465], [15], [334], [378, 312], [242], [245, 329], [245, 144], [586], [1]]]
 h' := ![![[460, 616], [588, 326], [550, 399], [198, 350], [400, 549], [598, 171], [70, 467], [154, 477], [69, 460], [0, 1]], ![[0, 1], [0, 291], [224, 218], [161, 267], [587, 68], [282, 446], [174, 150], [539, 140], [38, 157], [460, 616]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [345]]
 b := ![[], [430, 481]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI617N0 : CertifiedPrimeIdeal' SI617N0 617 where
  n := 2
  hpos := by decide
  P := [548, 157, 1]
  hirr := P617P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2138, -4923, 7370, 2121, -5656]
  a := ![13, -6, -3, 8, -19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![170, -3814, 7370, 2121, -5656]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI617N0 : Ideal.IsPrime I617N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI617N0 B_one_repr
lemma NI617N0 : Nat.card (O ⧸ I617N0) = 380689 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI617N0

def I617N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-77, -81, 14, 0, 30]] i)))

def SI617N1: IdealEqSpanCertificate' Table ![![-77, -81, 14, 0, 30]] 
 ![![617, 0, 0, 0, 0], ![0, 617, 0, 0, 0], ![60, 612, 1, 0, 0], ![300, 314, 0, 1, 0], ![607, 267, 0, 0, 1]] where
  M :=![![![-77, -81, 14, 0, 30], ![-120, -123, 18, -2, 60], ![-120, -113, 57, -10, 54], ![-48, -34, 40, 41, -6], ![28, 44, -10, 15, 17]]]
  hmulB := by decide  
  f := ![![![17411, -10493, 740, -1576, 3402]], ![![-13608, 8195, -574, 1230, -2652]], ![![-11796, 7103, -497, 1066, -2298]], ![![1548, -936, 68, -141, 306]], ![![11249, -6782, 480, -1019, 2201]]]
  g := ![![![-31, -27, 14, 0, 30], ![-60, -43, 18, -2, 60], ![-54, -75, 57, -10, 54], ![-18, -58, 40, 41, -6], ![-23, -5, -10, 15, 17]]]
  hle1 := by decide   
  hle2 := by decide  


def P617P1 : CertificateIrreducibleZModOfList' 617 2 2 9 [262, 606, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 616], [0, 1]]
 g := ![![[186, 130], [287], [270], [345, 265], [224], [531, 9], [320, 39], [121], [1]], ![[382, 487], [287], [270], [175, 352], [224], [13, 608], [132, 578], [121], [1]]]
 h' := ![![[11, 616], [99, 511], [61, 39], [309, 154], [522, 46], [320, 29], [72, 3], [539, 503], [355, 11], [0, 1]], ![[0, 1], [167, 106], [490, 578], [152, 463], [411, 571], [22, 588], [105, 614], [519, 114], [476, 606], [11, 616]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [414]]
 b := ![[], [404, 207]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI617N1 : CertifiedPrimeIdeal' SI617N1 617 where
  n := 2
  hpos := by decide
  P := [262, 606, 1]
  hirr := P617P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1807, -1467, 3338, -3565, 4513]
  a := ![-1, 0, 2, -8, 11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3034, -3452, 3338, -3565, 4513]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI617N1 : Ideal.IsPrime I617N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI617N1 B_one_repr
lemma NI617N1 : Nat.card (O ⧸ I617N1) = 380689 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI617N1

def I617N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 11, -20, 2, 10]] i)))

def SI617N2: IdealEqSpanCertificate' Table ![![11, 11, -20, 2, 10]] 
 ![![617, 0, 0, 0, 0], ![412, 1, 0, 0, 0], ![274, 0, 1, 0, 0], ![114, 0, 0, 1, 0], ![505, 0, 0, 0, 1]] where
  M :=![![![11, 11, -20, 2, 10], ![-40, -25, 82, -54, 32], ![-64, -65, 71, 120, -130], ![280, 266, -496, 43, 214], ![-36, 4, 110, -183, 175]]]
  hmulB := by decide  
  f := ![![![1311099, -791081, 55830, -118782, 256462]], ![![873820, -527243, 37210, -79166, 170928]], ![![582886, -351699, 24821, -52808, 114018]], ![![242822, -146512, 10340, -21999, 47498]], ![![1073775, -647885, 45724, -97281, 210039]]]
  g := ![![![-7, 11, -20, 2, 10], ![-36, -25, 82, -54, 32], ![96, -65, 71, 120, -130], ![-140, 266, -496, 43, 214], ![-161, 4, 110, -183, 175]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI617N2 : Nat.card (O ⧸ I617N2) = 617 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI617N2)

lemma isPrimeI617N2 : Ideal.IsPrime I617N2 := prime_ideal_of_norm_prime hp617.out _ NI617N2
def MulI617N0 : IdealMulLeCertificate' Table 
  ![![-505, -424, 948, -298, -110]] ![![-77, -81, 14, 0, 30]]
  ![![-12771, -8775, 28514, -22500, 10520]] where
 M := ![![![-12771, -8775, 28514, -22500, 10520]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI617N1 : IdealMulLeCertificate' Table 
  ![![-12771, -8775, 28514, -22500, 10520]] ![![11, 11, -20, 2, 10]]
  ![![617, 0, 0, 0, 0]] where
 M := ![![![-8293097, -7717436, 13877564, 977328, -7089330]]]
 hmul := by decide  
 g := ![![![![-13441, -12508, 22492, 1584, -11490]]]]
 hle2 := by decide  


def PBC617 : ContainsPrimesAboveP 617 ![I617N0, I617N1, I617N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI617N0
    exact isPrimeI617N1
    exact isPrimeI617N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 617 (by decide) (𝕀 ⊙ MulI617N0 ⊙ MulI617N1)
instance hp619 : Fact (Nat.Prime 619) := {out := by norm_num}

def I619N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-12773, -1844, 19420, 4377, 13242]] i)))

def SI619N0: IdealEqSpanCertificate' Table ![![-12773, -1844, 19420, 4377, 13242]] 
 ![![619, 0, 0, 0, 0], ![0, 619, 0, 0, 0], ![0, 0, 619, 0, 0], ![537, 300, 67, 1, 0], ![566, 310, 483, 0, 1]] where
  M :=![![![-12773, -1844, 19420, 4377, 13242], ![-52968, -11083, 75764, 16844, 52746], ![-105492, -24504, 147155, 32547, 103278], ![-180072, -44358, 247448, 54547, 174546], ![-158732, -39862, 216988, 47777, 153329]]]
  hmulB := by decide  
  f := ![![![265, 274, -436, -119, 312]], ![![-1248, -1033, 2420, -946, -90]], ![![180, -270, -1303, 3411, -2928]], ![![-345, -282, 637, -197, -78]], ![![-246, -480, -195, 2072, -2041]]]
  g := ![![![-15926, -8756, -10775, 4377, 13242], ![-62928, -34597, -42858, 16844, 52746], ![-122841, -67536, -83872, 32547, 103278], ![-207213, -113922, -141701, 54547, 174546], ![-181905, -100008, -124462, 47777, 153329]]]
  hle1 := by decide   
  hle2 := by decide  


def P619P0 : CertificateIrreducibleZModOfList' 619 3 2 9 [613, 491, 114, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 602, 300], [491, 16, 319], [0, 1]]
 g := ![![[415, 173, 343], [120, 268, 524], [313, 352], [184, 447, 39], [388, 81], [558, 398, 109], [290, 261, 150], [505, 1], []], ![[613, 91, 602, 14], [459, 53, 135, 584], [113, 600], [609, 177, 325, 12], [445, 209], [352, 448, 119, 391], [245, 319, 471, 153], [177, 256], [248, 245]], ![[76, 37, 81, 100], [567, 232, 441, 544], [125, 355], [202, 581, 288, 362], [147, 609], [293, 18, 240, 209], [186, 75, 53, 151], [610, 289], [229, 245]]]
 h' := ![![[14, 602, 300], [101, 312, 427], [26, 63, 545], [485, 529, 47], [104, 304, 343], [253, 222, 610], [502, 200, 193], [554, 270, 125], [0, 0, 1], [0, 1]], ![[491, 16, 319], [545, 516, 154], [92, 321, 384], [379, 144, 369], [112, 258, 124], [585, 561, 223], [244, 615, 569], [41, 403, 54], [446, 550, 16], [14, 602, 300]], ![[0, 1], [316, 410, 38], [54, 235, 309], [458, 565, 203], [223, 57, 152], [191, 455, 405], [172, 423, 476], [55, 565, 440], [426, 69, 602], [491, 16, 319]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [414, 317], []]
 b := ![[], [487, 391, 294], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI619N0 : CertifiedPrimeIdeal' SI619N0 619 where
  n := 3
  hpos := by decide
  P := [613, 491, 114, 1]
  hirr := P619P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4144319, 4054613, -9253444, 6260421, 485962]
  a := ![3, 10, 7, -15, 35]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5868750, -3270953, -1071763, 6260421, 485962]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI619N0 : Ideal.IsPrime I619N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI619N0 B_one_repr
lemma NI619N0 : Nat.card (O ⧸ I619N0) = 237176659 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI619N0

def I619N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![265, 274, -436, -119, 312]] i)))

def SI619N1: IdealEqSpanCertificate' Table ![![265, 274, -436, -119, 312]] 
 ![![619, 0, 0, 0, 0], ![0, 619, 0, 0, 0], ![332, 552, 1, 0, 0], ![579, 320, 0, 1, 0], ![269, 438, 0, 0, 1]] where
  M :=![![![265, 274, -436, -119, 312], ![-1248, -1033, 2420, -946, -90], ![180, -270, -1303, 3411, -2928], ![6480, 6294, -10264, -2777, 7350], ![-2324, -1564, 5220, -4331, 2153]]]
  hmulB := by decide  
  f := ![![![-12773, -1844, 19420, 4377, 13242]], ![![-52968, -11083, 75764, 16844, 52746]], ![![-54256, -10912, 78217, 17421, 54306]], ![![-39621, -7526, 57732, 12890, 39936]], ![![-43287, -8708, 62400, 13898, 43325]]]
  g := ![![![210, 230, -436, -119, 312], ![-376, -1607, 2420, -946, -90], ![-1219, 1470, -1303, 3411, -2928], ![4919, 5398, -10264, -2777, 7350], ![312, -3942, 5220, -4331, 2153]]]
  hle1 := by decide   
  hle2 := by decide  


def P619P1 : CertificateIrreducibleZModOfList' 619 2 2 9 [143, 205, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [414, 618], [0, 1]]
 g := ![![[404, 316], [350, 436], [239], [44, 154], [389], [567, 45], [198, 269], [552], [1]], ![[0, 303], [106, 183], [239], [43, 465], [389], [8, 574], [144, 350], [552], [1]]]
 h' := ![![[414, 618], [89, 88], [368, 386], [517, 471], [147, 57], [8, 113], [160, 402], [318, 561], [476, 414], [0, 1]], ![[0, 1], [0, 531], [470, 233], [526, 148], [223, 562], [365, 506], [77, 217], [447, 58], [409, 205], [414, 618]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [124]]
 b := ![[], [165, 62]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI619N1 : CertifiedPrimeIdeal' SI619N1 619 where
  n := 2
  hpos := by decide
  P := [143, 205, 1]
  hirr := P619P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1963, -1047, 4128, -787, 1392]
  a := ![1, 4, 2, -6, 13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2086, -4261, 4128, -787, 1392]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI619N1 : Ideal.IsPrime I619N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI619N1 B_one_repr
lemma NI619N1 : Nat.card (O ⧸ I619N1) = 383161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI619N1
def MulI619N0 : IdealMulLeCertificate' Table 
  ![![-12773, -1844, 19420, 4377, 13242]] ![![265, 274, -436, -119, 312]]
  ![![619, 0, 0, 0, 0]] where
 M := ![![![619, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I631N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-55, 32, 396, -497, 298]] i)))

def SI631N0: IdealEqSpanCertificate' Table ![![-55, 32, 396, -497, 298]] 
 ![![631, 0, 0, 0, 0], ![0, 631, 0, 0, 0], ![0, 0, 631, 0, 0], ![277, 127, 617, 1, 0], ![123, 574, 393, 0, 1]] where
  M :=![![![-55, 32, 396, -497, 298], ![-1192, -1249, 1852, 1488, -2386], ![4772, 4204, -8407, 1557, 2078], ![-3560, -1714, 9512, -11747, 7942], ![-6084, -5726, 9924, 1351, -5657]]]
  hmulB := by decide  
  f := ![![![5914695, -3563950, 251308, -535517, 1155260]], ![![-4621040, 2784449, -196340, 418390, -902582]], ![![1805164, -1087718, 76703, -163439, 352588]], ![![3434057, -2069221, 145913, -310919, 670744]], ![![-1923413, 1158970, -81719, 174147, -375679]]]
  g := ![![![160, -171, 301, -497, 298], ![-190, 1869, 34, 1488, -2386], ![-1081, -2197, -2830, 1557, 2078], ![3603, -4863, 6555, -11747, 7942], ![500, 4865, 2218, 1351, -5657]]]
  hle1 := by decide   
  hle2 := by decide  


def P631P0 : CertificateIrreducibleZModOfList' 631 3 2 9 [225, 120, 13, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [486, 86, 476], [132, 544, 155], [0, 1]]
 g := ![![[225, 193, 339], [5, 141, 20], [497, 351, 94], [473, 165], [223, 11, 445], [566, 290, 382], [495, 550, 508], [618, 1], []], ![[420, 455, 23, 185], [182, 342, 428, 436], [435, 220, 475, 452], [146, 72], [52, 577, 253, 187], [292, 178, 316, 447], [629, 452, 574, 559], [603, 628], [493, 47]], ![[180, 375, 71, 580], [503, 402, 49, 328], [487, 292, 485, 310], [571, 496], [458, 29, 608, 159], [515, 354, 50, 197], [185, 564, 394, 165], [278, 455], [183, 47]]]
 h' := ![![[486, 86, 476], [137, 601, 344], [493, 321, 438], [482, 440, 57], [305, 346, 436], [112, 141, 571], [312, 367, 535], [401, 73, 49], [0, 0, 1], [0, 1]], ![[132, 544, 155], [411, 178, 593], [104, 250, 479], [464, 448, 37], [42, 557, 564], [71, 375, 402], [314, 519, 54], [454, 5, 197], [333, 606, 544], [486, 86, 476]], ![[0, 1], [438, 483, 325], [316, 60, 345], [198, 374, 537], [450, 359, 262], [56, 115, 289], [462, 376, 42], [337, 553, 385], [227, 25, 86], [132, 544, 155]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [603, 263], []]
 b := ![[], [222, 341, 478], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI631N0 : CertifiedPrimeIdeal' SI631N0 631 where
  n := 3
  hpos := by decide
  P := [225, 120, 13, 1]
  hirr := P631P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-42303, -39332, 75148, -4276, -29472]
  a := ![4, -1, -1, 3, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![7555, 27608, 22656, -4276, -29472]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI631N0 : Ideal.IsPrime I631N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI631N0 B_one_repr
lemma NI631N0 : Nat.card (O ⧸ I631N0) = 251239591 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI631N0

def I631N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5914695, -3563950, 251308, -535517, 1155260]] i)))

def SI631N1: IdealEqSpanCertificate' Table ![![5914695, -3563950, 251308, -535517, 1155260]] 
 ![![631, 0, 0, 0, 0], ![0, 631, 0, 0, 0], ![139, 14, 1, 0, 0], ![578, 505, 0, 1, 0], ![562, 222, 0, 0, 1]] where
  M :=![![![5914695, -3563950, 251308, -535517, 1155260], ![-4621040, 2784449, -196340, 418390, -902582], ![1805164, -1087718, 76703, -163439, 352588], ![1605344, -967318, 68216, -145347, 313562], ![1866420, -1124632, 79308, -168985, 364555]]]
  hmulB := by decide  
  f := ![![![-55, 32, 396, -497, 298]], ![![-1192, -1249, 1852, 1488, -2386]], ![![-31, -14, 115, -74, 16]], ![![-1010, -973, 1860, 717, -1624]], ![![-478, -420, 1020, 83, -583]]]
  g := ![![![-584381, 10913, 251308, -535517, 1155260], ![456564, -8527, -196340, 418390, -902582], ![-178357, 3329, 76703, -163439, 352588], ![-158618, 2959, 68216, -145347, 313562], ![-184412, 3441, 79308, -168985, 364555]]]
  hle1 := by decide   
  hle2 := by decide  


def P631P1 : CertificateIrreducibleZModOfList' 631 2 2 9 [448, 94, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [537, 630], [0, 1]]
 g := ![![[65, 335], [258, 149], [599, 601], [31], [89, 254], [294, 128], [231, 149], [2], [1]], ![[125, 296], [134, 482], [264, 30], [31], [191, 377], [251, 503], [107, 482], [2], [1]]]
 h' := ![![[537, 630], [520, 270], [454, 113], [273, 427], [512, 381], [167, 221], [627, 510], [412, 113], [183, 537], [0, 1]], ![[0, 1], [380, 361], [559, 518], [519, 204], [34, 250], [216, 410], [12, 121], [517, 518], [185, 94], [537, 630]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [196]]
 b := ![[], [189, 98]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI631N1 : CertifiedPrimeIdeal' SI631N1 631 where
  n := 2
  hpos := by decide
  P := [448, 94, 1]
  hirr := P631P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-188173, -118761, 307606, -16017, 21487]
  a := ![7, -46, -24, 25, -119]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-72525, -1754, 307606, -16017, 21487]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI631N1 : Ideal.IsPrime I631N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI631N1 B_one_repr
lemma NI631N1 : Nat.card (O ⧸ I631N1) = 398161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI631N1
def MulI631N0 : IdealMulLeCertificate' Table 
  ![![-55, 32, 396, -497, 298]] ![![5914695, -3563950, 251308, -535517, 1155260]]
  ![![631, 0, 0, 0, 0]] where
 M := ![![![631, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC631 : ContainsPrimesAboveP 631 ![I631N0, I631N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI631N0
    exact isPrimeI631N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 631 (by decide) (𝕀 ⊙ MulI631N0)
instance hp641 : Fact (Nat.Prime 641) := {out := by norm_num}

def I641N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-143, 70, -4, 12, -22]] i)))

def SI641N0: IdealEqSpanCertificate' Table ![![-143, 70, -4, 12, -22]] 
 ![![641, 0, 0, 0, 0], ![0, 641, 0, 0, 0], ![20, 270, 1, 0, 0], ![369, 505, 0, 1, 0], ![175, 398, 0, 0, 1]] where
  M :=![![![-143, 70, -4, 12, -22], ![88, -79, 8, -10, 28], ![-56, 10, 5, 4, -2], ![-40, 20, 0, 7, -4], ![-40, 30, 0, 4, -5]]]
  hmulB := by decide  
  f := ![![![-15, -10, 4, 8, 2]], ![![-8, 1, -8, -10, 52]], ![![-4, 0, -3, -4, 22]], ![![-15, -5, -4, -3, 42]], ![![-9, -2, -4, -4, 33]]]
  g := ![![![-1, 6, -4, 12, -22], ![-2, -13, 8, -10, 28], ![-2, -4, 5, 4, -2], ![-3, -3, 0, 7, -4], ![-1, 0, 0, 4, -5]]]
  hle1 := by decide   
  hle2 := by decide  


def P641P0 : CertificateIrreducibleZModOfList' 641 2 2 9 [2, 567, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [74, 640], [0, 1]]
 g := ![![[604, 321], [571], [333], [516], [355], [50], [130], [457, 348], [1]], ![[0, 320], [571], [333], [516], [355], [50], [130], [569, 293], [1]]]
 h' := ![![[74, 640], [556, 287], [387, 311], [396, 153], [303, 61], [418, 454], [554, 306], [368, 435], [639, 74], [0, 1]], ![[0, 1], [0, 354], [325, 330], [180, 488], [330, 580], [41, 187], [122, 335], [508, 206], [346, 567], [74, 640]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [460]]
 b := ![[], [464, 230]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI641N0 : CertifiedPrimeIdeal' SI641N0 641 where
  n := 2
  hpos := by decide
  P := [2, 567, 1]
  hirr := P641P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-16350, -17632, 23714, 4027, -19452]
  a := ![1, -12, -7, 9, -36]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2227, -1111, 23714, 4027, -19452]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI641N0 : Ideal.IsPrime I641N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI641N0 B_one_repr
lemma NI641N0 : Nat.card (O ⧸ I641N0) = 410881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI641N0

def I641N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2041, 1188, -82, 182, -384]] i)))

def SI641N1: IdealEqSpanCertificate' Table ![![-2041, 1188, -82, 182, -384]] 
 ![![641, 0, 0, 0, 0], ![0, 641, 0, 0, 0], ![367, 524, 1, 0, 0], ![633, 597, 0, 1, 0], ![252, 405, 0, 0, 1]] where
  M :=![![![-2041, 1188, -82, 182, -384], ![1536, -991, 72, -144, 324], ![-648, 336, -19, 54, -108], ![-552, 324, -24, 53, -108], ![-624, 396, -32, 58, -127]]]
  hmulB := by decide  
  f := ![![![247, 60, -346, -70, -240]], ![![960, 241, -1320, -312, -900]], ![![929, 232, -1281, -296, -876]], ![![1143, 285, -1578, -361, -1080]], ![![708, 177, -976, -226, -667]]]
  g := ![![![15, 142, -82, 182, -384], ![-24, -131, 72, -144, 324], ![-1, 34, -19, 54, -108], ![3, 39, -24, 53, -108], ![10, 53, -32, 58, -127]]]
  hle1 := by decide   
  hle2 := by decide  


def P641P1 : CertificateIrreducibleZModOfList' 641 2 2 9 [217, 595, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [46, 640], [0, 1]]
 g := ![![[499, 562], [359], [529], [512], [353], [56], [118], [452, 193], [1]], ![[70, 79], [359], [529], [512], [353], [56], [118], [356, 448], [1]]]
 h' := ![![[46, 640], [427, 531], [105, 513], [58, 618], [369, 431], [335, 538], [155, 72], [630, 360], [424, 46], [0, 1]], ![[0, 1], [495, 110], [627, 128], [282, 23], [324, 210], [84, 103], [262, 569], [524, 281], [617, 595], [46, 640]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [528]]
 b := ![[], [338, 264]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI641N1 : CertifiedPrimeIdeal' SI641N1 641 where
  n := 2
  hpos := by decide
  P := [217, 595, 1]
  hirr := P641P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![355, 5964, 3362, 4376, 11002]
  a := ![3, 9, 2, 7, 11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-10571, -13766, 3362, 4376, 11002]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI641N1 : Ideal.IsPrime I641N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI641N1 B_one_repr
lemma NI641N1 : Nat.card (O ⧸ I641N1) = 410881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI641N1

def I641N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-39, -10, 54, 10, 38]] i)))

def SI641N2: IdealEqSpanCertificate' Table ![![-39, -10, 54, 10, 38]] 
 ![![641, 0, 0, 0, 0], ![335, 1, 0, 0, 0], ![616, 0, 1, 0, 0], ![174, 0, 0, 1, 0], ![60, 0, 0, 0, 1]] where
  M :=![![![-39, -10, 54, 10, 38], ![-152, -41, 208, 50, 136], ![-272, -58, 367, 90, 286], ![-496, -128, 696, 109, 488], ![-440, -122, 608, 134, 389]]]
  hmulB := by decide  
  f := ![![![-409079, 245422, -17258, 36962, -79522]], ![![-213297, 127961, -8998, 19272, -41462]], ![![-393320, 235966, -16593, 35538, -76458]], ![![-111218, 66724, -4692, 10049, -21620]], ![![-38492, 23094, -1624, 3478, -7483]]]
  g := ![![![-53, -10, 54, 10, 38], ![-205, -41, 208, 50, 136], ![-374, -58, 367, 90, 286], ![-678, -128, 696, 109, 488], ![-594, -122, 608, 134, 389]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI641N2 : Nat.card (O ⧸ I641N2) = 641 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI641N2)

lemma isPrimeI641N2 : Ideal.IsPrime I641N2 := prime_ideal_of_norm_prime hp641.out _ NI641N2
def MulI641N0 : IdealMulLeCertificate' Table 
  ![![-143, 70, -4, 12, -22]] ![![-2041, 1188, -82, 182, -384]]
  ![![409079, -245422, 17258, -36962, 79522]] where
 M := ![![![409079, -245422, 17258, -36962, 79522]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI641N1 : IdealMulLeCertificate' Table 
  ![![409079, -245422, 17258, -36962, 79522]] ![![-39, -10, 54, 10, 38]]
  ![![641, 0, 0, 0, 0]] where
 M := ![![![-641, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC641 : ContainsPrimesAboveP 641 ![I641N0, I641N1, I641N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI641N0
    exact isPrimeI641N1
    exact isPrimeI641N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 641 (by decide) (𝕀 ⊙ MulI641N0 ⊙ MulI641N1)
instance hp643 : Fact (Nat.Prime 643) := {out := by norm_num}

def I643N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-155631, -200210, 135702, 447999, -519082]] i)))

def SI643N0: IdealEqSpanCertificate' Table ![![-155631, -200210, 135702, 447999, -519082]] 
 ![![643, 0, 0, 0, 0], ![0, 643, 0, 0, 0], ![0, 0, 643, 0, 0], ![0, 0, 0, 643, 0], ![160, 488, 586, 72, 1]] where
  M :=![![![-155631, -200210, 135702, 447999, -519082], ![2076328, 1914233, -3514912, -105512, 1649830], ![-3299660, -2474634, 6863723, -4234315, 1333294], ![-3704752, -4742694, 3282704, 10484147, -12194566], ![6202684, 5270254, -11509592, 3161833, 1804493]]]
  hmulB := by decide  
  f := ![![![5579, -5124, 1274, -457, 2260]], ![![-9040, 1419, 3312, 1202, 1778]], ![![-3556, -3440, 6753, 1221, 5384]], ![![-6248, -3274, 11056, 2239, 8158]], ![![-9420, -3704, 10238, 2165, 7743]]]
  g := ![![![128923, 393642, 473278, 58821, -519082], ![-407304, -1249149, -1509044, -184904, 1649830], ![-336900, -1015742, -1204427, -155881, 1333294], ![3028656, 9247598, 11118660, 1381793, -12194566], ![-439372, -1361310, -1662430, -197141, 1804493]]]
  hle1 := by decide   
  hle2 := by decide  


def P643P0 : CertificateIrreducibleZModOfList' 643 4 2 9 [76, 46, 635, 332, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [146, 592, 455, 199], [212, 363, 295, 175], [596, 330, 536, 269], [0, 1]]
 g := ![![[15, 351, 354, 503], [577, 86, 283, 582], [424, 197, 606], [286, 242, 89], [505, 134, 473], [132, 337, 31], [338, 363, 38], [311, 1], []], ![[25, 637, 442, 258, 397, 619], [199, 105, 207, 575, 500, 561], [199, 416, 444], [388, 402, 60], [608, 608, 459], [476, 234, 218], [371, 50, 516], [134, 129, 106, 404, 574, 72], [173, 296, 378]], ![[312, 407, 31, 129, 99, 327], [111, 76, 304, 390, 185, 247], [602, 627, 365], [195, 344, 626], [383, 440, 167], [284, 476, 217], [391, 227, 181], [263, 457, 432, 481, 398, 104], [120, 629, 404]], ![[612, 195, 47, 627, 444, 219], [45, 495, 374, 375, 10, 88], [281, 238, 129], [203, 28, 477], [243, 148, 360], [581, 91, 375], [394, 462, 94], [528, 283, 151, 295, 407, 376], [418, 218, 345]]]
 h' := ![![[146, 592, 455, 199], [515, 39, 482, 303], [18, 271, 74, 608], [190, 550, 254, 261], [635, 164, 127, 416], [282, 454, 107, 452], [266, 87, 443, 139], [155, 407, 513, 279], [0, 0, 1], [0, 1]], ![[212, 363, 295, 175], [519, 353, 247, 115], [527, 222, 151, 446], [478, 624, 383, 517], [292, 357, 268, 405], [159, 475, 54, 83], [531, 214, 59, 223], [361, 218, 172, 143], [452, 307, 623, 327], [146, 592, 455, 199]], ![[596, 330, 536, 269], [516, 535, 552, 245], [78, 445, 584, 33], [465, 515, 141, 115], [87, 578, 598, 559], [574, 157, 503, 324], [492, 192, 548, 329], [251, 337, 415, 326], [459, 280, 127, 283], [212, 363, 295, 175]], ![[0, 1], [408, 359, 5, 623], [555, 348, 477, 199], [636, 240, 508, 393], [76, 187, 293, 549], [71, 200, 622, 427], [340, 150, 236, 595], [132, 324, 186, 538], [19, 56, 535, 33], [596, 330, 536, 269]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [341, 103, 317], []]
 b := ![[], [], [451, 223, 382, 68], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI643N0 : CertifiedPrimeIdeal' SI643N0 643 where
  n := 4
  hpos := by decide
  P := [76, 46, 635, 332, 1]
  hirr := P643P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-41483210714, -20771939980, 105395884664, -120986710820, 82157814978]
  a := ![3, -20, -13, 31, -73]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-20508139358, -62385358708, -74710861108, -9387790652, 82157814978]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI643N0 : Ideal.IsPrime I643N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI643N0 B_one_repr
lemma NI643N0 : Nat.card (O ⧸ I643N0) = 170940075601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI643N0

def I643N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5579, 5124, -1274, 457, -2260]] i)))

def SI643N1: IdealEqSpanCertificate' Table ![![-5579, 5124, -1274, 457, -2260]] 
 ![![643, 0, 0, 0, 0], ![209, 1, 0, 0, 0], ![343, 0, 1, 0, 0], ![60, 0, 0, 1, 0], ![218, 0, 0, 0, 1]] where
  M :=![![![-5579, 5124, -1274, 457, -2260], ![9040, -1419, -3312, -1202, -1778], ![3556, 3440, -6753, -1221, -5384], ![6248, 3274, -11056, -2239, -8158], ![4508, 2736, -9648, -1925, -7085]]]
  hmulB := by decide  
  f := ![![![155631, 200210, -135702, -447999, 519082]], ![![47357, 62099, -38642, -145453, 166156]], ![![88151, 110648, -83063, -232394, 274824]], ![![20284, 26058, -17768, -58109, 67402]], ![![43118, 59682, -28108, -156805, 173181]]]
  g := ![![![-271, 5124, -1274, 457, -2260], ![2957, -1419, -3312, -1202, -1778], ![4429, 3440, -6753, -1221, -5384], ![7818, 3274, -11056, -2239, -8158], ![6846, 2736, -9648, -1925, -7085]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI643N1 : Nat.card (O ⧸ I643N1) = 643 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI643N1)

lemma isPrimeI643N1 : Ideal.IsPrime I643N1 := prime_ideal_of_norm_prime hp643.out _ NI643N1
def MulI643N0 : IdealMulLeCertificate' Table 
  ![![-155631, -200210, 135702, 447999, -519082]] ![![-5579, 5124, -1274, 457, -2260]]
  ![![643, 0, 0, 0, 0]] where
 M := ![![![-643, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC643 : ContainsPrimesAboveP 643 ![I643N0, I643N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI643N0
    exact isPrimeI643N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 643 (by decide) (𝕀 ⊙ MulI643N0)


lemma PB1321I12_primes (p : ℕ) :
  p ∈ Set.range ![599, 601, 607, 613, 617, 619, 631, 641, 643] ↔ Nat.Prime p ∧ 593 < p ∧ p ≤ 643 := by
  rw [← List.mem_ofFn']
  convert primes_range 593 643 (by omega)

def PB1321I12 : PrimesBelowBoundCertificateInterval O 593 643 1321 where
  m := 9
  g := ![2, 3, 4, 3, 3, 2, 2, 3, 2]
  P := ![599, 601, 607, 613, 617, 619, 631, 641, 643]
  hP := PB1321I12_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I599N0, I599N1]
    · exact ![I601N0, I601N1, I601N2]
    · exact ![I607N0, I607N1, I607N2, I607N3]
    · exact ![I613N0, I613N1, I613N2]
    · exact ![I617N0, I617N1, I617N2]
    · exact ![I619N0, I619N1]
    · exact ![I631N0, I631N1]
    · exact ![I641N0, I641N1, I641N2]
    · exact ![I643N0, I643N1]
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
    · exact ![214921799, 358801]
    · exact ![361201, 361201, 601]
    · exact ![368449, 607, 607, 607]
    · exact ![230346397, 613, 613]
    · exact ![380689, 380689, 617]
    · exact ![237176659, 383161]
    · exact ![251239591, 398161]
    · exact ![410881, 410881, 641]
    · exact ![170940075601, 643]
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
      exact NI607N2
      exact NI607N3
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
    · dsimp ; intro j
      fin_cases j
      exact NI619N0
      exact NI619N1
    · dsimp ; intro j
      fin_cases j
      exact NI631N0
      exact NI631N1
    · dsimp ; intro j
      fin_cases j
      exact NI641N0
      exact NI641N1
      exact NI641N2
    · dsimp ; intro j
      fin_cases j
      exact NI643N0
      exact NI643N1
  β := ![I601N2, I607N1, I607N2, I607N3, I613N1, I613N2, I617N2, I641N2, I643N1]
  Il := ![[], [I601N2], [I607N1, I607N2, I607N3], [I613N1, I613N2], [I617N2], [], [], [I641N2], [I643N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
