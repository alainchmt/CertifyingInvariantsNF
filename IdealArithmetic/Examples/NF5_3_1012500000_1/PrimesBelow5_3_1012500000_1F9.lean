
import IdealArithmetic.Examples.NF5_3_1012500000_1.RI5_3_1012500000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp421 : Fact (Nat.Prime 421) := {out := by norm_num}

def I421N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14011, 13338, 4242, 3926, 230]] i)))

def SI421N0: IdealEqSpanCertificate' Table ![![14011, 13338, 4242, 3926, 230]] 
 ![![421, 0, 0, 0, 0], ![0, 421, 0, 0, 0], ![0, 0, 421, 0, 0], ![332, 353, 383, 1, 0], ![70, 201, 301, 0, 1]] where
  M :=![![![14011, 13338, 4242, 3926, 230], ![1380, 17461, 21218, 9534, 3926], ![23556, 60270, 55877, 28038, 9534], ![-2244, -2374, -984, -763, -94], ![16260, 49494, 48738, 23826, 8489]]]
  hmulB := by decide  
  f := ![![![127, 230, -86, -70, -14]], ![![-84, -83, 98, -54, -70]], ![![-420, -1134, 545, 2010, -54]], ![![-352, -919, 509, 1725, -118]], ![![-314, -799, 417, 1382, -75]]]
  g := ![![![-3101, -3370, -3726, 3926, 230], ![-8168, -9827, -11430, 9534, 3926], ![-23640, -27918, -32191, 28038, 9534], ![612, 679, 759, -763, -94], ![-20162, -23913, -27629, 23826, 8489]]]
  hle1 := by decide   
  hle2 := by decide  


def P421P0 : CertificateIrreducibleZModOfList' 421 3 2 8 [337, 367, 362, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [21, 311, 317], [38, 109, 104], [0, 1]]
 g := ![![[316, 238, 100], [327, 320], [227, 53, 417], [105, 85], [46, 184], [104, 355, 268], [409, 113], [1]], ![[331, 74, 289, 12], [191, 414], [2, 297, 285, 246], [401, 412], [246, 196], [3, 293, 183, 5], [277, 308], [32, 202, 264, 48]], ![[300, 92, 118, 247], [219, 256], [374, 102, 145, 108], [125, 49], [305, 246], [129, 192, 151, 328], [226, 182], [382, 93, 126, 373]]]
 h' := ![![[21, 311, 317], [76, 180, 10], [123, 138, 337], [119, 306, 363], [154, 364, 80], [316, 212, 326], [154, 234, 119], [84, 54, 59], [0, 1]], ![[38, 109, 104], [159, 47, 52], [59, 314, 68], [370, 93, 165], [114, 14, 334], [105, 107, 14], [353, 234, 2], [161, 308, 394], [21, 311, 317]], ![[0, 1], [193, 194, 359], [290, 390, 16], [52, 22, 314], [197, 43, 7], [39, 102, 81], [65, 374, 300], [234, 59, 389], [38, 109, 104]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [234, 48], []]
 b := ![[], [74, 403, 130], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI421N0 : CertifiedPrimeIdeal' SI421N0 421 where
  n := 3
  hpos := by decide
  P := [337, 367, 362, 1]
  hirr := P421P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-427739, -1071694, 520590, 1525634, 174644]
  a := ![0, -1, -4, -1, -6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1233167, -1365140, -1511556, 1525634, 174644]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI421N0 : Ideal.IsPrime I421N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI421N0 B_one_repr
lemma NI421N0 : Nat.card (O ⧸ I421N0) = 74618461 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI421N0

def I421N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-127, -230, 86, 70, 14]] i)))

def SI421N1: IdealEqSpanCertificate' Table ![![-127, -230, 86, 70, 14]] 
 ![![421, 0, 0, 0, 0], ![0, 421, 0, 0, 0], ![317, 231, 1, 0, 0], ![267, 376, 0, 1, 0], ![227, 233, 0, 0, 1]] where
  M :=![![![-127, -230, 86, 70, 14], ![84, 83, -98, 54, 70], ![420, 1134, -545, -2010, 54], ![-156, -362, 488, 1303, -362], ![-2220, -5538, 2166, 7434, 271]]]
  hmulB := by decide  
  f := ![![![-14011, -13338, -4242, -3926, -230]], ![![-1380, -17461, -21218, -9534, -3926]], ![![-11363, -19767, -14969, -8254, -2350]], ![![-10113, -24048, -21638, -11003, -3652]], ![![-8357, -16973, -14146, -7450, -2317]]]
  g := ![![![-117, -118, 86, 70, 14], ![2, -33, -98, 54, 70], ![1657, 2067, -545, -2010, 54], ![-999, -1232, 488, 1303, -362], ![-6497, -7991, 2166, 7434, 271]]]
  hle1 := by decide   
  hle2 := by decide  


def P421P1 : CertificateIrreducibleZModOfList' 421 2 2 8 [121, 56, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [365, 420], [0, 1]]
 g := ![![[331, 254], [79], [255, 358], [166], [393], [401, 55], [414], [365, 1]], ![[0, 167], [79], [415, 63], [166], [393], [268, 366], [414], [309, 420]]]
 h' := ![![[365, 420], [273, 268], [299, 105], [234, 217], [310, 88], [315, 285], [342, 359], [40, 68], [0, 1]], ![[0, 1], [0, 153], [313, 316], [291, 204], [13, 333], [353, 136], [25, 62], [21, 353], [365, 420]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [294]]
 b := ![[], [327, 147]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI421N1 : CertifiedPrimeIdeal' SI421N1 421 where
  n := 2
  hpos := by decide
  P := [121, 56, 1]
  hirr := P421P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1064, -7420, 4420, 2688, 411]
  a := ![3, -64, 1, -1, 2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5257, -5071, 4420, 2688, 411]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI421N1 : Ideal.IsPrime I421N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI421N1 B_one_repr
lemma NI421N1 : Nat.card (O ⧸ I421N1) = 177241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI421N1
def MulI421N0 : IdealMulLeCertificate' Table 
  ![![14011, 13338, 4242, 3926, 230]] ![![-127, -230, 86, 70, 14]]
  ![![421, 0, 0, 0, 0]] where
 M := ![![![-421, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC421 : ContainsPrimesAboveP 421 ![I421N0, I421N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI421N0
    exact isPrimeI421N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 421 (by decide) (𝕀 ⊙ MulI421N0)
instance hp431 : Fact (Nat.Prime 431) := {out := by norm_num}

def I431N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![312671, 167131, -73347, 13704, -26392]] i)))

def SI431N0: IdealEqSpanCertificate' Table ![![312671, 167131, -73347, 13704, -26392]] 
 ![![431, 0, 0, 0, 0], ![0, 431, 0, 0, 0], ![0, 0, 431, 0, 0], ![223, 293, 282, 1, 0], ![47, 134, 233, 0, 1]] where
  M :=![![![312671, 167131, -73347, 13704, -26392], ![-158352, -83209, 38954, -6138, 13704], ![82224, 47208, -15025, 5466, -6138], ![-47250, -25245, 11049, -2077, 3980], ![-35646, -16077, 12181, 120, 3725]]]
  hmulB := by decide  
  f := ![![![-203, -515, 157, 600, 74]], ![![444, 907, -940, -2190, 600]], ![![3600, 9444, -2123, -9870, -2190]], ![![2543, 6507, -1936, -7603, -988]], ![![2035, 5258, -1413, -5886, -965]]]
  g := ![![![-3487, -723, 5131, 13704, -26392], ![1314, -281, -3302, -6138, 13704], ![-1968, -1698, -293, 5466, -6138], ![531, 116, -767, -2077, 3980], ![-551, -1277, -2064, 120, 3725]]]
  hle1 := by decide   
  hle2 := by decide  


def P431P0 : CertificateIrreducibleZModOfList' 431 3 2 8 [271, 385, 79, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [227, 235, 110], [125, 195, 321], [0, 1]]
 g := ![![[225, 379, 184], [254, 4, 97], [155, 183, 125], [350, 234, 41], [171, 265], [400, 313, 10], [84, 207], [1]], ![[74, 316, 235, 76], [313, 244, 246, 243], [118, 216, 108, 119], [350, 35, 101, 352], [283, 171], [59, 420, 9, 223], [347, 1], [425, 147, 63, 72]], ![[316, 72, 343, 374], [223, 14, 84, 193], [1, 191, 106, 26], [317, 46, 183, 383], [428, 209], [206, 97, 402, 292], [392, 366], [274, 14, 272, 359]]]
 h' := ![![[227, 235, 110], [126, 239, 299], [233, 244, 195], [401, 137, 43], [327, 147, 327], [212, 387, 103], [250, 415, 410], [160, 46, 352], [0, 1]], ![[125, 195, 321], [249, 228, 119], [193, 340, 215], [267, 65, 181], [73, 295, 200], [287, 0, 160], [94, 124, 179], [76, 218, 430], [227, 235, 110]], ![[0, 1], [270, 395, 13], [81, 278, 21], [414, 229, 207], [110, 420, 335], [361, 44, 168], [132, 323, 273], [142, 167, 80], [125, 195, 321]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [388, 321], []]
 b := ![[], [395, 42, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI431N0 : CertifiedPrimeIdeal' SI431N0 431 where
  n := 3
  hpos := by decide
  P := [271, 385, 79, 1]
  hirr := P431P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-88844, -211984, 124208, 348076, -28108]
  a := ![1, -3, -2, -1, -3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-177236, -228380, -212260, 348076, -28108]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI431N0 : Ideal.IsPrime I431N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI431N0 B_one_repr
lemma NI431N0 : Nat.card (O ⧸ I431N0) = 80062991 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI431N0

def I431N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![203, 515, -157, -600, -74]] i)))

def SI431N1: IdealEqSpanCertificate' Table ![![203, 515, -157, -600, -74]] 
 ![![431, 0, 0, 0, 0], ![0, 431, 0, 0, 0], ![344, 35, 1, 0, 0], ![120, 123, 0, 1, 0], ![199, 98, 0, 0, 1]] where
  M :=![![![203, 515, -157, -600, -74], ![-444, -907, 940, 2190, -600], ![-3600, -9444, 2123, 9870, 2190], ![3990, 9597, -4679, -14317, 550], ![11670, 31587, -4237, -28104, -10477]]]
  hmulB := by decide  
  f := ![![![-312671, -167131, 73347, -13704, 26392]], ![![158352, 83209, -38954, 6138, -13704]], ![![-236888, -126747, 55413, -10452, 19966]], ![![-41754, -22728, 9279, -2059, 3428]], ![![-108277, -58210, 24980, -4932, 9061]]]
  g := ![![![327, 202, -157, -600, -74], ![-1084, -567, 940, 2190, -600], ![-5462, -3509, 2123, 9870, 2190], ![7476, 4363, -4679, -14317, 550], ![16071, 10820, -4237, -28104, -10477]]]
  hle1 := by decide   
  hle2 := by decide  


def P431P1 : CertificateIrreducibleZModOfList' 431 2 2 8 [134, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [421, 430], [0, 1]]
 g := ![![[103, 225], [182, 342], [152, 54], [96, 5], [198], [379, 60], [294], [421, 1]], ![[8, 206], [210, 89], [43, 377], [46, 426], [198], [210, 371], [294], [411, 430]]]
 h' := ![![[421, 430], [179, 15], [320, 341], [66, 384], [202, 250], [72, 225], [310, 329], [47, 397], [0, 1]], ![[0, 1], [29, 416], [358, 90], [105, 47], [288, 181], [408, 206], [37, 102], [387, 34], [421, 430]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [87]]
 b := ![[], [2, 259]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI431N1 : CertifiedPrimeIdeal' SI431N1 431 where
  n := 2
  hpos := by decide
  P := [134, 10, 1]
  hirr := P431P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2767, 6280, -2297, -8932, 1773]
  a := ![1, 19, 3, -1, 6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3508, 2347, -2297, -8932, 1773]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI431N1 : Ideal.IsPrime I431N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI431N1 B_one_repr
lemma NI431N1 : Nat.card (O ⧸ I431N1) = 185761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI431N1
def MulI431N0 : IdealMulLeCertificate' Table 
  ![![312671, 167131, -73347, 13704, -26392]] ![![203, 515, -157, -600, -74]]
  ![![431, 0, 0, 0, 0]] where
 M := ![![![-431, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC431 : ContainsPrimesAboveP 431 ![I431N0, I431N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI431N0
    exact isPrimeI431N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 431 (by decide) (𝕀 ⊙ MulI431N0)
instance hp433 : Fact (Nat.Prime 433) := {out := by norm_num}

def I433N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4003, -3188, 1219, -357, 447]] i)))

def SI433N0: IdealEqSpanCertificate' Table ![![-4003, -3188, 1219, -357, 447]] 
 ![![433, 0, 0, 0, 0], ![0, 433, 0, 0, 0], ![0, 0, 433, 0, 0], ![81, 288, 383, 1, 0], ![295, 312, 142, 0, 1]] where
  M :=![![![-4003, -3188, 1219, -357, 447], ![2682, 2702, -962, 339, -357], ![-2142, -2673, 905, -363, 339], ![1410, 1827, -611, 251, -230], ![708, 768, -265, 111, -100]]]
  hmulB := by decide  
  f := ![![![5, 14, 7, -3, 3]], ![![18, 50, 26, -3, -3]], ![![-18, -27, 143, 219, -3]], ![![-3, 12, 145, 191, -4]], ![![11, 38, 70, 66, -1]]]
  g := ![![![-247, -92, 172, -357, 447], ![186, 38, -185, 339, -357], ![-168, -9, 212, -363, 339], ![113, 3, -148, 251, -230], ![49, 0, -66, 111, -100]]]
  hle1 := by decide   
  hle2 := by decide  


def P433P0 : CertificateIrreducibleZModOfList' 433 3 2 8 [383, 215, 274, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [199, 106, 316], [393, 326, 117], [0, 1]]
 g := ![![[411, 372, 164], [281, 143], [246, 379], [194, 429], [372, 355, 216], [197, 340, 106], [184, 167], [1]], ![[127, 175, 32, 345], [305, 64], [402, 41], [292, 275], [16, 355, 301, 137], [83, 348, 394, 179], [34, 297], [340, 337, 79, 54]], ![[364, 107, 33, 325], [299, 256], [0, 79], [36, 143], [331, 29, 383, 17], [149, 359, 149, 300], [80, 280], [262, 383, 422, 379]]]
 h' := ![![[199, 106, 316], [32, 31, 200], [188, 326, 24], [102, 359, 268], [414, 312, 358], [324, 273, 251], [9, 116, 52], [50, 218, 159], [0, 1]], ![[393, 326, 117], [378, 404, 87], [158, 211, 425], [323, 141, 333], [331, 54, 99], [105, 324, 90], [388, 306, 349], [112, 219, 348], [199, 106, 316]], ![[0, 1], [78, 431, 146], [275, 329, 417], [334, 366, 265], [117, 67, 409], [20, 269, 92], [68, 11, 32], [194, 429, 359], [393, 326, 117]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [254, 48], []]
 b := ![[], [66, 101, 389], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI433N0 : CertifiedPrimeIdeal' SI433N0 433 where
  n := 3
  hpos := by decide
  P := [383, 215, 274, 1]
  hirr := P433P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1207395, -2957662, 1341106, 4198156, 68520]
  a := ![-1, 0, -2, 2, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-834807, -2848510, -3732754, 4198156, 68520]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI433N0 : Ideal.IsPrime I433N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI433N0 B_one_repr
lemma NI433N0 : Nat.card (O ⧸ I433N0) = 81182737 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI433N0

def I433N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, -8, 12, -2, 4]] i)))

def SI433N1: IdealEqSpanCertificate' Table ![![-7, -8, 12, -2, 4]] 
 ![![433, 0, 0, 0, 0], ![341, 1, 0, 0, 0], ![196, 0, 1, 0, 0], ![165, 0, 0, 1, 0], ![283, 0, 0, 0, 1]] where
  M :=![![![-7, -8, 12, -2, 4], ![24, 53, 14, 6, -2], ![-12, -6, 97, 102, 6], ![12, 16, -22, -23, 14], ![108, 264, -52, -282, 25]]]
  hmulB := by decide  
  f := ![![![16159841, 8618088, -3819216, 696322, -1369456]], ![![12707365, 6776873, -3003258, 547556, -1076878]], ![![7324496, 3906174, -1731071, 315610, -620710]], ![![6152265, 3281020, -1454026, 265099, -521370]], ![![10557335, 5630256, -2495120, 454912, -894675]]]
  g := ![![![-1, -8, 12, -2, 4], ![-49, 53, 14, 6, -2], ![-82, -6, 97, 102, 6], ![-3, 16, -22, -23, 14], ![-93, 264, -52, -282, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI433N1 : Nat.card (O ⧸ I433N1) = 433 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI433N1)

lemma isPrimeI433N1 : Ideal.IsPrime I433N1 := prime_ideal_of_norm_prime hp433.out _ NI433N1

def I433N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7823, 4172, -1849, 337, -663]] i)))

def SI433N2: IdealEqSpanCertificate' Table ![![7823, 4172, -1849, 337, -663]] 
 ![![433, 0, 0, 0, 0], ![395, 1, 0, 0, 0], ![288, 0, 1, 0, 0], ![381, 0, 0, 1, 0], ![321, 0, 0, 0, 1]] where
  M :=![![![7823, 4172, -1849, 337, -663], ![-3978, -2122, 940, -171, 337], ![2022, 1077, -479, 87, -171], ![-1182, -629, 279, -53, 100], ![-924, -492, 219, -39, 76]]]
  hmulB := by decide  
  f := ![![![19127, 31958, -10185, 4627, -3855]], ![![17395, 29064, -9263, 4208, -3506]], ![![12786, 21363, -6809, 3093, -2577]], ![![16785, 28045, -8938, 4060, -3383]], ![![14163, 23664, -7542, 3426, -2855]]]
  g := ![![![-2363, 4172, -1849, 337, -663], ![1202, -2122, 940, -171, 337], ![-609, 1077, -479, 87, -171], ![358, -629, 279, -53, 100], ![279, -492, 219, -39, 76]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI433N2 : Nat.card (O ⧸ I433N2) = 433 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI433N2)

lemma isPrimeI433N2 : Ideal.IsPrime I433N2 := prime_ideal_of_norm_prime hp433.out _ NI433N2
def MulI433N0 : IdealMulLeCertificate' Table 
  ![![-4003, -3188, 1219, -357, 447]] ![![-7, -8, 12, -2, 4]]
  ![![-19127, -31958, 10185, -4627, 3855]] where
 M := ![![![-19127, -31958, 10185, -4627, 3855]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI433N1 : IdealMulLeCertificate' Table 
  ![![-19127, -31958, 10185, -4627, 3855]] ![![7823, 4172, -1849, 337, -663]]
  ![![433, 0, 0, 0, 0]] where
 M := ![![![-433, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC433 : ContainsPrimesAboveP 433 ![I433N0, I433N1, I433N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI433N0
    exact isPrimeI433N1
    exact isPrimeI433N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 433 (by decide) (𝕀 ⊙ MulI433N0 ⊙ MulI433N1)
instance hp439 : Fact (Nat.Prime 439) := {out := by norm_num}

def I439N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1067, -1504, 494, -210, 186]] i)))

def SI439N0: IdealEqSpanCertificate' Table ![![-1067, -1504, 494, -210, 186]] 
 ![![439, 0, 0, 0, 0], ![0, 439, 0, 0, 0], ![188, 162, 1, 0, 0], ![98, 259, 0, 1, 0], ![80, 345, 0, 0, 1]] where
  M :=![![![-1067, -1504, 494, -210, 186], ![1116, 1723, -556, 246, -210], ![-1260, -2034, 649, -294, 246], ![876, 1422, -454, 205, -172], ![336, 528, -170, 78, -65]]]
  hmulB := by decide  
  f := ![![![-5, -8, -34, -42, -6]], ![![-36, -95, -44, 30, -42]], ![![-16, -40, -31, -6, -18]], ![![-22, -57, -34, 7, -26]], ![![-28, -73, -42, 12, -35]]]
  g := ![![![-201, -208, 494, -210, 186], ![224, 229, -556, 246, -210], ![-260, -264, 649, -294, 246], ![182, 185, -454, 205, -172], ![68, 69, -170, 78, -65]]]
  hle1 := by decide   
  hle2 := by decide  


def P439P0 : CertificateIrreducibleZModOfList' 439 2 2 8 [438, 280, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [159, 438], [0, 1]]
 g := ![![[159, 247], [86, 14], [331, 283], [28], [68, 40], [272, 350], [353], [159, 1]], ![[361, 192], [117, 425], [111, 156], [28], [282, 399], [169, 89], [353], [318, 438]]]
 h' := ![![[159, 438], [86, 329], [331, 392], [262, 399], [68, 109], [272, 308], [172, 204], [159, 259], [0, 1]], ![[0, 1], [156, 110], [321, 47], [48, 40], [278, 330], [76, 131], [122, 235], [74, 180], [159, 438]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [191]]
 b := ![[], [200, 315]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI439N0 : CertifiedPrimeIdeal' SI439N0 439 where
  n := 2
  hpos := by decide
  P := [438, 280, 1]
  hirr := P439P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-402, -2288, -984, -344, -4]
  a := ![0, 0, -6, -10, -4]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![498, 564, -984, -344, -4]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI439N0 : Ideal.IsPrime I439N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI439N0 B_one_repr
lemma NI439N0 : Nat.card (O ⧸ I439N0) = 192721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI439N0

def I439N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-293, -156, 69, -13, 25]] i)))

def SI439N1: IdealEqSpanCertificate' Table ![![-293, -156, 69, -13, 25]] 
 ![![439, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![390, 0, 1, 0, 0], ![228, 0, 0, 1, 0], ![356, 0, 0, 0, 1]] where
  M :=![![![-293, -156, 69, -13, 25], ![150, 82, -36, 3, -13], ![-78, -45, 23, 9, 3], ![42, 17, -11, 5, 0], ![48, 48, -31, -57, 8]]]
  hmulB := by decide  
  f := ![![![37, -634, -1965, -649, -409]], ![![-5, -24, -41, -16, -8]], ![![24, -591, -1777, -591, -369]], ![![18, -331, -1019, -337, -212]], ![![20, -542, -1619, -539, -336]]]
  g := ![![![-73, -156, 69, -13, 25], ![40, 82, -36, 3, -13], ![-27, -45, 23, 9, 3], ![7, 17, -11, 5, 0], ![50, 48, -31, -57, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI439N1 : Nat.card (O ⧸ I439N1) = 439 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI439N1)

lemma isPrimeI439N1 : Ideal.IsPrime I439N1 := prime_ideal_of_norm_prime hp439.out _ NI439N1

def I439N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6847, -19549, -18857, -9300, -3262]] i)))

def SI439N2: IdealEqSpanCertificate' Table ![![-6847, -19549, -18857, -9300, -3262]] 
 ![![439, 0, 0, 0, 0], ![38, 1, 0, 0, 0], ![312, 0, 1, 0, 0], ![63, 0, 0, 1, 0], ![302, 0, 0, 0, 1]] where
  M :=![![![-6847, -19549, -18857, -9300, -3262], ![-19572, -55777, -53772, -26526, -9300], ![-55800, -159072, -153367, -75654, -26526], ![1374, 3921, 3781, 1865, 654], ![-47754, -136125, -131241, -64740, -22699]]]
  hmulB := by decide  
  f := ![![![-565, -1259, 611, 1284, -80]], ![![-50, -113, 52, 114, -4]], ![![-384, -852, 413, 846, -54]], ![![-87, -192, 104, 221, -24]], ![![-464, -1051, 499, 1140, -53]]]
  g := ![![![18657, -19549, -18857, -9300, -3262], ![53204, -55777, -53772, -26526, -9300], ![151746, -159072, -153367, -75654, -26526], ![-3741, 3921, 3781, 1865, 654], ![129854, -136125, -131241, -64740, -22699]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI439N2 : Nat.card (O ⧸ I439N2) = 439 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI439N2)

lemma isPrimeI439N2 : Ideal.IsPrime I439N2 := prime_ideal_of_norm_prime hp439.out _ NI439N2

def I439N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19, -53, 4, 43, 21]] i)))

def SI439N3: IdealEqSpanCertificate' Table ![![-19, -53, 4, 43, 21]] 
 ![![439, 0, 0, 0, 0], ![232, 1, 0, 0, 0], ![173, 0, 1, 0, 0], ![175, 0, 0, 1, 0], ![47, 0, 0, 0, 1]] where
  M :=![![![-19, -53, 4, 43, 21], ![126, 296, -168, -483, 43], ![258, 771, 103, -333, -483], ![-612, -1550, 506, 1885, 186], ![-462, -1701, -1040, -645, 1960]]]
  hmulB := by decide  
  f := ![![![437711, 233247, -104086, 18655, -37227]], ![![230810, 122990, -54890, 9835, -19631]], ![![172747, 92046, -41089, 7358, -14694]], ![![174335, 92899, -41456, 7430, -14827]], ![![46741, 24900, -11124, 1988, -3977]]]
  g := ![![![7, -53, 4, 43, 21], ![98, 296, -168, -483, 43], ![-263, 771, 103, -333, -483], ![-153, -1550, 506, 1885, 186], ![1355, -1701, -1040, -645, 1960]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI439N3 : Nat.card (O ⧸ I439N3) = 439 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI439N3)

lemma isPrimeI439N3 : Ideal.IsPrime I439N3 := prime_ideal_of_norm_prime hp439.out _ NI439N3
def MulI439N0 : IdealMulLeCertificate' Table 
  ![![-1067, -1504, 494, -210, 186]] ![![-293, -156, 69, -13, 25]]
  ![![48607, 26252, -11573, 2153, -4153]] where
 M := ![![![48607, 26252, -11573, 2153, -4153]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI439N1 : IdealMulLeCertificate' Table 
  ![![48607, 26252, -11573, 2153, -4153]] ![![-6847, -19549, -18857, -9300, -3262]]
  ![![437711, 233247, -104086, 18655, -37227]] where
 M := ![![![437711, 233247, -104086, 18655, -37227]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI439N2 : IdealMulLeCertificate' Table 
  ![![437711, 233247, -104086, 18655, -37227]] ![![-19, -53, 4, 43, 21]]
  ![![439, 0, 0, 0, 0]] where
 M := ![![![439, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC439 : ContainsPrimesAboveP 439 ![I439N0, I439N1, I439N2, I439N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI439N0
    exact isPrimeI439N1
    exact isPrimeI439N2
    exact isPrimeI439N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 439 (by decide) (𝕀 ⊙ MulI439N0 ⊙ MulI439N1 ⊙ MulI439N2)
instance hp443 : Fact (Nat.Prime 443) := {out := by norm_num}

def I443N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4271, 11073, -2857, -12186, -2164]] i)))

def SI443N0: IdealEqSpanCertificate' Table ![![4271, 11073, -2857, -12186, -2164]] 
 ![![443, 0, 0, 0, 0], ![0, 443, 0, 0, 0], ![0, 0, 443, 0, 0], ![102, 321, 164, 1, 0], ![56, 174, 294, 0, 1]] where
  M :=![![![4271, 11073, -2857, -12186, -2164], ![-12984, -28189, 23344, 58368, -12186], ![-73116, -195774, 32219, 184308, 58368], ![94926, 231621, -102259, -327193, 1534], ![220866, 617025, -28657, -456858, -264223]]]
  hmulB := by decide  
  f := ![![![-6611303, -3526065, 1562571, -284922, 560294]], ![![3361764, 1793107, -794606, 144900, -284922]], ![![-1709532, -912066, 404077, -73740, 144900]], ![![283092, 150978, -66939, 12191, -23998]], ![![-648098, -345801, 153175, -27966, 54931]]]
  g := ![![![3089, 9705, 5941, -12186, -2164], ![-11928, -37571, -13468, 58368, -12186], ![-49980, -156918, -106895, 184308, 58368], ![75356, 237006, 119879, -327193, 1534], ![139090, 436215, 344419, -456858, -264223]]]
  hle1 := by decide   
  hle2 := by decide  


def P443P0 : CertificateIrreducibleZModOfList' 443 3 2 8 [433, 28, 439, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [49, 300, 244], [398, 142, 199], [0, 1]]
 g := ![![[315, 183, 380], [205, 247, 316], [430, 88], [13, 257, 144], [149, 294, 1], [38, 3, 117], [283, 16], [1]], ![[190, 94, 380, 202], [374, 56, 83, 419], [130, 156], [270, 388, 190, 232], [2, 1, 78, 227], [201, 84, 238, 256], [175, 300], [170, 1, 376, 371]], ![[45, 311, 399, 54], [236, 407, 279, 157], [113, 411], [401, 96, 239, 154], [266, 261, 195, 269], [292, 238, 335, 429], [283, 263], [342, 409, 431, 72]]]
 h' := ![![[49, 300, 244], [278, 383, 384], [379, 334, 279], [130, 218, 242], [161, 79, 12], [380, 298, 442], [272, 93, 219], [10, 415, 4], [0, 1]], ![[398, 142, 199], [258, 282, 18], [399, 165, 175], [119, 324, 285], [247, 377, 159], [420, 344, 361], [320, 180, 187], [182, 69, 381], [49, 300, 244]], ![[0, 1], [203, 221, 41], [281, 387, 432], [193, 344, 359], [354, 430, 272], [243, 244, 83], [253, 170, 37], [9, 402, 58], [398, 142, 199]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [297, 129], []]
 b := ![[], [142, 292, 201], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI443N0 : CertifiedPrimeIdeal' SI443N0 443 where
  n := 3
  hpos := by decide
  P := [433, 28, 439, 1]
  hirr := P443P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-345959, -1161900, 241146, 1158876, 407076]
  a := ![13, -1, -2, 1, -6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-319069, -1002240, -698634, 1158876, 407076]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI443N0 : Ideal.IsPrime I443N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI443N0 B_one_repr
lemma NI443N0 : Nat.card (O ⧸ I443N0) = 86938307 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI443N0

def I443N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, -12, -20, -8, -4]] i)))

def SI443N1: IdealEqSpanCertificate' Table ![![5, -12, -20, -8, -4]] 
 ![![443, 0, 0, 0, 0], ![84, 1, 0, 0, 0], ![32, 0, 1, 0, 0], ![422, 0, 0, 1, 0], ![404, 0, 0, 0, 1]] where
  M :=![![![5, -12, -20, -8, -4], ![-24, -55, -48, -24, -8], ![-48, -144, -143, -72, -24], ![0, 4, 4, 1, 0], ![-48, -132, -116, -48, -23]]]
  hmulB := by decide  
  f := ![![![-9953, -16732, 5308, -2440, 2012]], ![![-1860, -3127, 992, -456, 376]], ![![-752, -1264, 401, -184, 152]], ![![-9458, -15900, 5044, -2319, 1912]], ![![-9068, -15244, 4836, -2224, 1833]]]
  g := ![![![15, -12, -20, -8, -4], ![44, -55, -48, -24, -8], ![128, -144, -143, -72, -24], ![-2, 4, 4, 1, 0], ![100, -132, -116, -48, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI443N1 : Nat.card (O ⧸ I443N1) = 443 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI443N1)

lemma isPrimeI443N1 : Ideal.IsPrime I443N1 := prime_ideal_of_norm_prime hp443.out _ NI443N1

def I443N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-877411, -478157, 210015, -39602, 75402]] i)))

def SI443N2: IdealEqSpanCertificate' Table ![![-877411, -478157, 210015, -39602, 75402]] 
 ![![443, 0, 0, 0, 0], ![264, 1, 0, 0, 0], ![298, 0, 1, 0, 0], ![29, 0, 0, 1, 0], ![260, 0, 0, 0, 1]] where
  M :=![![![-877411, -478157, 210015, -39602, 75402], ![452412, 253619, -110118, 21660, -39602], ![-237612, -141618, 60013, -12852, 21660], ![140466, 85357, -35901, 7885, -12972], ![105954, 60339, -26033, 5238, -9371]]]
  hmulB := by decide  
  f := ![![![-3389, -11955, -6093, -2530, 12672]], ![![-1848, -6703, -3808, -2088, 7546]], ![![-2314, -7956, -3605, -920, 7944]], ![![-785, -2282, -128, 1287, 1250]], ![![-1190, -5685, -6091, -6646, 9571]]]
  g := ![![![100035, -478157, 210015, -39602, 75402], ![-54220, 253619, -110118, 21660, -39602], ![31618, -141618, 60013, -12852, 21660], ![-19303, 85357, -35901, 7885, -12972], ![-13050, 60339, -26033, 5238, -9371]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI443N2 : Nat.card (O ⧸ I443N2) = 443 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI443N2)

lemma isPrimeI443N2 : Ideal.IsPrime I443N2 := prime_ideal_of_norm_prime hp443.out _ NI443N2
def MulI443N0 : IdealMulLeCertificate' Table 
  ![![4271, 11073, -2857, -12186, -2164]] ![![5, -12, -20, -8, -4]]
  ![![-3389, -11955, -6093, -2530, 12672]] where
 M := ![![![-3389, -11955, -6093, -2530, 12672]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI443N1 : IdealMulLeCertificate' Table 
  ![![-3389, -11955, -6093, -2530, 12672]] ![![-877411, -478157, 210015, -39602, 75402]]
  ![![443, 0, 0, 0, 0]] where
 M := ![![![443, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC443 : ContainsPrimesAboveP 443 ![I443N0, I443N1, I443N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI443N0
    exact isPrimeI443N1
    exact isPrimeI443N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 443 (by decide) (𝕀 ⊙ MulI443N0 ⊙ MulI443N1)
instance hp449 : Fact (Nat.Prime 449) := {out := by norm_num}

def I449N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![449, 0, 0, 0, 0]] i)))

def SI449N0: IdealEqSpanCertificate' Table ![![449, 0, 0, 0, 0]] 
 ![![449, 0, 0, 0, 0], ![0, 449, 0, 0, 0], ![0, 0, 449, 0, 0], ![0, 0, 0, 449, 0], ![0, 0, 0, 0, 449]] where
  M :=![![![449, 0, 0, 0, 0], ![0, 449, 0, 0, 0], ![0, 0, 449, 0, 0], ![0, 0, 0, 449, 0], ![0, 0, 0, 0, 449]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P449P0 : CertificateIrreducibleZModOfList' 449 5 2 8 [137, 191, 2, 369, 214, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [30, 283, 114, 79, 120], [215, 194, 262, 233, 38], [295, 239, 102, 29, 164], [144, 181, 420, 108, 127], [0, 1]]
 g := ![![[26, 246, 408, 430, 144], [61, 442, 37, 98], [172, 45, 361, 282], [21, 293, 417, 362], [386, 241, 31, 445], [328, 42, 31, 14], [78, 235, 1], []], ![[173, 18, 308, 371, 336, 342, 114, 206], [263, 344, 302, 379], [183, 166, 114, 269], [7, 133, 402, 237], [133, 315, 388, 322], [20, 128, 298, 174], [143, 139, 78, 282, 350, 346, 205, 159], [135, 162, 121, 400, 37, 328, 310, 248]], ![[153, 42, 249, 420, 344, 88, 98, 355], [442, 350, 45, 327], [144, 426, 140, 421], [52, 354, 415, 356], [12, 264, 365, 212], [352, 281, 230, 409], [419, 112, 392, 219, 106, 161, 107, 364], [121, 181, 331, 106, 330, 32, 93, 94]], ![[280, 341, 69, 376, 339, 48, 444, 53], [167, 248, 288, 393], [139, 6, 48, 447], [54, 117, 200, 251], [365, 88, 230, 202], [72, 70, 276, 199], [82, 139, 313, 293, 308, 430, 38, 7], [92, 158, 39, 40, 383, 214, 326, 417]], ![[351, 214, 36, 157, 218, 176, 297, 41], [6, 139, 311, 250], [33, 75, 445, 134], [239, 138, 22, 371], [428, 176, 132, 88], [237, 10, 333, 417], [7, 349, 8, 166, 239, 420, 252, 360], [321, 143, 77, 356, 286, 415, 133, 45]]]
 h' := ![![[30, 283, 114, 79, 120], [225, 227, 286, 142, 12], [282, 52, 114, 229, 239], [442, 192, 314, 92, 103], [424, 65, 303, 28, 132], [431, 226, 354, 437, 315], [90, 52, 171, 191, 310], [0, 0, 0, 1], [0, 1]], ![[215, 194, 262, 233, 38], [82, 13, 314, 89, 318], [275, 115, 44, 162, 218], [287, 229, 27, 221, 291], [177, 184, 421, 198, 374], [82, 118, 446, 408, 261], [240, 432, 287, 297, 39], [423, 415, 253, 299, 22], [30, 283, 114, 79, 120]], ![[295, 239, 102, 29, 164], [317, 251, 423, 288, 148], [433, 107, 182, 314, 35], [285, 358, 143, 419, 337], [434, 16, 42, 368, 51], [346, 393, 445, 44, 86], [286, 140, 360, 408, 233], [245, 352, 16, 107, 98], [215, 194, 262, 233, 38]], ![[144, 181, 420, 108, 127], [61, 397, 329, 415, 61], [364, 112, 370, 211, 217], [439, 130, 202, 324, 235], [334, 289, 329, 346, 196], [282, 206, 279, 342, 162], [244, 339, 161, 26, 358], [319, 138, 197, 323, 316], [295, 239, 102, 29, 164]], ![[0, 1], [132, 10, 444, 413, 359], [171, 63, 188, 431, 189], [162, 438, 212, 291, 381], [240, 344, 252, 407, 145], [147, 404, 272, 116, 74], [360, 384, 368, 425, 407], [159, 442, 432, 168, 13], [144, 181, 420, 108, 127]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [256, 313, 154, 357], [], [], []]
 b := ![[], [163, 153, 303, 119, 345], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI449N0 : CertifiedPrimeIdeal' SI449N0 449 where
  n := 5
  hpos := by decide
  P := [137, 191, 2, 369, 214, 1]
  hirr := P449P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1308563804, 3284906899, -1162817057, -4151643927, -293701676]
  a := ![-1, -3, 1, -1, 2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2914396, 7316051, -2589793, -9246423, -654124]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI449N0 : Ideal.IsPrime I449N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI449N0 B_one_repr
lemma NI449N0 : Nat.card (O ⧸ I449N0) = 18248690477249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI449N0

def PBC449 : ContainsPrimesAboveP 449 ![I449N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI449N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![449, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 449 (by decide) 𝕀

instance hp457 : Fact (Nat.Prime 457) := {out := by norm_num}

def I457N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-173, -102, 44, 8, 16]] i)))

def SI457N0: IdealEqSpanCertificate' Table ![![-173, -102, 44, 8, 16]] 
 ![![457, 0, 0, 0, 0], ![0, 457, 0, 0, 0], ![59, 332, 1, 0, 0], ![438, 134, 0, 1, 0], ![322, 99, 0, 0, 1]] where
  M :=![![![-173, -102, 44, 8, 16], ![96, 67, -42, -48, 8], ![48, 216, -43, -252, -48], ![-72, -220, 110, 353, -18], ![-276, -786, 116, 732, 251]]]
  hmulB := by decide  
  f := ![![![-55757, -93178, 29608, -13528, 11216]], ![![67296, 112483, -35690, 16344, -13528]], ![![41513, 69390, -22011, 10084, -8344]], ![![-33582, -56114, 17846, -8143, 6758]], ![![-24662, -41209, 13106, -5980, 4963]]]
  g := ![![![-25, -38, 44, 8, 16], ![46, 43, -42, -48, 8], ![281, 116, -43, -252, -48], ![-340, -180, 110, 353, -18], ![-894, -355, 116, 732, 251]]]
  hle1 := by decide   
  hle2 := by decide  


def P457P0 : CertificateIrreducibleZModOfList' 457 2 2 8 [4, 173, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [284, 456], [0, 1]]
 g := ![![[386, 343], [361], [268], [446, 445], [18], [441], [72, 415], [284, 1]], ![[0, 114], [361], [268], [237, 12], [18], [441], [26, 42], [111, 456]]]
 h' := ![![[284, 456], [142, 228], [407, 438], [44, 106], [64, 380], [291, 240], [169, 436], [235, 220], [0, 1]], ![[0, 1], [0, 229], [38, 19], [443, 351], [132, 77], [358, 217], [146, 21], [106, 237], [284, 456]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [290]]
 b := ![[], [432, 145]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI457N0 : CertifiedPrimeIdeal' SI457N0 457 where
  n := 2
  hpos := by decide
  P := [4, 173, 1]
  hirr := P457P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![994, 1162, 238, -2142, 608]
  a := ![3, 0, 3, -4, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1596, 326, 238, -2142, 608]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI457N0 : Ideal.IsPrime I457N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI457N0 B_one_repr
lemma NI457N0 : Nat.card (O ⧸ I457N0) = 208849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI457N0

def I457N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-151, -242, 85, -33, 31]] i)))

def SI457N1: IdealEqSpanCertificate' Table ![![-151, -242, 85, -33, 31]] 
 ![![457, 0, 0, 0, 0], ![0, 457, 0, 0, 0], ![233, 373, 1, 0, 0], ![175, 352, 0, 1, 0], ![88, 96, 0, 0, 1]] where
  M :=![![![-151, -242, 85, -33, 31], ![186, 314, -78, 51, -33], ![-198, -309, 161, -27, 51], ![150, 249, -81, 35, -30], ![72, 138, 9, 27, -4]]]
  hmulB := by decide  
  f := ![![![-151, -88, 41, 9, 11]], ![![66, 14, -18, 21, 9]], ![![-23, -33, 6, 21, 13]], ![![-7, -23, 2, 20, 11]], ![![-16, -16, 5, 9, 4]]]
  g := ![![![-37, -51, 85, -33, 31], ![27, 32, -78, 51, -33], ![-82, -122, 161, -27, 51], ![34, 46, -81, 35, -30], ![-14, -27, 9, 27, -4]]]
  hle1 := by decide   
  hle2 := by decide  


def P457P1 : CertificateIrreducibleZModOfList' 457 2 2 8 [369, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [435, 456], [0, 1]]
 g := ![![[114, 3], [50], [262], [17, 65], [330], [338], [454, 429], [435, 1]], ![[48, 454], [50], [262], [415, 392], [330], [338], [156, 28], [413, 456]]]
 h' := ![![[435, 456], [220, 312], [293, 57], [125, 292], [113, 61], [271, 70], [193, 126], [349, 115], [0, 1]], ![[0, 1], [211, 145], [410, 400], [99, 165], [142, 396], [102, 387], [163, 331], [104, 342], [435, 456]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [293]]
 b := ![[], [12, 375]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI457N1 : CertifiedPrimeIdeal' SI457N1 457 where
  n := 2
  hpos := by decide
  P := [369, 22, 1]
  hirr := P457P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1046, 1396, -1157, -3004, 953]
  a := ![1, 1, 1, -1, 4]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1559, 3061, -1157, -3004, 953]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI457N1 : Ideal.IsPrime I457N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI457N1 B_one_repr
lemma NI457N1 : Nat.card (O ⧸ I457N1) = 208849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI457N1

def I457N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-193, -324, 103, -47, 39]] i)))

def SI457N2: IdealEqSpanCertificate' Table ![![-193, -324, 103, -47, 39]] 
 ![![457, 0, 0, 0, 0], ![209, 1, 0, 0, 0], ![191, 0, 1, 0, 0], ![411, 0, 0, 1, 0], ![70, 0, 0, 0, 1]] where
  M :=![![![-193, -324, 103, -47, 39], ![234, 392, -124, 57, -47], ![-282, -471, 151, -69, 57], ![198, 331, -105, 49, -40], ![72, 120, -37, 21, -14]]]
  hmulB := by decide  
  f := ![![![791, 442, -169, 31, -57]], ![![361, 202, -77, 14, -26]], ![![331, 185, -70, 14, -24]], ![![711, 397, -152, 28, -51]], ![![122, 70, -27, 1, -8]]]
  g := ![![![141, -324, 103, -47, 39], ![-171, 392, -124, 57, -47], ![205, -471, 151, -69, 57], ![-145, 331, -105, 49, -40], ![-56, 120, -37, 21, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI457N2 : Nat.card (O ⧸ I457N2) = 457 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI457N2)

lemma isPrimeI457N2 : Ideal.IsPrime I457N2 := prime_ideal_of_norm_prime hp457.out _ NI457N2
def MulI457N0 : IdealMulLeCertificate' Table 
  ![![-173, -102, 44, 8, 16]] ![![-151, -242, 85, -33, 31]]
  ![![791, 442, -169, 31, -57]] where
 M := ![![![791, 442, -169, 31, -57]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI457N1 : IdealMulLeCertificate' Table 
  ![![791, 442, -169, 31, -57]] ![![-193, -324, 103, -47, 39]]
  ![![457, 0, 0, 0, 0]] where
 M := ![![![457, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC457 : ContainsPrimesAboveP 457 ![I457N0, I457N1, I457N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI457N0
    exact isPrimeI457N1
    exact isPrimeI457N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 457 (by decide) (𝕀 ⊙ MulI457N0 ⊙ MulI457N1)
instance hp461 : Fact (Nat.Prime 461) := {out := by norm_num}

def I461N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 70, -159, -279, 21]] i)))

def SI461N0: IdealEqSpanCertificate' Table ![![37, 70, -159, -279, 21]] 
 ![![461, 0, 0, 0, 0], ![0, 461, 0, 0, 0], ![0, 0, 461, 0, 0], ![52, 308, 219, 1, 0], ![56, 100, 136, 0, 1]] where
  M :=![![![37, 70, -159, -279, 21], ![126, 352, -212, -495, -279], ![-1674, -4059, 1327, 5235, -495], ![342, 513, -1219, -2423, 1120], ![6072, 14622, -7531, -22239, 442]]]
  hmulB := by decide  
  f := ![![![-330199, -175964, 78005, -14205, 27969]], ![![167814, 89336, -39620, 7203, -14205]], ![![-85230, -45261, 20093, -3639, 7203]], ![![34492, 18394, -8152, 1486, -2923]], ![![-28768, -15304, 6789, -1233, 2434]]]
  g := ![![![29, 182, 126, -279, 21], ![90, 392, 317, -495, -279], ![-534, -3399, -2338, 5235, -495], ![138, 1377, 818, -2423, 1120], ![2468, 14794, 10418, -22239, 442]]]
  hle1 := by decide   
  hle2 := by decide  


def P461P0 : CertificateIrreducibleZModOfList' 461 3 2 8 [46, 307, 137, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [318, 252, 114], [6, 208, 347], [0, 1]]
 g := ![![[414, 186, 346], [84, 104], [267, 12, 157], [130, 421, 262], [405, 196], [402, 320], [136, 321, 329], [1]], ![[97, 359, 0, 1], [77, 368], [247, 379, 387, 416], [132, 282, 30, 25], [154, 169], [333, 166], [10, 274, 372, 142], [370, 227, 1, 351]], ![[106, 120, 387, 311], [403, 5], [99, 306, 42, 109], [198, 409, 313, 249], [126, 1], [280, 164], [313, 231, 439, 96], [297, 399, 196, 110]]]
 h' := ![![[318, 252, 114], [311, 105, 231], [165, 167, 330], [13, 261, 247], [438, 344, 359], [428, 426, 447], [198, 457, 117], [415, 154, 324], [0, 1]], ![[6, 208, 347], [326, 423, 88], [258, 410, 88], [446, 393, 455], [103, 387, 21], [415, 134, 13], [360, 293, 369], [414, 247, 124], [318, 252, 114]], ![[0, 1], [290, 394, 142], [237, 345, 43], [380, 268, 220], [233, 191, 81], [6, 362, 1], [431, 172, 436], [384, 60, 13], [6, 208, 347]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 170], []]
 b := ![[], [382, 406, 136], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI461N0 : CertifiedPrimeIdeal' SI461N0 461 where
  n := 3
  hpos := by decide
  P := [46, 307, 137, 1]
  hirr := P461P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2576, -2213, 1161, 4717, -218]
  a := ![4, 0, 0, 1, 0]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-500, -3109, -2174, 4717, -218]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI461N0 : Ideal.IsPrime I461N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI461N0 B_one_repr
lemma NI461N0 : Nat.card (O ⧸ I461N0) = 97972181 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI461N0

def I461N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![330199, 175964, -78005, 14205, -27969]] i)))

def SI461N1: IdealEqSpanCertificate' Table ![![330199, 175964, -78005, 14205, -27969]] 
 ![![461, 0, 0, 0, 0], ![0, 461, 0, 0, 0], ![124, 72, 1, 0, 0], ![294, 350, 0, 1, 0], ![18, 188, 0, 0, 1]] where
  M :=![![![330199, 175964, -78005, 14205, -27969], ![-167814, -89336, 39620, -7203, 14205], ![85230, 45261, -20093, 3639, -7203], ![-49818, -26433, 11739, -2123, 4208], ![-38976, -20736, 9199, -1671, 3298]]]
  hmulB := by decide  
  f := ![![![-37, -70, 159, 279, -21]], ![![-126, -352, 212, 495, 279]], ![![-26, -65, 73, 141, 39]], ![![-120, -313, 265, 559, 196]], ![![-66, -178, 109, 261, 112]]]
  g := ![![![13731, 13186, -78005, 14205, -27969], ![-6982, -6706, 39620, -7203, 14205], ![3550, 3411, -20093, 3639, -7203], ![-2076, -1995, 11739, -2123, 4208], ![-1622, -1558, 9199, -1671, 3298]]]
  hle1 := by decide   
  hle2 := by decide  


def P461P1 : CertificateIrreducibleZModOfList' 461 2 2 8 [441, 364, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [97, 460], [0, 1]]
 g := ![![[74, 23], [229], [75, 216], [271, 126], [403], [202], [27, 347], [97, 1]], ![[0, 438], [229], [282, 245], [46, 335], [403], [202], [33, 114], [194, 460]]]
 h' := ![![[97, 460], [290, 439], [117, 167], [349, 157], [182, 204], [139, 147], [79, 335], [96, 209], [0, 1]], ![[0, 1], [0, 22], [181, 294], [365, 304], [147, 257], [107, 314], [304, 126], [85, 252], [97, 460]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [413]]
 b := ![[], [242, 437]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI461N1 : CertifiedPrimeIdeal' SI461N1 461 where
  n := 2
  hpos := by decide
  P := [441, 364, 1]
  hirr := P461P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![18356, 34566, -26396, -57846, 11391]
  a := ![7, 2, -24, 0, -23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![43586, 43470, -26396, -57846, 11391]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI461N1 : Ideal.IsPrime I461N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI461N1 B_one_repr
lemma NI461N1 : Nat.card (O ⧸ I461N1) = 212521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI461N1
def MulI461N0 : IdealMulLeCertificate' Table 
  ![![37, 70, -159, -279, 21]] ![![330199, 175964, -78005, 14205, -27969]]
  ![![461, 0, 0, 0, 0]] where
 M := ![![![-461, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC461 : ContainsPrimesAboveP 461 ![I461N0, I461N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI461N0
    exact isPrimeI461N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 461 (by decide) (𝕀 ⊙ MulI461N0)
instance hp463 : Fact (Nat.Prime 463) := {out := by norm_num}

def I463N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10079, -5439, 2303, -468, 840]] i)))

def SI463N0: IdealEqSpanCertificate' Table ![![-10079, -5439, 2303, -468, 840]] 
 ![![463, 0, 0, 0, 0], ![0, 463, 0, 0, 0], ![0, 0, 463, 0, 0], ![0, 0, 0, 463, 0], ![381, 144, 377, 350, 1]] where
  M :=![![![-10079, -5439, 2303, -468, 840], ![5040, 2521, -1422, 102, -468], ![-2808, -1980, 25, -414, 102], ![1506, 777, -329, 133, -120], ![990, 57, -825, -228, -125]]]
  hmulB := by decide  
  f := ![![![-149, -249, 79, -36, 30]], ![![180, 301, -96, 42, -36]], ![![-216, -360, 115, -54, 42]], ![![150, 249, -79, 43, -30]], ![![-129, -216, 69, -28, 25]]]
  g := ![![![-713, -273, -679, -636, 840], ![396, 151, 378, 354, -468], ![-90, -36, -83, -78, 102], ![102, 39, 97, 91, -120], ![105, 39, 100, 94, -125]]]
  hle1 := by decide   
  hle2 := by decide  


def P463P0 : CertificateIrreducibleZModOfList' 463 4 2 8 [206, 192, 164, 399, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [430, 441, 30, 55], [444, 62, 138, 35], [116, 422, 295, 373], [0, 1]]
 g := ![![[380, 1, 313, 453], [347, 346, 378, 189], [37, 293, 82, 36], [345, 315, 295, 271], [157, 271, 451], [380, 80, 264], [200, 228, 64, 1], []], ![[258, 236, 151, 448, 172, 277], [249, 278, 239, 142, 147, 261], [108, 376, 154, 332, 349, 211], [331, 282, 377, 277, 179, 334], [387, 395, 185], [263, 350, 247], [21, 272, 342, 151, 454, 100], [197, 434, 410, 74, 395, 158]], ![[161, 303, 55, 53, 245, 370], [395, 313, 13, 287, 310, 70], [185, 2, 211, 163, 400, 230], [177, 185, 113, 331, 31, 389], [330, 302, 77], [322, 226, 425], [168, 253, 376, 322, 238, 65], [162, 115, 303, 69, 427, 279]], ![[179, 182, 223, 96, 249, 33], [22, 317, 63, 358, 133, 246], [183, 406, 122, 61, 309, 336], [74, 221, 92, 401, 8, 361], [22, 24, 57], [292, 247, 409], [131, 389, 276, 423, 427, 255], [360, 451, 362, 98, 381, 225]]]
 h' := ![![[430, 441, 30, 55], [283, 33, 220, 180], [249, 252, 194, 397], [232, 237, 108, 457], [324, 196, 440, 119], [16, 233, 251, 86], [7, 287, 62, 417], [0, 0, 0, 1], [0, 1]], ![[444, 62, 138, 35], [368, 94, 133, 436], [353, 275, 108, 131], [50, 67, 257, 196], [160, 220, 367, 385], [264, 62, 418, 50], [344, 255, 452, 408], [339, 451, 10, 414], [430, 441, 30, 55]], ![[116, 422, 295, 373], [98, 268, 285, 193], [449, 365, 452, 203], [210, 34, 199, 208], [250, 57, 26, 73], [450, 457, 136, 143], [306, 457, 311, 305], [50, 314, 313, 122], [444, 62, 138, 35]], ![[0, 1], [346, 68, 288, 117], [440, 34, 172, 195], [15, 125, 362, 65], [74, 453, 93, 349], [327, 174, 121, 184], [446, 390, 101, 259], [43, 161, 140, 389], [116, 422, 295, 373]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [280, 372, 336], []]
 b := ![[], [], [209, 77, 131, 83], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI463N0 : CertifiedPrimeIdeal' SI463N0 463 where
  n := 4
  hpos := by decide
  P := [206, 192, 164, 399, 1]
  hirr := P463P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![705641966, 1809111667, -561940446, -2133221313, -313349257]
  a := ![1, 3, -8, -1, -9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![259377341, 101363725, 253932461, 232265699, -313349257]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI463N0 : Ideal.IsPrime I463N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI463N0 B_one_repr
lemma NI463N0 : Nat.card (O ⧸ I463N0) = 45954068161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI463N0

def I463N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-149, -249, 79, -36, 30]] i)))

def SI463N1: IdealEqSpanCertificate' Table ![![-149, -249, 79, -36, 30]] 
 ![![463, 0, 0, 0, 0], ![113, 1, 0, 0, 0], ![195, 0, 1, 0, 0], ![397, 0, 0, 1, 0], ![47, 0, 0, 0, 1]] where
  M :=![![![-149, -249, 79, -36, 30], ![180, 301, -96, 42, -36], ![-216, -360, 115, -54, 42], ![150, 249, -79, 43, -30], ![54, 87, -33, 12, -5]]]
  hmulB := by decide  
  f := ![![![-10079, -5439, 2303, -468, 840]], ![![-2449, -1322, 559, -114, 204]], ![![-4251, -2295, 970, -198, 354]], ![![-8639, -4662, 1974, -401, 720]], ![![-1021, -552, 232, -48, 85]]]
  g := ![![![55, -249, 79, -36, 30], ![-65, 301, -96, 42, -36], ![81, -360, 115, -54, 42], ![-61, 249, -79, 43, -30], ![-17, 87, -33, 12, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI463N1 : Nat.card (O ⧸ I463N1) = 463 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI463N1)

lemma isPrimeI463N1 : Ideal.IsPrime I463N1 := prime_ideal_of_norm_prime hp463.out _ NI463N1
def MulI463N0 : IdealMulLeCertificate' Table 
  ![![-10079, -5439, 2303, -468, 840]] ![![-149, -249, 79, -36, 30]]
  ![![463, 0, 0, 0, 0]] where
 M := ![![![463, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC463 : ContainsPrimesAboveP 463 ![I463N0, I463N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI463N0
    exact isPrimeI463N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 463 (by decide) (𝕀 ⊙ MulI463N0)


lemma PB1556I9_primes (p : ℕ) :
  p ∈ Set.range ![421, 431, 433, 439, 443, 449, 457, 461, 463] ↔ Nat.Prime p ∧ 419 < p ∧ p ≤ 463 := by
  rw [← List.mem_ofFn']
  convert primes_range 419 463 (by omega)

def PB1556I9 : PrimesBelowBoundCertificateInterval O 419 463 1556 where
  m := 9
  g := ![2, 2, 3, 4, 3, 1, 3, 2, 2]
  P := ![421, 431, 433, 439, 443, 449, 457, 461, 463]
  hP := PB1556I9_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I421N0, I421N1]
    · exact ![I431N0, I431N1]
    · exact ![I433N0, I433N1, I433N2]
    · exact ![I439N0, I439N1, I439N2, I439N3]
    · exact ![I443N0, I443N1, I443N2]
    · exact ![I449N0]
    · exact ![I457N0, I457N1, I457N2]
    · exact ![I461N0, I461N1]
    · exact ![I463N0, I463N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC421
    · exact PBC431
    · exact PBC433
    · exact PBC439
    · exact PBC443
    · exact PBC449
    · exact PBC457
    · exact PBC461
    · exact PBC463
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![74618461, 177241]
    · exact ![80062991, 185761]
    · exact ![81182737, 433, 433]
    · exact ![192721, 439, 439, 439]
    · exact ![86938307, 443, 443]
    · exact ![18248690477249]
    · exact ![208849, 208849, 457]
    · exact ![97972181, 212521]
    · exact ![45954068161, 463]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI421N0
      exact NI421N1
    · dsimp ; intro j
      fin_cases j
      exact NI431N0
      exact NI431N1
    · dsimp ; intro j
      fin_cases j
      exact NI433N0
      exact NI433N1
      exact NI433N2
    · dsimp ; intro j
      fin_cases j
      exact NI439N0
      exact NI439N1
      exact NI439N2
      exact NI439N3
    · dsimp ; intro j
      fin_cases j
      exact NI443N0
      exact NI443N1
      exact NI443N2
    · dsimp ; intro j
      fin_cases j
      exact NI449N0
    · dsimp ; intro j
      fin_cases j
      exact NI457N0
      exact NI457N1
      exact NI457N2
    · dsimp ; intro j
      fin_cases j
      exact NI461N0
      exact NI461N1
    · dsimp ; intro j
      fin_cases j
      exact NI463N0
      exact NI463N1
  β := ![I433N1, I433N2, I439N1, I439N2, I439N3, I443N1, I443N2, I457N2, I463N1]
  Il := ![[], [], [I433N1, I433N2], [I439N1, I439N2, I439N3], [I443N1, I443N2], [], [I457N2], [], [I463N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
