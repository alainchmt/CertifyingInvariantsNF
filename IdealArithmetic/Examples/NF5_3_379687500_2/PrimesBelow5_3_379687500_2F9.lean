
import IdealArithmetic.Examples.NF5_3_379687500_2.RI5_3_379687500_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp421 : Fact (Nat.Prime 421) := {out := by norm_num}

def I421N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![421, 0, 0, 0, 0]] i)))

def SI421N0: IdealEqSpanCertificate' Table ![![421, 0, 0, 0, 0]] 
 ![![421, 0, 0, 0, 0], ![0, 421, 0, 0, 0], ![0, 0, 421, 0, 0], ![0, 0, 0, 421, 0], ![0, 0, 0, 0, 421]] where
  M :=![![![421, 0, 0, 0, 0], ![0, 421, 0, 0, 0], ![0, 0, 421, 0, 0], ![0, 0, 0, 421, 0], ![0, 0, 0, 0, 421]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P421P0 : CertificateIrreducibleZModOfList' 421 5 2 8 [56, 75, 250, 394, 111, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [311, 20, 203, 18, 245], [114, 319, 274, 212, 297], [169, 33, 35, 326, 324], [137, 48, 330, 286, 397], [0, 1]]
 g := ![![[17, 390, 419, 310, 132], [68, 279, 417, 231], [91, 117, 136, 250, 192], [52, 321, 286, 252], [276, 100, 215, 35], [193, 255, 293, 322, 376], [310, 1], []], ![[414, 402, 256, 255, 105, 369, 286, 339], [8, 198, 276, 353], [319, 98, 208, 173, 145, 215, 132, 49], [50, 409, 191, 176], [286, 169, 237, 282], [103, 114, 328, 390, 339, 380, 318, 15], [109, 31, 251, 38], [213, 193, 169, 317, 114, 377, 123, 174]], ![[277, 289, 285, 387, 224, 156, 6, 256], [244, 23, 244, 245], [52, 348, 142, 236, 266, 368, 179, 146], [125, 261, 375, 274], [353, 34, 107, 67], [144, 303, 58, 342, 328, 181, 109, 314], [364, 166, 108, 140], [181, 321, 313, 167, 359, 254, 396, 85]], ![[388, 91, 253, 352, 33, 85, 74, 404], [359, 224, 97, 314], [196, 121, 87, 405, 246, 312, 47, 234], [299, 272, 339, 342], [206, 104, 274, 340], [135, 271, 135, 87, 226, 158, 380, 132], [361, 49, 131, 101], [300, 327, 14, 323, 72, 248, 415, 55]], ![[274, 59, 289, 105, 169, 2, 138, 331], [164, 164, 207, 152], [357, 42, 241, 165, 140, 366, 207, 168], [320, 154, 404, 16], [215, 276, 68, 375], [303, 192, 292, 111, 365, 252, 122, 295], [254, 122, 8, 93], [299, 43, 234, 35, 193, 225, 294, 69]]]
 h' := ![![[311, 20, 203, 18, 245], [233, 129, 130, 215, 72], [377, 74, 393, 35, 264], [20, 420, 360, 228, 171], [220, 265, 358, 235, 44], [138, 412, 3, 121, 344], [322, 270, 310, 121, 139], [0, 0, 0, 1], [0, 1]], ![[114, 319, 274, 212, 297], [263, 16, 99, 146, 290], [106, 365, 287, 389, 61], [266, 252, 255, 245, 381], [31, 271, 157, 160, 184], [414, 88, 137, 245, 91], [266, 256, 245, 408, 230], [62, 357, 185, 402, 248], [311, 20, 203, 18, 245]], ![[169, 33, 35, 326, 324], [130, 1, 326, 319, 312], [213, 213, 291, 31, 137], [108, 92, 296, 391, 397], [218, 118, 175, 226, 287], [48, 310, 259, 301, 151], [414, 395, 340, 204, 179], [13, 14, 7, 18, 154], [114, 319, 274, 212, 297]], ![[137, 48, 330, 286, 397], [282, 386, 43, 354, 411], [52, 112, 321, 223, 34], [348, 351, 3, 385, 382], [377, 257, 219, 159, 323], [158, 240, 8, 153, 160], [312, 105, 168, 187, 4], [84, 128, 203, 82, 331], [169, 33, 35, 326, 324]], ![[0, 1], [310, 310, 244, 229, 178], [361, 78, 392, 164, 346], [227, 148, 349, 14, 353], [92, 352, 354, 62, 4], [240, 213, 14, 22, 96], [30, 237, 200, 343, 290], [402, 343, 26, 339, 109], [137, 48, 330, 286, 397]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [103, 87, 122, 265], [], [], []]
 b := ![[], [217, 152, 300, 257, 334], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI421N0 : CertifiedPrimeIdeal' SI421N0 421 where
  n := 5
  hpos := by decide
  P := [56, 75, 250, 394, 111, 1]
  hirr := P421P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4743097270076449, 5297075124886980, 305841507730689, -1958764753310837, -11884812106027763]
  a := ![935, 890, 79, -369, -2189]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![11266264299469, 12582126187380, 726464388909, -4652647870097, -28229957496503]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI421N0 : Ideal.IsPrime I421N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI421N0 B_one_repr
lemma NI421N0 : Nat.card (O ⧸ I421N0) = 13225450646101 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI421N0

def PBC421 : ContainsPrimesAboveP 421 ![I421N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI421N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![421, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 421 (by decide) 𝕀

instance hp431 : Fact (Nat.Prime 431) := {out := by norm_num}

def I431N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10751, -6035, -672, 2339, 13554]] i)))

def SI431N0: IdealEqSpanCertificate' Table ![![-10751, -6035, -672, 2339, 13554]] 
 ![![431, 0, 0, 0, 0], ![0, 431, 0, 0, 0], ![240, 109, 1, 0, 0], ![161, 159, 0, 1, 0], ![421, 219, 0, 0, 1]] where
  M :=![![![-10751, -6035, -672, 2339, 13554], ![-18118, -10157, -1130, 3936, 22804], ![-30608, -17238, -1915, 6672, 38660], ![-10576, -5877, -669, 2295, 13288], ![-11412, -6413, -711, 2482, 14383]]]
  hmulB := by decide  
  f := ![![![-2525, -1694, -89, 821, 4546]], ![![-12282, -8239, -460, 4002, 22176]], ![![-4650, -3119, -171, 1514, 8388]], ![![-5731, -3842, -212, 1866, 10338]], ![![-8687, -5828, -320, 2829, 15673]]]
  g := ![![![-13764, -7594, -672, 2339, 13554], ![-23158, -12777, -1130, 3936, 22804], ![-39260, -21661, -1915, 6672, 38660], ![-13489, -7443, -669, 2295, 13288], ![-14607, -8059, -711, 2482, 14383]]]
  hle1 := by decide   
  hle2 := by decide  


def P431P0 : CertificateIrreducibleZModOfList' 431 2 2 8 [347, 336, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [95, 430], [0, 1]]
 g := ![![[427, 118], [223, 314], [292, 58], [56, 54], [32], [342, 288], [347], [95, 1]], ![[0, 313], [314, 117], [199, 373], [14, 377], [32], [118, 143], [347], [190, 430]]]
 h' := ![![[95, 430], [199, 379], [392, 363], [394, 187], [322, 47], [282, 321], [421, 101], [222, 58], [0, 1]], ![[0, 1], [0, 52], [397, 68], [57, 244], [46, 384], [176, 110], [103, 330], [129, 373], [95, 430]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [228]]
 b := ![[], [188, 114]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI431N0 : CertifiedPrimeIdeal' SI431N0 431 where
  n := 2
  hpos := by decide
  P := [347, 336, 1]
  hirr := P431P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2669664, -2900598, -194876, 1094474, 6611588]
  a := ![-1313, -1315, -111, 518, 3074]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6764706, -3720692, -194876, 1094474, 6611588]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI431N0 : Ideal.IsPrime I431N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI431N0 B_one_repr
lemma NI431N0 : Nat.card (O ⧸ I431N0) = 185761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI431N0

def I431N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11003, -7346, -401, 3573, 19804]] i)))

def SI431N1: IdealEqSpanCertificate' Table ![![-11003, -7346, -401, 3573, 19804]] 
 ![![431, 0, 0, 0, 0], ![80, 1, 0, 0, 0], ![65, 0, 1, 0, 0], ![169, 0, 0, 1, 0], ![422, 0, 0, 0, 1]] where
  M :=![![![-11003, -7346, -401, 3573, 19804], ![-52898, -35317, -1930, 17172, 95186], ![-254032, -169554, -9269, 82446, 456994], ![-482978, -322449, -17631, 156759, 868958], ![38462, 25681, 1405, -12482, -69195]]]
  hmulB := by decide  
  f := ![![![19303, 20551, 3678, -8805, -52488]], ![![3646, 3759, 680, -1626, -9714]], ![![2293, 2611, 457, -1097, -6510]], ![![7933, 8972, 1575, -3778, -22430]], ![![18870, 19953, 3579, -8566, -51087]]]
  g := ![![![-19393, -7346, -401, 3573, 19804], ![-93208, -35317, -1930, 17172, 95186], ![-447499, -169554, -9269, 82446, 456994], ![-850890, -322449, -17631, 156759, 868958], ![67755, 25681, 1405, -12482, -69195]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI431N1 : Nat.card (O ⧸ I431N1) = 431 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI431N1)

lemma isPrimeI431N1 : Ideal.IsPrime I431N1 := prime_ideal_of_norm_prime hp431.out _ NI431N1

def I431N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, 7, 2, 1, 4]] i)))

def SI431N2: IdealEqSpanCertificate' Table ![![9, 7, 2, 1, 4]] 
 ![![431, 0, 0, 0, 0], ![257, 1, 0, 0, 0], ![325, 0, 1, 0, 0], ![313, 0, 0, 1, 0], ![66, 0, 0, 0, 1]] where
  M :=![![![9, 7, 2, 1, 4], ![-58, -41, 6, 26, 130], ![-780, -630, -35, 298, 1638], ![-2008, -1281, -93, 641, 3610], ![264, 163, 17, -78, -449]]]
  hmulB := by decide  
  f := ![![![168707, 270196, 16013, -85773, -551472]], ![![98603, 157919, 9359, -50131, -322314]], ![![137385, 220034, 13040, -69849, -449090]], ![![91511, 146555, 8686, -46524, -299122]], ![![31112, 49829, 2953, -15818, -101701]]]
  g := ![![![-7, 7, 2, 1, 4], ![-19, -41, 6, 26, 130], ![-67, -630, -35, 298, 1638], ![-189, -1281, -93, 641, 3610], ![16, 163, 17, -78, -449]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI431N2 : Nat.card (O ⧸ I431N2) = 431 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI431N2)

lemma isPrimeI431N2 : Ideal.IsPrime I431N2 := prime_ideal_of_norm_prime hp431.out _ NI431N2

def I431N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1037, -1625, -97, 518, 3324]] i)))

def SI431N3: IdealEqSpanCertificate' Table ![![-1037, -1625, -97, 518, 3324]] 
 ![![431, 0, 0, 0, 0], ![416, 1, 0, 0, 0], ![206, 0, 1, 0, 0], ![149, 0, 0, 1, 0], ![124, 0, 0, 0, 1]] where
  M :=![![![-1037, -1625, -97, 518, 3324], ![5012, 8119, 480, -2570, -16544], ![-26332, -41880, -2483, 13324, 85588], ![78858, 126762, 7512, -40187, -258516], ![-13494, -21620, -1282, 6860, 44113]]]
  hmulB := by decide  
  f := ![![![21629, 5539, 2033, -4588, -30384]], ![![20712, 5147, 1928, -4346, -28840]], ![![9966, 2770, 963, -2180, -14356]], ![![8897, 2953, 917, -2091, -13596]], ![![5926, 1342, 536, -1204, -8039]]]
  g := ![![![477, -1625, -97, 518, 3324], ![-2406, 8119, 480, -2570, -16544], ![12318, -41880, -2483, 13324, 85588], ![-37489, 126762, 7512, -40187, -258516], ![6386, -21620, -1282, 6860, 44113]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI431N3 : Nat.card (O ⧸ I431N3) = 431 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI431N3)

lemma isPrimeI431N3 : Ideal.IsPrime I431N3 := prime_ideal_of_norm_prime hp431.out _ NI431N3
def MulI431N0 : IdealMulLeCertificate' Table 
  ![![-10751, -6035, -672, 2339, 13554]] ![![-11003, -7346, -401, 3573, 19804]]
  ![![-129407, -72708, -8070, 28218, 163450]] where
 M := ![![![-129407, -72708, -8070, 28218, 163450]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI431N1 : IdealMulLeCertificate' Table 
  ![![-129407, -72708, -8070, 28218, 163450]] ![![9, 7, 2, 1, 4]]
  ![![-4163943, -2345629, -258236, 913963, 5289602]] where
 M := ![![![-4163943, -2345629, -258236, 913963, 5289602]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI431N2 : IdealMulLeCertificate' Table 
  ![![-4163943, -2345629, -258236, 913963, 5289602]] ![![-1037, -1625, -97, 518, 3324]]
  ![![431, 0, 0, 0, 0]] where
 M := ![![![56991561, 31751770, 3620831, -12153769, -70609006]]]
 hmul := by decide  
 g := ![![![![132231, 73670, 8401, -28199, -163826]]]]
 hle2 := by decide  


def PBC431 : ContainsPrimesAboveP 431 ![I431N0, I431N1, I431N2, I431N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI431N0
    exact isPrimeI431N1
    exact isPrimeI431N2
    exact isPrimeI431N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 431 (by decide) (𝕀 ⊙ MulI431N0 ⊙ MulI431N1 ⊙ MulI431N2)
instance hp433 : Fact (Nat.Prime 433) := {out := by norm_num}

def I433N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9341, -5657, -1268, 2967, 18430]] i)))

def SI433N0: IdealEqSpanCertificate' Table ![![-9341, -5657, -1268, 2967, 18430]] 
 ![![433, 0, 0, 0, 0], ![0, 433, 0, 0, 0], ![369, 183, 1, 0, 0], ![259, 19, 0, 1, 0], ![288, 388, 0, 0, 1]] where
  M :=![![![-9341, -5657, -1268, 2967, 18430], ![11650, 26045, 3860, -9444, -53944], ![95048, 31146, 9733, -22200, -144464], ![-183020, -192345, -34623, 82785, 493976], ![34076, 41851, 7171, -17240, -101817]]]
  hmulB := by decide  
  f := ![![![-3493, -8614, -417, 2643, 17346]], ![![36378, 54029, 3362, -17202, -110268]], ![![12021, 14883, 1030, -4823, -30570]], ![![649, -932, 8, 242, 1774]], ![![30086, 42373, 2717, -13558, -86637]]]
  g := ![![![-12974, -16122, -1268, 2967, 18430], ![38266, 47181, 3860, -9444, -53944], ![101291, 126383, 9733, -22200, -144464], ![-348992, -432083, -34623, 82785, 493976], ![72001, 89058, 7171, -17240, -101817]]]
  hle1 := by decide   
  hle2 := by decide  


def P433P0 : CertificateIrreducibleZModOfList' 433 2 2 8 [290, 135, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [298, 432], [0, 1]]
 g := ![![[426, 109], [383], [222], [385], [169, 53], [97, 144], [216], [298, 1]], ![[0, 324], [383], [222], [385], [375, 380], [142, 289], [216], [163, 432]]]
 h' := ![![[298, 432], [195, 242], [150, 88], [130, 39], [352, 144], [15, 273], [70, 421], [180, 182], [0, 1]], ![[0, 1], [0, 191], [394, 345], [61, 394], [397, 289], [398, 160], [391, 12], [291, 251], [298, 432]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [360]]
 b := ![[], [26, 180]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI433N0 : CertifiedPrimeIdeal' SI433N0 433 where
  n := 2
  hpos := by decide
  P := [290, 135, 1]
  hirr := P433P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7396, -5523, 98, 2189, 12742]
  a := ![129, 120, 11, -51, -302]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-9885, -11568, 98, 2189, 12742]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI433N0 : Ideal.IsPrime I433N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI433N0 B_one_repr
lemma NI433N0 : Nat.card (O ⧸ I433N0) = 187489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI433N0

def I433N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-93, -94, -12, 36, 206]] i)))

def SI433N1: IdealEqSpanCertificate' Table ![![-93, -94, -12, 36, 206]] 
 ![![433, 0, 0, 0, 0], ![0, 433, 0, 0, 0], ![28, 85, 1, 0, 0], ![95, 256, 0, 1, 0], ![117, 6, 0, 0, 1]] where
  M :=![![![-93, -94, -12, 36, 206], ![-352, -157, -28, 86, 526], ![108, 444, 103, -166, -1014], ![-140, -918, -54, 285, 1442], ![-176, 50, -6, 4, 67]]]
  hmulB := by decide  
  f := ![![![3195, 5146, 304, -1632, -10498]], ![![-16504, -26365, -1564, 8374, 53830]], ![![-2840, -4533, -269, 1440, 9256]], ![![-9647, -15404, -914, 4893, 31452]], ![![735, 1186, 70, -376, -2419]]]
  g := ![![![-63, -22, -12, 36, 206], ![-160, -53, -28, 86, 526], ![304, 93, 103, -166, -1014], ![-449, -180, -54, 285, 1442], ![-19, -2, -6, 4, 67]]]
  hle1 := by decide   
  hle2 := by decide  


def P433P1 : CertificateIrreducibleZModOfList' 433 2 2 8 [230, 276, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [157, 432], [0, 1]]
 g := ![![[261, 401], [383], [415], [218], [8, 164], [154, 385], [230], [157, 1]], ![[0, 32], [383], [415], [218], [209, 269], [412, 48], [230], [314, 432]]]
 h' := ![![[157, 432], [401, 276], [67, 345], [61, 207], [325, 376], [86, 233], [156, 144], [262, 171], [0, 1]], ![[0, 1], [0, 157], [107, 88], [85, 226], [36, 57], [295, 200], [248, 289], [263, 262], [157, 432]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [282]]
 b := ![[], [406, 141]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI433N1 : CertifiedPrimeIdeal' SI433N1 433 where
  n := 2
  hpos := by decide
  P := [230, 276, 1]
  hirr := P433P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3247985, -2993068, -198627, 1216390, 7239548]
  a := ![-1401, -1316, -119, 552, 3280]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2217715, -787397, -198627, 1216390, 7239548]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI433N1 : Ideal.IsPrime I433N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI433N1 B_one_repr
lemma NI433N1 : Nat.card (O ⧸ I433N1) = 187489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI433N1

def I433N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![27, 41, 7, -16, -94]] i)))

def SI433N2: IdealEqSpanCertificate' Table ![![27, 41, 7, -16, -94]] 
 ![![433, 0, 0, 0, 0], ![165, 1, 0, 0, 0], ![54, 0, 1, 0, 0], ![281, 0, 0, 1, 0], ![120, 0, 0, 0, 1]] where
  M :=![![![27, 41, 7, -16, -94], ![88, -13, 6, -8, -70], ![-600, -576, -97, 254, 1506], ![-206, 498, 66, -125, -658], ![66, -88, -8, 18, 83]]]
  hmulB := by decide  
  f := ![![![5147, 6763, 443, -2202, -13962]], ![![1923, 2510, 165, -818, -5184]], ![![874, 1206, 77, -390, -2482]], ![![2661, 3299, 223, -1083, -6836]], ![![1546, 2062, 134, -670, -4253]]]
  g := ![![![20, 41, 7, -16, -94], ![29, -13, 6, -8, -70], ![-352, -576, -97, 254, 1506], ![65, 498, 66, -125, -658], ![0, -88, -8, 18, 83]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI433N2 : Nat.card (O ⧸ I433N2) = 433 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI433N2)

lemma isPrimeI433N2 : Ideal.IsPrime I433N2 := prime_ideal_of_norm_prime hp433.out _ NI433N2
def MulI433N0 : IdealMulLeCertificate' Table 
  ![![-9341, -5657, -1268, 2967, 18430]] ![![-93, -94, -12, 36, 206]]
  ![![-936027, -598995, -130914, 307025, 1899148]] where
 M := ![![![-936027, -598995, -130914, 307025, 1899148]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI433N1 : IdealMulLeCertificate' Table 
  ![![-936027, -598995, -130914, 307025, 1899148]] ![![27, 41, 7, -16, -94]]
  ![![433, 0, 0, 0, 0]] where
 M := ![![![62660729, 30589718, 7622965, -17677225, -111633462]]]
 hmul := by decide  
 g := ![![![![144713, 70646, 17605, -40825, -257814]]]]
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

def I439N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5539, -3707, -202, 1801, 9986]] i)))

def SI439N0: IdealEqSpanCertificate' Table ![![-5539, -3707, -202, 1801, 9986]] 
 ![![439, 0, 0, 0, 0], ![0, 439, 0, 0, 0], ![0, 0, 439, 0, 0], ![369, 253, 358, 1, 0], ![243, 45, 143, 0, 1]] where
  M :=![![![-5539, -3707, -202, 1801, 9986], ![-26562, -17693, -966, 8616, 47736], ![-128112, -85746, -4691, 41628, 230856], ![-242340, -161067, -8799, 78511, 434868], ![19240, 12721, 695, -6218, -34413]]]
  hmulB := by decide  
  f := ![![![75, 110, 13, -37, -206]], ![![522, 301, 60, -150, -924]], ![![-372, -1050, -161, 384, 2208]], ![![57, -590, -86, 196, 1098]], ![![-25, -250, -39, 89, 509]]]
  g := ![![![-7054, -2070, -4722, 1801, 9986], ![-33726, -9899, -22578, 8616, 47736], ![-163068, -47850, -109157, 41628, 230856], ![-307257, -90190, -205699, 78511, 434868], ![24319, 7140, 16282, -6218, -34413]]]
  hle1 := by decide   
  hle2 := by decide  


def P439P0 : CertificateIrreducibleZModOfList' 439 3 2 8 [165, 327, 379, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [383, 92, 135], [116, 346, 304], [0, 1]]
 g := ![![[3, 89, 70], [102, 143, 111], [6, 220, 29], [149, 145], [105, 249, 69], [161, 348, 350], [282, 88], [1]], ![[214, 24, 20, 187], [32, 46, 103, 134], [366, 66, 365, 326], [298, 103], [10, 266, 49, 430], [1, 69, 157, 378], [167, 315], [293, 418, 8, 219]], ![[238, 410, 240, 127], [438, 321, 30, 242], [150, 206, 371, 260], [244, 242], [295, 382, 91, 258], [42, 270, 276, 286], [372, 291], [248, 165, 192, 220]]]
 h' := ![![[383, 92, 135], [291, 373, 387], [327, 129, 150], [349, 270, 111], [235, 228, 375], [214, 243, 76], [11, 298, 204], [274, 112, 60], [0, 1]], ![[116, 346, 304], [138, 245, 316], [238, 214, 392], [123, 254, 226], [256, 182, 295], [201, 21, 275], [314, 135, 186], [368, 111, 321], [383, 92, 135]], ![[0, 1], [15, 260, 175], [81, 96, 336], [44, 354, 102], [72, 29, 208], [326, 175, 88], [21, 6, 49], [158, 216, 58], [116, 346, 304]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [94, 60], []]
 b := ![[], [128, 40, 341], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI439N0 : CertifiedPrimeIdeal' SI439N0 439 where
  n := 3
  hpos := by decide
  P := [165, 327, 379, 1]
  hirr := P439P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8582524025, 9200558211, 518583501, -3457723802, -20881152761]
  a := ![1656, 1578, 142, -652, -3877]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![14484288674, 4154115158, 9622752960, -3457723802, -20881152761]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI439N0 : Ideal.IsPrime I439N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI439N0 B_one_repr
lemma NI439N0 : Nat.card (O ⧸ I439N0) = 84604519 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI439N0

def I439N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![33, 54, 3, -17, -110]] i)))

def SI439N1: IdealEqSpanCertificate' Table ![![33, 54, 3, -17, -110]] 
 ![![439, 0, 0, 0, 0], ![23, 1, 0, 0, 0], ![349, 0, 1, 0, 0], ![202, 0, 0, 1, 0], ![117, 0, 0, 0, 1]] where
  M :=![![![33, 54, 3, -17, -110], ![-190, -293, -18, 94, 604], ![932, 1494, 91, -476, -3056], ![-2790, -4509, -267, 1429, 9180], ![470, 765, 45, -242, -1555]]]
  hmulB := by decide  
  f := ![![![-1909, -1233, -102, 545, 3074]], ![![-115, -74, -6, 33, 186]], ![![-1575, -1017, -83, 451, 2542]], ![![-982, -639, -51, 285, 1604]], ![![-503, -324, -27, 143, 807]]]
  g := ![![![32, 54, 3, -17, -110], ![-175, -293, -18, 94, 604], ![885, 1494, 91, -476, -3056], ![-2662, -4509, -267, 1429, 9180], ![451, 765, 45, -242, -1555]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI439N1 : Nat.card (O ⧸ I439N1) = 439 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI439N1)

lemma isPrimeI439N1 : Ideal.IsPrime I439N1 := prime_ideal_of_norm_prime hp439.out _ NI439N1

def I439N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![77, 22, 2, -10, -60]] i)))

def SI439N2: IdealEqSpanCertificate' Table ![![77, 22, 2, -10, -60]] 
 ![![439, 0, 0, 0, 0], ![140, 1, 0, 0, 0], ![155, 0, 1, 0, 0], ![267, 0, 0, 1, 0], ![179, 0, 0, 0, 1]] where
  M :=![![![77, 22, 2, -10, -60], ![20, 17, -6, 4, 40], ![440, 492, 71, -188, -1088], ![528, -30, 24, -55, -420], ![-36, 34, -4, 2, 35]]]
  hmulB := by decide  
  f := ![![![-1909, -3838, -230, 1126, 7476]], ![![-568, -1167, -70, 340, 2264]], ![![-793, -1586, -95, 466, 3092]], ![![-585, -1488, -90, 407, 2784]], ![![-869, -1704, -102, 504, 3335]]]
  g := ![![![23, 22, 2, -10, -60], ![-22, 17, -6, 4, 40], ![377, 492, 71, -188, -1088], ![207, -30, 24, -55, -420], ![-25, 34, -4, 2, 35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI439N2 : Nat.card (O ⧸ I439N2) = 439 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI439N2)

lemma isPrimeI439N2 : Ideal.IsPrime I439N2 := prime_ideal_of_norm_prime hp439.out _ NI439N2
def MulI439N0 : IdealMulLeCertificate' Table 
  ![![-5539, -3707, -202, 1801, 9986]] ![![33, 54, 3, -17, -110]]
  ![![1909, 3838, 230, -1126, -7476]] where
 M := ![![![1909, 3838, 230, -1126, -7476]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI439N1 : IdealMulLeCertificate' Table 
  ![![1909, 3838, 230, -1126, -7476]] ![![77, 22, 2, -10, -60]]
  ![![439, 0, 0, 0, 0]] where
 M := ![![![-439, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC439 : ContainsPrimesAboveP 439 ![I439N0, I439N1, I439N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI439N0
    exact isPrimeI439N1
    exact isPrimeI439N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 439 (by decide) (𝕀 ⊙ MulI439N0 ⊙ MulI439N1)
instance hp443 : Fact (Nat.Prime 443) := {out := by norm_num}

def I443N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-311, -307, -47, 130, 786]] i)))

def SI443N0: IdealEqSpanCertificate' Table ![![-311, -307, -47, 130, 786]] 
 ![![443, 0, 0, 0, 0], ![0, 443, 0, 0, 0], ![0, 0, 443, 0, 0], ![55, 128, 88, 1, 0], ![398, 41, 75, 0, 1]] where
  M :=![![![-311, -307, -47, 130, 786], ![-92, 637, 54, -160, -922], ![1384, 12, 325, -310, -1906], ![-1026, -888, -528, 733, 3114], ![-42, 194, 94, -110, -419]]]
  hmulB := by decide  
  f := ![![![-37141, -20851, -2321, 8080, 46818]], ![![-62696, -35197, -3918, 13640, 79034]], ![![-105848, -59424, -6613, 23030, 133442]], ![![-43835, -24609, -2739, 9537, 55260]], ![![-57180, -32101, -3573, 12440, 72081]]]
  g := ![![![-723, -111, -159, 130, 786], ![848, 133, 188, -160, -922], ![1754, 266, 385, -310, -1906], ![-2891, -502, -674, 733, 3114], ![390, 71, 93, -110, -419]]]
  hle1 := by decide   
  hle2 := by decide  


def P443P0 : CertificateIrreducibleZModOfList' 443 3 2 8 [103, 180, 328, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [204, 88, 370], [354, 354, 73], [0, 1]]
 g := ![![[355, 281, 268], [206, 73, 77], [314, 315], [45, 52, 417], [90, 201, 432], [128, 276, 155], [298, 378], [1]], ![[131, 224, 258, 321], [142, 388, 363, 347], [178, 373], [302, 386, 72, 153], [248, 117, 354, 378], [166, 153, 79, 106], [31, 318], [89, 190, 174, 380]], ![[320, 33, 220, 304], [170, 27, 380, 29], [357, 265], [208, 163, 49, 323], [408, 3, 385, 427], [396, 407, 77, 377], [424, 359], [200, 32, 230, 63]]]
 h' := ![![[204, 88, 370], [46, 126, 197], [380, 413, 43], [238, 37, 275], [33, 27, 204], [106, 270, 280], [293, 324, 191], [340, 263, 115], [0, 1]], ![[354, 354, 73], [429, 209, 292], [395, 117, 135], [218, 170, 290], [175, 301, 251], [168, 256, 113], [105, 404, 105], [148, 74, 247], [204, 88, 370]], ![[0, 1], [422, 108, 397], [347, 356, 265], [160, 236, 321], [23, 115, 431], [251, 360, 50], [423, 158, 147], [65, 106, 81], [354, 354, 73]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24, 380], []]
 b := ![[], [407, 254, 430], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI443N0 : CertifiedPrimeIdeal' SI443N0 443 where
  n := 3
  hpos := by decide
  P := [103, 180, 328, 1]
  hirr := P443P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-54486569, -89592960, -4864896, 28004288, 180714288]
  a := ![-170, -162, -16, 62, 398]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-165957131, -25019024, -36168880, 28004288, 180714288]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI443N0 : Ideal.IsPrime I443N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI443N0 B_one_repr
lemma NI443N0 : Nat.card (O ⧸ I443N0) = 86938307 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI443N0

def I443N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37141, 20851, 2321, -8080, -46818]] i)))

def SI443N1: IdealEqSpanCertificate' Table ![![37141, 20851, 2321, -8080, -46818]] 
 ![![443, 0, 0, 0, 0], ![0, 443, 0, 0, 0], ![230, 268, 1, 0, 0], ![75, 395, 0, 1, 0], ![284, 147, 0, 0, 1]] where
  M :=![![![37141, 20851, 2321, -8080, -46818], ![62696, 35197, 3918, -13640, -79034], ![105848, 59424, 6613, -23030, -133442], ![36438, 20454, 2274, -7931, -45942], ![39486, 22168, 2468, -8590, -49775]]]
  hmulB := by decide  
  f := ![![![311, 307, 47, -130, -786]], ![![92, -637, -54, 160, 922]], ![![214, -226, -9, 30, 154]], ![![137, -514, -39, 119, 682]], ![![230, -15, 12, -30, -197]]]
  g := ![![![30261, 21383, 2321, -8080, -46818], ![51084, 36097, 3918, -13640, -79034], ![86252, 60948, 6613, -23030, -133442], ![29697, 20987, 2274, -7931, -45942], ![32172, 22733, 2468, -8590, -49775]]]
  hle1 := by decide   
  hle2 := by decide  


def P443P1 : CertificateIrreducibleZModOfList' 443 2 2 8 [118, 69, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [374, 442], [0, 1]]
 g := ![![[147, 126], [130, 165], [52], [439, 209], [302, 81], [55, 41], [183], [374, 1]], ![[313, 317], [263, 278], [52], [194, 234], [29, 362], [327, 402], [183], [305, 442]]]
 h' := ![![[374, 442], [165, 353], [21, 348], [29, 297], [247, 274], [155, 9], [428, 22], [168, 213], [0, 1]], ![[0, 1], [173, 90], [374, 95], [357, 146], [390, 169], [420, 434], [239, 421], [90, 230], [374, 442]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [88]]
 b := ![[], [189, 44]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI443N1 : CertifiedPrimeIdeal' SI443N1 443 where
  n := 2
  hpos := by decide
  P := [118, 69, 1]
  hirr := P443P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11386916, -10458938, -677434, 4258038, 25216774]
  a := ![-2743, -2614, -230, 1086, 6422]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-16560934, -11778098, -677434, 4258038, 25216774]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI443N1 : Ideal.IsPrime I443N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI443N1 B_one_repr
lemma NI443N1 : Nat.card (O ⧸ I443N1) = 196249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI443N1
def MulI443N0 : IdealMulLeCertificate' Table 
  ![![-311, -307, -47, 130, 786]] ![![37141, 20851, 2321, -8080, -46818]]
  ![![443, 0, 0, 0, 0]] where
 M := ![![![-443, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC443 : ContainsPrimesAboveP 443 ![I443N0, I443N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI443N0
    exact isPrimeI443N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 443 (by decide) (𝕀 ⊙ MulI443N0)
instance hp449 : Fact (Nat.Prime 449) := {out := by norm_num}

def I449N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![66777, 37491, 4172, -14527, -84178]] i)))

def SI449N0: IdealEqSpanCertificate' Table ![![66777, 37491, 4172, -14527, -84178]] 
 ![![449, 0, 0, 0, 0], ![0, 449, 0, 0, 0], ![0, 0, 449, 0, 0], ![229, 407, 83, 1, 0], ![15, 195, 245, 0, 1]] where
  M :=![![![66777, 37491, 4172, -14527, -84178], ![112606, 63167, 7034, -24480, -141820], ![190640, 107406, 11941, -41592, -241100], ![64600, 35169, 3993, -13749, -79408], ![71116, 40113, 4451, -15522, -89981]]]
  hmulB := by decide  
  f := ![![![-2559, -1716, -95, 833, 4618]], ![![-12306, -8201, -452, 3990, 22128]], ![![-58716, -39102, -2119, 19028, 105444]], ![![-23563, -15704, -859, 7640, 42354]], ![![-37449, -24942, -1355, 12137, 67265]]]
  g := ![![![10370, 49810, 48627, -14527, -84178], ![17474, 83923, 81926, -24480, -141820], ![29692, 142650, 139273, -41592, -241100], ![9809, 47028, 45880, -13749, -79408], ![11081, 53238, 51978, -15522, -89981]]]
  hle1 := by decide   
  hle2 := by decide  


def P449P0 : CertificateIrreducibleZModOfList' 449 3 2 8 [284, 365, 79, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [433, 213, 111], [386, 235, 338], [0, 1]]
 g := ![![[38, 74, 70], [397, 191], [436, 347], [146, 36], [15, 441], [251, 287], [407, 161, 404], [1]], ![[4, 197, 304, 114], [226, 53], [78, 440], [384, 224], [422, 1], [115, 98], [278, 9, 329, 271], [345, 251, 374, 426]], ![[370, 68, 57, 351], [174, 388], [161, 315], [236, 197], [448, 35], [193, 207], [120, 118, 175, 371], [309, 340, 379, 23]]]
 h' := ![![[433, 213, 111], [347, 8, 238], [262, 153, 33], [179, 428, 267], [421, 125, 443], [416, 4, 428], [254, 423, 319], [165, 84, 370], [0, 1]], ![[386, 235, 338], [379, 280, 244], [51, 422, 43], [287, 340, 248], [96, 268, 342], [153, 423, 448], [443, 209, 239], [296, 50, 188], [433, 213, 111]], ![[0, 1], [221, 161, 416], [78, 323, 373], [447, 130, 383], [11, 56, 113], [25, 22, 22], [48, 266, 340], [294, 315, 340], [386, 235, 338]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [361, 234], []]
 b := ![[], [262, 5, 277], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI449N0 : CertifiedPrimeIdeal' SI449N0 449 where
  n := 3
  hpos := by decide
  P := [284, 365, 79, 1]
  hirr := P449P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7500275, -10182804, -598381, 3443900, 21649430]
  a := ![-129, -126, -11, 50, 302]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2496425, -12546746, -12451119, 3443900, 21649430]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI449N0 : Ideal.IsPrime I449N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI449N0 B_one_repr
lemma NI449N0 : Nat.card (O ⧸ I449N0) = 90518849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI449N0

def I449N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2559, -1716, -95, 833, 4618]] i)))

def SI449N1: IdealEqSpanCertificate' Table ![![-2559, -1716, -95, 833, 4618]] 
 ![![449, 0, 0, 0, 0], ![0, 449, 0, 0, 0], ![354, 284, 1, 0, 0], ![292, 117, 0, 1, 0], ![156, 127, 0, 0, 1]] where
  M :=![![![-2559, -1716, -95, 833, 4618], ![-12306, -8201, -452, 3990, 22128], ![-58716, -39102, -2119, 19028, 105444], ![-111806, -74859, -4095, 36349, 201476], ![8874, 5967, 325, -2892, -16025]]]
  hmulB := by decide  
  f := ![![![66777, 37491, 4172, -14527, -84178]], ![![112606, 63167, 7034, -24480, -141820]], ![![124298, 69752, 7765, -27030, -156608]], ![![72914, 40920, 4555, -15857, -91876]], ![![55210, 30982, 3449, -12006, -69561]]]
  g := ![![![-2077, -1467, -95, 833, 4618], ![-9954, -7031, -452, 3990, 22128], ![-47470, -33530, -2119, 19028, 105444], ![-90660, -64036, -4095, 36349, 201476], ![7212, 5094, 325, -2892, -16025]]]
  hle1 := by decide   
  hle2 := by decide  


def P449P1 : CertificateIrreducibleZModOfList' 449 2 2 8 [200, 237, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [212, 448], [0, 1]]
 g := ![![[421, 339], [295], [439], [111], [393], [20], [135, 90], [212, 1]], ![[0, 110], [295], [439], [111], [393], [20], [357, 359], [424, 448]]]
 h' := ![![[212, 448], [131, 226], [326, 173], [349, 341], [131, 88], [49, 232], [389, 213], [255, 293], [0, 1]], ![[0, 1], [0, 223], [184, 276], [352, 108], [378, 361], [292, 217], [196, 236], [409, 156], [212, 448]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [430]]
 b := ![[], [109, 215]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI449N1 : CertifiedPrimeIdeal' SI449N1 449 where
  n := 2
  hpos := by decide
  P := [200, 237, 1]
  hirr := P449P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4817334, -4671651, -301772, 1848671, 11066048]
  a := ![-1738, -1656, -145, 684, 4069]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4819834, -3431294, -301772, 1848671, 11066048]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI449N1 : Ideal.IsPrime I449N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI449N1 B_one_repr
lemma NI449N1 : Nat.card (O ⧸ I449N1) = 201601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI449N1
def MulI449N0 : IdealMulLeCertificate' Table 
  ![![66777, 37491, 4172, -14527, -84178]] ![![-2559, -1716, -95, 833, 4618]]
  ![![449, 0, 0, 0, 0]] where
 M := ![![![449, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC449 : ContainsPrimesAboveP 449 ![I449N0, I449N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI449N0
    exact isPrimeI449N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 449 (by decide) (𝕀 ⊙ MulI449N0)
instance hp457 : Fact (Nat.Prime 457) := {out := by norm_num}

def I457N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![401, -80, 14, -6, 66]] i)))

def SI457N0: IdealEqSpanCertificate' Table ![![401, -80, 14, -6, 66]] 
 ![![457, 0, 0, 0, 0], ![0, 457, 0, 0, 0], ![292, 90, 1, 0, 0], ![424, 164, 0, 1, 0], ![45, 50, 0, 0, 1]] where
  M :=![![![401, -80, 14, -6, 66], ![2868, 3221, 222, -1094, -6810], ![-4700, -10584, -577, 3150, 20858], ![26612, 39804, 2370, -12921, -82322], ![-3524, -6188, -346, 1958, 12631]]]
  hmulB := by decide  
  f := ![![![5025, -256, 286, -598, -4534]], ![![-25292, -25051, -4602, 10978, 65774]], ![![-1824, -5014, -717, 1762, 9974]], ![![-4020, -9000, -1334, 3263, 18638]], ![![-2359, -2826, -488, 1172, 6933]]]
  g := ![![![-9, -8, 14, -6, 66], ![1550, 1101, 222, -1094, -6810], ![-4618, -3322, -577, 3150, 20858], ![18638, 13264, 2370, -12921, -82322], ![-2847, -2030, -346, 1958, 12631]]]
  hle1 := by decide   
  hle2 := by decide  


def P457P0 : CertificateIrreducibleZModOfList' 457 2 2 8 [53, 123, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [334, 456], [0, 1]]
 g := ![![[261, 147], [254], [349], [308, 440], [1], [421], [285, 25], [334, 1]], ![[3, 310], [254], [349], [114, 17], [1], [421], [409, 432], [211, 456]]]
 h' := ![![[334, 456], [127, 101], [172, 305], [128, 226], [246, 393], [199, 456], [433, 197], [121, 452], [0, 1]], ![[0, 1], [43, 356], [131, 152], [207, 231], [349, 64], [322, 1], [423, 260], [279, 5], [334, 456]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [379]]
 b := ![[], [115, 418]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI457N0 : CertifiedPrimeIdeal' SI457N0 457 where
  n := 2
  hpos := by decide
  P := [53, 123, 1]
  hirr := P457P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1702501, -1624378, -107612, 648192, 3874672]
  a := ![-1061, -1010, -91, 418, 2484]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-917885, -638898, -107612, 648192, 3874672]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI457N0 : Ideal.IsPrime I457N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI457N0 B_one_repr
lemma NI457N0 : Nat.card (O ⧸ I457N0) = 208849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI457N0

def I457N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-37587, -21102, -2349, 8177, 47380]] i)))

def SI457N1: IdealEqSpanCertificate' Table ![![-37587, -21102, -2349, 8177, 47380]] 
 ![![457, 0, 0, 0, 0], ![0, 457, 0, 0, 0], ![447, 36, 1, 0, 0], ![185, 243, 0, 1, 0], ![55, 62, 0, 0, 1]] where
  M :=![![![-37587, -21102, -2349, 8177, 47380], ![-63450, -35621, -3966, 13804, 79986], ![-107072, -60090, -6689, 23286, 134930], ![-36754, -20637, -2295, 7991, 46294], ![-39978, -22443, -2499, 8698, 50401]]]
  hmulB := by decide  
  f := ![![![-47, -147, -18, 41, 288]], ![![1094, 1375, 84, -498, -2978]], ![![43, -39, -11, 1, 50]], ![![591, 705, 39, -260, -1540]], ![![139, 164, 9, -61, -359]]]
  g := ![![![-6797, -10637, -2349, 8177, 47380], ![-11474, -17957, -3966, 13804, 79986], ![-19357, -30292, -6689, 23286, 134930], ![-6642, -10394, -2295, 7991, 46294], ![-7230, -11315, -2499, 8698, 50401]]]
  hle1 := by decide   
  hle2 := by decide  


def P457P1 : CertificateIrreducibleZModOfList' 457 2 2 8 [423, 82, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [375, 456], [0, 1]]
 g := ![![[132, 336], [262], [359], [45, 252], [441], [323], [119, 269], [375, 1]], ![[0, 121], [262], [359], [403, 205], [441], [323], [454, 188], [293, 456]]]
 h' := ![![[375, 456], [394, 172], [13, 165], [159, 198], [289, 326], [390, 21], [390, 133], [411, 360], [0, 1]], ![[0, 1], [0, 285], [193, 292], [375, 259], [63, 131], [39, 436], [452, 324], [139, 97], [375, 456]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [182]]
 b := ![[], [75, 91]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI457N1 : CertifiedPrimeIdeal' SI457N1 457 where
  n := 2
  hpos := by decide
  P := [423, 82, 1]
  hirr := P457P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1856924, -1707840, -112788, 695749, 4122487]
  a := ![-1099, -1047, -93, 435, 2573]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-671534, -924089, -112788, 695749, 4122487]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI457N1 : Ideal.IsPrime I457N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI457N1 B_one_repr
lemma NI457N1 : Nat.card (O ⧸ I457N1) = 208849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI457N1

def I457N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-12981, -8664, -474, 4212, 23348]] i)))

def SI457N2: IdealEqSpanCertificate' Table ![![-12981, -8664, -474, 4212, 23348]] 
 ![![457, 0, 0, 0, 0], ![331, 1, 0, 0, 0], ![119, 0, 1, 0, 0], ![354, 0, 0, 1, 0], ![129, 0, 0, 0, 1]] where
  M :=![![![-12981, -8664, -474, 4212, 23348], ![-62296, -41581, -2274, 20216, 112060], ![-299040, -199608, -10915, 97048, 537948], ![-568288, -379332, -20742, 184431, 1022320], ![45212, 30180, 1650, -14674, -81339]]]
  hmulB := by decide  
  f := ![![![971, -408, 102, -76, -564]], ![![697, -301, 72, -52, -392]], ![![197, -144, 23, -4, -40]], ![![934, -108, 102, -137, -928]], ![![239, -156, 24, -6, -63]]]
  g := ![![![-3483, -8664, -474, 4212, 23348], ![-16719, -41581, -2274, 20216, 112060], ![-80263, -199608, -10915, 97048, 537948], ![-152536, -379332, -20742, 184431, 1022320], ![12137, 30180, 1650, -14674, -81339]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI457N2 : Nat.card (O ⧸ I457N2) = 457 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI457N2)

lemma isPrimeI457N2 : Ideal.IsPrime I457N2 := prime_ideal_of_norm_prime hp457.out _ NI457N2
def MulI457N0 : IdealMulLeCertificate' Table 
  ![![401, -80, 14, -6, 66]] ![![-37587, -21102, -2349, 8177, 47380]]
  ![![-13913419, -7810898, -869479, 3026783, 17538222]] where
 M := ![![![-13913419, -7810898, -869479, 3026783, 17538222]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI457N1 : IdealMulLeCertificate' Table 
  ![![-13913419, -7810898, -869479, 3026783, 17538222]] ![![-12981, -8664, -474, 4212, 23348]]
  ![![457, 0, 0, 0, 0]] where
 M := ![![![60429567, 33667190, 3839257, -12886943, -74868482]]]
 hmul := by decide  
 g := ![![![![132231, 73670, 8401, -28199, -163826]]]]
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

def I461N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 85, 23, -52, -330]] i)))

def SI461N0: IdealEqSpanCertificate' Table ![![197, 85, 23, -52, -330]] 
 ![![461, 0, 0, 0, 0], ![0, 461, 0, 0, 0], ![0, 0, 461, 0, 0], ![221, 315, 87, 1, 0], ![47, 460, 457, 0, 1]] where
  M :=![![![197, 85, 23, -52, -330], ![-400, -619, -102, 244, 1414], ![-1888, -336, -139, 346, 2374], ![4770, 4434, 798, -1951, -11862], ![-942, -992, -172, 422, 2537]]]
  hmulB := by decide  
  f := ![![![169, 91, 11, -34, -198]], ![![236, 133, 18, -44, -266]], ![![32, -84, 13, 58, 310]], ![![247, 118, 20, -35, -216]], ![![285, 59, 32, 10, 21]]]
  g := ![![![59, 365, 337, -52, -330], ![-262, -1579, -1448, 244, 1414], ![-412, -2606, -2419, 346, 2374], ![2155, 13179, 12129, -1951, -11862], ![-463, -2822, -2595, 422, 2537]]]
  hle1 := by decide   
  hle2 := by decide  


def P461P0 : CertificateIrreducibleZModOfList' 461 3 2 8 [88, 108, 163, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [189, 157, 224], [109, 303, 237], [0, 1]]
 g := ![![[45, 160, 39], [16, 400], [278, 187, 126], [203, 138, 289], [118, 16], [136, 399], [121, 59, 292], [1]], ![[77, 325, 66, 23], [410, 97], [76, 180, 318, 455], [243, 153, 353, 23], [214, 166], [317, 92], [141, 402, 374, 336], [378, 267, 66, 244]], ![[304, 371, 152, 97], [441, 166], [270, 0, 109, 104], [63, 412, 171, 87], [149, 457], [60, 64], [259, 24, 51, 281], [382, 113, 153, 217]]]
 h' := ![![[189, 157, 224], [14, 170, 430], [430, 398, 441], [115, 357, 204], [174, 454, 17], [199, 456, 4], [416, 87, 409], [373, 353, 298], [0, 1]], ![[109, 303, 237], [34, 296, 105], [62, 235, 112], [47, 339, 253], [176, 21, 356], [81, 48, 92], [115, 64, 44], [313, 155, 179], [189, 157, 224]], ![[0, 1], [354, 456, 387], [327, 289, 369], [369, 226, 4], [300, 447, 88], [53, 418, 365], [102, 310, 8], [117, 414, 445], [109, 303, 237]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [261, 290], []]
 b := ![[], [459, 298, 151], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI461N0 : CertifiedPrimeIdeal' SI461N0 461 where
  n := 3
  hpos := by decide
  P := [88, 108, 163, 1]
  hirr := P461P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![16747261784, 18536233939, 1059166095, -6873222644, -41682160412]
  a := ![1838, 1754, 146, -722, -4303]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![7580891552, 46328405979, 42619906387, -6873222644, -41682160412]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI461N0 : Ideal.IsPrime I461N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI461N0 B_one_repr
lemma NI461N0 : Nat.card (O ⧸ I461N0) = 97972181 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI461N0

def I461N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-169, -91, -11, 34, 198]] i)))

def SI461N1: IdealEqSpanCertificate' Table ![![-169, -91, -11, 34, 198]] 
 ![![461, 0, 0, 0, 0], ![0, 461, 0, 0, 0], ![241, 288, 1, 0, 0], ![442, 225, 0, 1, 0], ![230, 240, 0, 0, 1]] where
  M :=![![![-169, -91, -11, 34, 198], ![-236, -133, -18, 44, 266], ![-32, 84, -13, -58, -310], ![606, 300, 12, -193, -1002], ![-258, -130, -14, 58, 323]]]
  hmulB := by decide  
  f := ![![![-197, -85, -23, 52, 330]], ![![400, 619, 102, -244, -1414]], ![![151, 343, 52, -126, -716]], ![![-4, 211, 26, -65, -348]], ![![112, 282, 42, -102, -577]]]
  g := ![![![-126, -113, -11, 34, 198], ![-166, -149, -18, 44, 266], ![217, 198, -13, -58, -310], ![680, 609, 12, -193, -1002], ![-210, -188, -14, 58, 323]]]
  hle1 := by decide   
  hle2 := by decide  


def P461P1 : CertificateIrreducibleZModOfList' 461 2 2 8 [356, 149, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [312, 460], [0, 1]]
 g := ![![[82, 180], [164], [202, 289], [58, 236], [198], [132], [367, 336], [312, 1]], ![[0, 281], [164], [14, 172], [391, 225], [198], [132], [91, 125], [163, 460]]]
 h' := ![![[312, 460], [179, 258], [4, 436], [97, 444], [21, 202], [254, 171], [272, 339], [29, 178], [0, 1]], ![[0, 1], [0, 203], [41, 25], [325, 17], [349, 259], [130, 290], [10, 122], [245, 283], [312, 460]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [288]]
 b := ![[], [125, 144]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI461N1 : CertifiedPrimeIdeal' SI461N1 461 where
  n := 2
  hpos := by decide
  P := [356, 149, 1]
  hirr := P461P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1789528, -1726869, -104280, 681485, 4072902]
  a := ![1149, 1098, 95, -453, -2690]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2634798, -2391594, -104280, 681485, 4072902]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI461N1 : Ideal.IsPrime I461N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI461N1 B_one_repr
lemma NI461N1 : Nat.card (O ⧸ I461N1) = 212521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI461N1
def MulI461N0 : IdealMulLeCertificate' Table 
  ![![197, 85, 23, -52, -330]] ![![-169, -91, -11, 34, 198]]
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

def I463N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-811, -905, -160, 383, 2276]] i)))

def SI463N0: IdealEqSpanCertificate' Table ![![-811, -905, -160, 383, 2276]] 
 ![![463, 0, 0, 0, 0], ![0, 463, 0, 0, 0], ![242, 230, 1, 0, 0], ![292, 410, 0, 1, 0], ![281, 423, 0, 0, 1]] where
  M :=![![![-811, -905, -160, 383, 2276], ![-1382, 871, 18, -78, -58], ![11636, 9630, 1885, -4474, -27158], ![-5740, -16815, -2367, 5849, 33046], ![308, 3049, 383, -962, -5269]]]
  hmulB := by decide  
  f := ![![![11603, 7640, 451, -3655, -20320]], ![![52390, 34753, 1956, -16808, -93250]], ![![32622, 21612, 1227, -10432, -57898]], ![![54710, 36259, 2053, -17513, -97186]], ![![54829, 36336, 2058, -17549, -97387]]]
  g := ![![![-1541, -2341, -160, 383, 2276], ![72, 115, 18, -78, -58], ![18344, 27858, 1885, -4474, -27158], ![-22520, -34231, -2367, 5849, 33046], ![3605, 5482, 383, -962, -5269]]]
  hle1 := by decide   
  hle2 := by decide  


def P463P0 : CertificateIrreducibleZModOfList' 463 2 2 8 [22, 129, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [334, 462], [0, 1]]
 g := ![![[69, 293], [29, 256], [176, 68], [87, 69], [140], [162], [157, 86], [334, 1]], ![[238, 170], [341, 207], [201, 395], [446, 394], [140], [162], [175, 377], [205, 462]]]
 h' := ![![[334, 462], [288, 331], [295, 16], [401, 122], [329, 388], [135, 401], [250, 438], [60, 414], [0, 1]], ![[0, 1], [185, 132], [83, 447], [405, 341], [281, 75], [262, 62], [234, 25], [362, 49], [334, 462]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [149]]
 b := ![[], [291, 306]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI463N0 : CertifiedPrimeIdeal' SI463N0 463 where
  n := 2
  hpos := by decide
  P := [22, 129, 1]
  hirr := P463P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5183996, -4749723, -311661, 1938864, 11473920]
  a := ![-1823, -1737, -153, 722, 4268]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-8034734, -12055011, -311661, 1938864, 11473920]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI463N0 : Ideal.IsPrime I463N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI463N0 B_one_repr
lemma NI463N0 : Nat.card (O ⧸ I463N0) = 214369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI463N0

def I463N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-49, -30, -3, 11, 62]] i)))

def SI463N1: IdealEqSpanCertificate' Table ![![-49, -30, -3, 11, 62]] 
 ![![463, 0, 0, 0, 0], ![0, 463, 0, 0, 0], ![198, 188, 1, 0, 0], ![272, 390, 0, 1, 0], ![431, 268, 0, 0, 1]] where
  M :=![![![-49, -30, -3, 11, 62], ![-134, -95, -12, 38, 224], ![-188, -18, -5, 20, 116], ![18, -81, 15, 7, 36], ![-86, -39, -9, 20, 117]]]
  hmulB := by decide  
  f := ![![![-87, -51, -6, 25, 142]], ![![-274, -161, -6, 76, 436]], ![![-150, -88, -5, 42, 240]], ![![-288, -171, -9, 81, 464]], ![![-239, -140, -9, 67, 383]]]
  g := ![![![-63, -44, -3, 11, 62], ![-226, -157, -12, 38, 224], ![-118, -82, -5, 20, 116], ![-44, -33, 15, 7, 36], ![-117, -81, -9, 20, 117]]]
  hle1 := by decide   
  hle2 := by decide  


def P463P1 : CertificateIrreducibleZModOfList' 463 2 2 8 [32, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [444, 462], [0, 1]]
 g := ![![[44, 246], [41, 124], [34, 122], [402, 435], [111], [417], [99, 362], [444, 1]], ![[0, 217], [0, 339], [31, 341], [8, 28], [111], [417], [166, 101], [425, 462]]]
 h' := ![![[444, 462], [77, 199], [301, 357], [100, 234], [53, 322], [319, 379], [73, 152], [145, 329], [0, 1]], ![[0, 1], [0, 264], [0, 106], [284, 229], [417, 141], [63, 84], [426, 311], [376, 134], [444, 462]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [306]]
 b := ![[], [296, 153]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI463N1 : CertifiedPrimeIdeal' SI463N1 463 where
  n := 2
  hpos := by decide
  P := [32, 19, 1]
  hirr := P463P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7622586, -7541773, -473606, 2941967, 17701706]
  a := ![2342, 2234, 199, -920, -5483]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-18020516, -12548441, -473606, 2941967, 17701706]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI463N1 : Ideal.IsPrime I463N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI463N1 B_one_repr
lemma NI463N1 : Nat.card (O ⧸ I463N1) = 214369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI463N1

def I463N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2929, 1958, 106, -954, -5286]] i)))

def SI463N2: IdealEqSpanCertificate' Table ![![2929, 1958, 106, -954, -5286]] 
 ![![463, 0, 0, 0, 0], ![45, 1, 0, 0, 0], ![290, 0, 1, 0, 0], ![275, 0, 0, 1, 0], ![400, 0, 0, 0, 1]] where
  M :=![![![2929, 1958, 106, -954, -5286], ![14172, 9469, 516, -4606, -25530], ![68180, 45504, 2485, -22134, -122678], ![129808, 86700, 4740, -42141, -233614], ![-10372, -6928, -380, 3364, 18653]]]
  hmulB := by decide  
  f := ![![![2247, -6602, -646, 1690, 8518]], ![![113, -713, -78, 200, 1048]], ![![1494, -3868, -367, 966, 4814]], ![![1859, -3814, -338, 901, 4368]], ![![1812, -5752, -572, 1492, 7565]]]
  g := ![![![4883, 1958, 106, -954, -5286], ![23579, 9469, 516, -4606, -25530], ![113300, 45504, 2485, -22134, -122678], ![215741, 86700, 4740, -42141, -233614], ![-17224, -6928, -380, 3364, 18653]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI463N2 : Nat.card (O ⧸ I463N2) = 463 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI463N2)

lemma isPrimeI463N2 : Ideal.IsPrime I463N2 := prime_ideal_of_norm_prime hp463.out _ NI463N2
def MulI463N0 : IdealMulLeCertificate' Table 
  ![![-811, -905, -160, 383, 2276]] ![![-49, -30, -3, 11, 62]]
  ![![2247, -6602, -646, 1690, 8518]] where
 M := ![![![2247, -6602, -646, 1690, 8518]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI463N1 : IdealMulLeCertificate' Table 
  ![![2247, -6602, -646, 1690, 8518]] ![![2929, 1958, 106, -954, -5286]]
  ![![463, 0, 0, 0, 0]] where
 M := ![![![463, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC463 : ContainsPrimesAboveP 463 ![I463N0, I463N1, I463N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI463N0
    exact isPrimeI463N1
    exact isPrimeI463N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 463 (by decide) (𝕀 ⊙ MulI463N0 ⊙ MulI463N1)


lemma PB953I9_primes (p : ℕ) :
  p ∈ Set.range ![421, 431, 433, 439, 443, 449, 457, 461, 463] ↔ Nat.Prime p ∧ 419 < p ∧ p ≤ 463 := by
  rw [← List.mem_ofFn']
  convert primes_range 419 463 (by omega)

def PB953I9 : PrimesBelowBoundCertificateInterval O 419 463 953 where
  m := 9
  g := ![1, 4, 3, 3, 2, 2, 3, 2, 3]
  P := ![421, 431, 433, 439, 443, 449, 457, 461, 463]
  hP := PB953I9_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I421N0]
    · exact ![I431N0, I431N1, I431N2, I431N3]
    · exact ![I433N0, I433N1, I433N2]
    · exact ![I439N0, I439N1, I439N2]
    · exact ![I443N0, I443N1]
    · exact ![I449N0, I449N1]
    · exact ![I457N0, I457N1, I457N2]
    · exact ![I461N0, I461N1]
    · exact ![I463N0, I463N1, I463N2]
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
    · exact ![13225450646101]
    · exact ![185761, 431, 431, 431]
    · exact ![187489, 187489, 433]
    · exact ![84604519, 439, 439]
    · exact ![86938307, 196249]
    · exact ![90518849, 201601]
    · exact ![208849, 208849, 457]
    · exact ![97972181, 212521]
    · exact ![214369, 214369, 463]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI421N0
    · dsimp ; intro j
      fin_cases j
      exact NI431N0
      exact NI431N1
      exact NI431N2
      exact NI431N3
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
    · dsimp ; intro j
      fin_cases j
      exact NI443N0
      exact NI443N1
    · dsimp ; intro j
      fin_cases j
      exact NI449N0
      exact NI449N1
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
      exact NI463N2
  β := ![I431N1, I431N2, I431N3, I433N2, I439N1, I439N2, I457N2, I463N2]
  Il := ![[], [I431N1, I431N2, I431N3], [I433N2], [I439N1, I439N2], [], [], [I457N2], [], [I463N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
