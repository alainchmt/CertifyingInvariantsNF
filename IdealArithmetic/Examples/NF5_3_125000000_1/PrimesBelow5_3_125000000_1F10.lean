
import IdealArithmetic.Examples.NF5_3_125000000_1.RI5_3_125000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp467 : Fact (Nat.Prime 467) := {out := by norm_num}

def I467N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![467, 0, 0, 0, 0]] i)))

def SI467N0: IdealEqSpanCertificate' Table ![![467, 0, 0, 0, 0]] 
 ![![467, 0, 0, 0, 0], ![0, 467, 0, 0, 0], ![0, 0, 467, 0, 0], ![0, 0, 0, 467, 0], ![0, 0, 0, 0, 467]] where
  M :=![![![467, 0, 0, 0, 0], ![0, 467, 0, 0, 0], ![0, 0, 467, 0, 0], ![0, 0, 0, 467, 0], ![0, 0, 0, 0, 467]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P467P0 : CertificateIrreducibleZModOfList' 467 5 2 8 [6, 437, 452, 459, 250, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [138, 223, 424, 301, 386], [419, 342, 296, 123, 444], [395, 397, 265, 239, 31], [199, 438, 416, 271, 73], [0, 1]]
 g := ![![[444, 455, 300, 306, 134], [394, 145, 122, 255, 438], [307, 434, 318, 155], [244, 243, 459, 319], [402, 156, 203, 346, 285], [461, 243, 259, 75], [397, 217, 1], []], ![[402, 7, 148, 273, 17, 419, 51, 237], [106, 84, 71, 407, 27, 250, 386, 298], [293, 393, 327, 129], [72, 26, 298, 300], [433, 40, 11, 51, 230, 348, 442, 18], [434, 136, 383, 127], [17, 395, 342, 221, 155, 406, 22, 340], [301, 194, 180, 366, 21, 13, 372, 5]], ![[63, 210, 390, 433, 175, 390, 94, 415], [270, 181, 367, 149, 341, 70, 144, 314], [70, 110, 397, 153], [316, 72, 140, 177], [379, 131, 14, 48, 448, 285, 185, 99], [402, 307, 202, 374], [270, 326, 354, 69, 62, 411, 166, 281], [84, 381, 343, 276, 336, 459, 174, 442]], ![[210, 52, 108, 181, 127, 6, 210, 271], [211, 138, 8, 412, 240, 162, 455, 184], [239, 81, 430, 155], [17, 65, 230, 352], [66, 430, 2, 48, 421, 280, 246, 72], [84, 66, 206, 7], [256, 277, 242, 243, 170, 333, 422, 281], [373, 6, 396, 456, 370, 134, 178, 370]], ![[56, 48, 370, 464, 104, 215, 291, 333], [244, 215, 24, 282, 125, 374, 235, 464], [263, 356, 328, 277], [437, 17, 42, 68], [13, 122, 423, 78, 210, 155, 257, 135], [113, 308, 344, 120], [137, 208, 150, 336, 19, 334, 319, 29], [444, 270, 215, 48, 398, 112, 19, 6]]]
 h' := ![![[138, 223, 424, 301, 386], [438, 183, 464, 310, 282], [21, 140, 375, 17, 275], [262, 75, 50, 224, 33], [390, 77, 428, 458, 188], [377, 123, 75, 147, 288], [420, 334, 317, 390, 104], [0, 0, 0, 1], [0, 1]], ![[419, 342, 296, 123, 444], [91, 93, 227, 3, 371], [283, 246, 23, 206, 258], [241, 148, 146, 184, 237], [109, 180, 323, 300, 208], [386, 460, 105, 257, 42], [144, 63, 94, 372, 320], [325, 136, 237, 0, 295], [138, 223, 424, 301, 386]], ![[395, 397, 265, 239, 31], [156, 169, 143, 92, 344], [94, 144, 75, 259, 397], [72, 458, 356, 360, 66], [10, 271, 129, 201, 287], [228, 247, 254, 30, 4], [267, 360, 216, 440, 29], [50, 184, 389, 176, 370], [419, 342, 296, 123, 444]], ![[199, 438, 416, 271, 73], [32, 223, 131, 72, 97], [419, 291, 77, 450, 75], [406, 217, 180, 213, 434], [294, 325, 21, 450, 207], [123, 257, 69, 219, 366], [354, 436, 112, 133, 53], [449, 350, 424, 276, 368], [395, 397, 265, 239, 31]], ![[0, 1], [226, 266, 436, 457, 307], [339, 113, 384, 2, 396], [460, 36, 202, 420, 164], [41, 81, 33, 459, 44], [286, 314, 431, 281, 234], [253, 208, 195, 66, 428], [112, 264, 351, 14, 368], [199, 438, 416, 271, 73]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [218, 180, 6, 142], [], [], []]
 b := ![[], [400, 391, 323, 263, 94], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI467N0 : CertifiedPrimeIdeal' SI467N0 467 where
  n := 5
  hpos := by decide
  P := [6, 437, 452, 459, 250, 1]
  hirr := P467P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1213722726, 2090561926, 1815062281, 932275369, 251666767]
  a := ![0, -2, -3, -3, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2598978, 4476578, 3886643, 1996307, 538901]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI467N0 : Ideal.IsPrime I467N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI467N0 B_one_repr
lemma NI467N0 : Nat.card (O ⧸ I467N0) = 22211833167107 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI467N0

def PBC467 : ContainsPrimesAboveP 467 ![I467N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI467N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![467, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 467 (by decide) 𝕀

instance hp479 : Fact (Nat.Prime 479) := {out := by norm_num}

def I479N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-169, -117, -42, 39, 32]] i)))

def SI479N0: IdealEqSpanCertificate' Table ![![-169, -117, -42, 39, 32]] 
 ![![479, 0, 0, 0, 0], ![0, 479, 0, 0, 0], ![0, 0, 479, 0, 0], ![117, 433, 447, 1, 0], ![391, 247, 367, 0, 1]] where
  M :=![![![-169, -117, -42, 39, 32], ![640, 173, -234, -116, 78], ![780, 671, 173, -273, -116], ![-1480, -306, 788, 289, -312], ![-3120, -2218, -306, 944, 289]]]
  hmulB := by decide  
  f := ![![![-111, -129, -88, -35, -26]], ![![-520, -511, -258, -150, -70]], ![![-700, -809, -511, -223, -150]], ![![-1153, -1251, -733, -353, -210]], ![![-899, -993, -599, -278, -173]]]
  g := ![![![-36, -52, -61, 39, 32], ![-34, 65, 48, -116, 78], ![163, 308, 344, -273, -116], ![181, -101, -29, 289, -312], ![-473, -1007, -1103, 944, 289]]]
  hle1 := by decide   
  hle2 := by decide  


def P479P0 : CertificateIrreducibleZModOfList' 479 3 2 8 [462, 48, 14, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [478, 474, 186], [466, 4, 293], [0, 1]]
 g := ![![[169, 24, 350], [21, 85, 128], [152, 174, 61], [408, 333, 36], [256, 181, 105], [53, 276], [45, 37, 196], [1]], ![[417, 69, 267, 113], [15, 269, 29, 312], [120, 188, 34, 123], [151, 155, 422, 461], [292, 128, 1, 118], [140, 350], [59, 324, 145, 269], [100, 252, 237, 449]], ![[214, 473, 275, 181], [27, 292, 374, 388], [361, 19, 380, 373], [44, 203, 86, 243], [56, 44, 88, 264], [394, 442], [12, 470, 353, 206], [73, 459, 397, 30]]]
 h' := ![![[478, 474, 186], [357, 233, 395], [189, 183, 420], [230, 212, 260], [41, 50, 473], [309, 165, 50], [286, 195, 252], [17, 431, 465], [0, 1]], ![[466, 4, 293], [348, 436, 371], [323, 181, 272], [123, 394, 236], [7, 446, 175], [330, 81, 234], [377, 449, 395], [262, 427, 117], [478, 474, 186]], ![[0, 1], [200, 289, 192], [215, 115, 266], [377, 352, 462], [212, 462, 310], [104, 233, 195], [152, 314, 311], [2, 100, 376], [466, 4, 293]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [215, 464], []]
 b := ![[], [176, 418, 425], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI479N0 : CertifiedPrimeIdeal' SI479N0 479 where
  n := 3
  hpos := by decide
  P := [462, 48, 14, 1]
  hirr := P479P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-72623961, -44407087, -3315982, -10098298, -4457531]
  a := ![3, -65, 2, -66, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![5953594, 11334376, 12832019, -10098298, -4457531]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI479N0 : Ideal.IsPrime I479N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI479N0 B_one_repr
lemma NI479N0 : Nat.card (O ⧸ I479N0) = 109902239 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI479N0

def I479N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-111, -129, -88, -35, -26]] i)))

def SI479N1: IdealEqSpanCertificate' Table ![![-111, -129, -88, -35, -26]] 
 ![![479, 0, 0, 0, 0], ![0, 479, 0, 0, 0], ![225, 32, 1, 0, 0], ![464, 47, 0, 1, 0], ![442, 165, 0, 0, 1]] where
  M :=![![![-111, -129, -88, -35, -26], ![-520, -511, -258, -150, -70], ![-700, -809, -511, -223, -150], ![-1240, -1250, -680, -361, -188], ![-1880, -2088, -1250, -586, -361]]]
  hmulB := by decide  
  f := ![![![-169, -117, -42, 39, 32]], ![![640, 173, -234, -116, 78]], ![![-35, -42, -35, 10, 20]], ![![-104, -97, -62, 27, 38]], ![![58, -53, -120, -2, 57]]]
  g := ![![![99, 18, -88, -35, -26], ![330, 55, -258, -150, -70], ![593, 106, -511, -223, -150], ![840, 143, -680, -361, -188], ![1484, 261, -1250, -586, -361]]]
  hle1 := by decide   
  hle2 := by decide  


def P479P1 : CertificateIrreducibleZModOfList' 479 2 2 8 [345, 436, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [43, 478], [0, 1]]
 g := ![![[440, 168], [380, 197], [168, 63], [321, 211], [430, 49], [294], [429, 178], [43, 1]], ![[0, 311], [229, 282], [3, 416], [293, 268], [142, 430], [294], [419, 301], [86, 478]]]
 h' := ![![[43, 478], [146, 108], [478, 453], [383, 365], [140, 393], [154, 472], [6, 343], [14, 67], [0, 1]], ![[0, 1], [0, 371], [318, 26], [271, 114], [274, 86], [332, 7], [385, 136], [21, 412], [43, 478]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [192]]
 b := ![[], [331, 96]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI479N1 : CertifiedPrimeIdeal' SI479N1 479 where
  n := 2
  hpos := by decide
  P := [345, 436, 1]
  hirr := P479P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![902, -1282, 119, -1900, -796]
  a := ![1, -4, -1, -5, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2521, 450, 119, -1900, -796]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI479N1 : Ideal.IsPrime I479N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI479N1 B_one_repr
lemma NI479N1 : Nat.card (O ⧸ I479N1) = 229441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI479N1
def MulI479N0 : IdealMulLeCertificate' Table 
  ![![-169, -117, -42, 39, 32]] ![![-111, -129, -88, -35, -26]]
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

def I487N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![27, 6, -16, -1, 2]] i)))

def SI487N0: IdealEqSpanCertificate' Table ![![27, 6, -16, -1, 2]] 
 ![![487, 0, 0, 0, 0], ![0, 487, 0, 0, 0], ![0, 0, 487, 0, 0], ![12, 458, 181, 1, 0], ![263, 232, 326, 0, 1]] where
  M :=![![![27, 6, -16, -1, 2], ![40, 35, 12, -34, -2], ![-20, 14, 35, 13, -34], ![-360, -214, 8, 69, 14], ![140, -92, -214, 1, 69]]]
  hmulB := by decide  
  f := ![![![-99, -8, 8, -7, 8]], ![![160, 5, -16, 8, -14]], ![![-140, -12, 5, -9, 8]], ![![96, 0, -13, 4, -10]], ![![-71, -10, 0, -6, 3]]]
  g := ![![![-1, 0, -1, -1, 2], ![2, 33, 14, -34, -2], ![18, 4, 18, 13, -34], ![-10, -72, -35, 69, 14], ![-37, -34, -47, 1, 69]]]
  hle1 := by decide   
  hle2 := by decide  


def P487P0 : CertificateIrreducibleZModOfList' 487 3 2 8 [54, 138, 341, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [160, 328, 177], [473, 158, 310], [0, 1]]
 g := ![![[466, 455, 185], [206, 246, 392], [320, 351, 232], [196, 467], [41, 91], [81, 212, 378], [339, 331, 375], [1]], ![[344, 250, 175, 284], [64, 169, 201, 463], [142, 322, 449, 220], [142, 32], [471, 444], [124, 216, 391, 55], [184, 89, 196, 408], [134, 302, 270, 251]], ![[94, 465, 6, 425], [249, 60, 183, 317], [419, 386, 477, 436], [231, 271], [30, 124], [62, 50, 370, 478], [140, 10, 275, 368], [55, 10, 221, 236]]]
 h' := ![![[160, 328, 177], [77, 364, 395], [252, 293, 300], [265, 259, 254], [302, 220, 286], [9, 329, 401], [200, 109, 418], [433, 349, 146], [0, 1]], ![[473, 158, 310], [108, 410, 218], [389, 159, 400], [191, 131, 263], [281, 351, 364], [216, 14, 328], [403, 329, 112], [399, 102, 103], [160, 328, 177]], ![[0, 1], [252, 200, 361], [30, 35, 274], [476, 97, 457], [369, 403, 324], [362, 144, 245], [314, 49, 444], [130, 36, 238], [473, 158, 310]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [415, 452], []]
 b := ![[], [3, 83, 102], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI487N0 : CertifiedPrimeIdeal' SI487N0 487 where
  n := 3
  hpos := by decide
  P := [54, 138, 341, 1]
  hirr := P487P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4112054, 5684963, 4404744, 2047789, 806866]
  a := ![1, 18, 4, 17, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-477756, -2298553, -1292163, 2047789, 806866]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI487N0 : Ideal.IsPrime I487N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI487N0 B_one_repr
lemma NI487N0 : Nat.card (O ⧸ I487N0) = 115501303 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI487N0

def I487N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, 2, 0, 0, 0]] i)))

def SI487N1: IdealEqSpanCertificate' Table ![![-7, 2, 0, 0, 0]] 
 ![![487, 0, 0, 0, 0], ![240, 1, 0, 0, 0], ![420, 0, 1, 0, 0], ![128, 0, 0, 1, 0], ![224, 0, 0, 0, 1]] where
  M :=![![![-7, 2, 0, 0, 0], ![0, -7, 4, 0, 0], ![0, 2, -7, 4, 0], ![0, 0, 0, -7, 4], ![40, 24, 0, -2, -7]]]
  hmulB := by decide  
  f := ![![![-801, -798, -456, -224, -128]], ![![-400, -399, -228, -112, -64]], ![![-700, -698, -399, -196, -112]], ![![-224, -224, -128, -63, -36]], ![![-392, -392, -224, -110, -63]]]
  g := ![![![-1, 2, 0, 0, 0], ![0, -7, 4, 0, 0], ![4, 2, -7, 4, 0], ![0, 0, 0, -7, 4], ![-8, 24, 0, -2, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI487N1 : Nat.card (O ⧸ I487N1) = 487 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI487N1)

lemma isPrimeI487N1 : Ideal.IsPrime I487N1 := prime_ideal_of_norm_prime hp487.out _ NI487N1

def I487N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 30, 16, 9, 4]] i)))

def SI487N2: IdealEqSpanCertificate' Table ![![37, 30, 16, 9, 4]] 
 ![![487, 0, 0, 0, 0], ![372, 1, 0, 0, 0], ![449, 0, 1, 0, 0], ![64, 0, 0, 1, 0], ![271, 0, 0, 0, 1]] where
  M :=![![![37, 30, 16, 9, 4], ![80, 101, 60, 28, 18], ![180, 178, 101, 51, 28], ![240, 258, 148, 73, 42], ![420, 446, 258, 127, 73]]]
  hmulB := by decide  
  f := ![![![-109, 28, 136, -61, -18]], ![![-84, 21, 104, -46, -14]], ![![-103, 24, 125, -56, -16]], ![![-8, 6, 16, -9, -2]], ![![-57, 20, 78, -36, -11]]]
  g := ![![![-41, 30, 16, 9, 4], ![-146, 101, 60, 28, 18], ![-251, 178, 101, 51, 28], ![-366, 258, 148, 73, 42], ![-635, 446, 258, 127, 73]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI487N2 : Nat.card (O ⧸ I487N2) = 487 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI487N2)

lemma isPrimeI487N2 : Ideal.IsPrime I487N2 := prime_ideal_of_norm_prime hp487.out _ NI487N2
def MulI487N0 : IdealMulLeCertificate' Table 
  ![![27, 6, -16, -1, 2]] ![![-7, 2, 0, 0, 0]]
  ![![-109, 28, 136, -61, -18]] where
 M := ![![![-109, 28, 136, -61, -18]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI487N1 : IdealMulLeCertificate' Table 
  ![![-109, 28, 136, -61, -18]] ![![37, 30, 16, 9, 4]]
  ![![487, 0, 0, 0, 0]] where
 M := ![![![487, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC487 : ContainsPrimesAboveP 487 ![I487N0, I487N1, I487N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI487N0
    exact isPrimeI487N1
    exact isPrimeI487N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 487 (by decide) (𝕀 ⊙ MulI487N0 ⊙ MulI487N1)
instance hp491 : Fact (Nat.Prime 491) := {out := by norm_num}

def I491N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![74189, 20960, -17420, 10757, -8936]] i)))

def SI491N0: IdealEqSpanCertificate' Table ![![74189, 20960, -17420, 10757, -8936]] 
 ![![491, 0, 0, 0, 0], ![0, 491, 0, 0, 0], ![0, 0, 491, 0, 0], ![0, 0, 0, 491, 0], ![240, 217, 298, 266, 1]] where
  M :=![![![74189, 20960, -17420, 10757, -8936], ![-178720, -50463, 41920, -25904, 21514], ![215140, 60684, -50463, 31163, -25904], ![-169680, -47854, 39724, -24559, 20406], ![204060, 57458, -47854, 29521, -24559]]]
  hmulB := by decide  
  f := ![![![-1, -2, -4, -1, 2]], ![![40, 19, -4, -10, -2]], ![![-20, 6, 19, -3, -10]], ![![-120, -70, 8, 29, -2]], ![![-60, -27, 12, 9, -7]]]
  g := ![![![4519, 3992, 5388, 4863, -8936], ![-10880, -9611, -12972, -11708, 21514], ![13100, 11572, 15619, 14097, -25904], ![-10320, -9116, -12304, -11105, 20406], ![12420, 10971, 14808, 13365, -24559]]]
  hle1 := by decide   
  hle2 := by decide  


def P491P0 : CertificateIrreducibleZModOfList' 491 4 2 8 [32, 444, 339, 133, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [83, 188, 217, 385], [287, 128, 452, 423], [479, 174, 313, 174], [0, 1]]
 g := ![![[381, 468, 353, 401], [333, 8, 176, 424], [486, 420, 239], [358, 285, 28, 117], [195, 166, 1], [248, 6, 134, 238], [112, 165, 358, 1], []], ![[192, 214, 94, 137, 144, 193], [87, 52, 298, 157, 208, 149], [364, 166, 255], [410, 291, 177, 220, 145, 337], [446, 88, 225], [282, 164, 60, 415, 260, 479], [214, 207, 25, 117, 374, 338], [88, 43, 333, 373, 390, 150]], ![[46, 486, 364, 99, 438, 214], [457, 381, 400, 422, 252, 317], [32, 237, 31], [283, 174, 188, 254, 303, 32], [225, 386, 4], [81, 481, 291, 412, 379, 362], [302, 447, 283, 356, 392, 267], [306, 290, 468, 401, 78, 299]], ![[272, 41, 248, 117, 2, 375], [417, 366, 382, 404, 355, 126], [439, 370, 48], [66, 106, 277, 116, 263, 462], [131, 264, 256], [176, 308, 305, 485, 71, 164], [197, 260, 448, 353, 481, 42], [223, 393, 375, 485, 252, 85]]]
 h' := ![![[83, 188, 217, 385], [146, 245, 113, 281], [215, 291, 317, 193], [328, 409, 321, 132], [160, 243, 489, 399], [411, 176, 96, 490], [344, 475, 66, 464], [0, 0, 0, 1], [0, 1]], ![[287, 128, 452, 423], [453, 412, 295, 286], [299, 228, 449, 185], [60, 100, 162, 234], [91, 234, 66, 477], [319, 132, 133, 15], [265, 468, 285, 364], [393, 418, 239, 430], [83, 188, 217, 385]], ![[479, 174, 313, 174], [295, 137, 194, 355], [18, 325, 376, 411], [166, 145, 425, 86], [339, 365, 195, 76], [34, 277, 475, 2], [105, 443, 353, 468], [245, 159, 363, 292], [287, 128, 452, 423]], ![[0, 1], [102, 188, 380, 60], [33, 138, 331, 193], [260, 328, 74, 39], [155, 140, 232, 30], [418, 397, 278, 475], [314, 87, 278, 177], [465, 405, 380, 259], [479, 174, 313, 174]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [144, 303, 101], []]
 b := ![[], [], [309, 445, 372, 182], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI491N0 : CertifiedPrimeIdeal' SI491N0 491 where
  n := 4
  hpos := by decide
  P := [32, 444, 339, 133, 1]
  hirr := P491P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2288625, -4717108, -2616770, 3805749, -1061841]
  a := ![-1, 2, -4, 4, -9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![514365, 459679, 639128, 583005, -1061841]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI491N0 : Ideal.IsPrime I491N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI491N0 B_one_repr
lemma NI491N0 : Nat.card (O ⧸ I491N0) = 58120048561 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI491N0

def I491N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 2, 4, 1, -2]] i)))

def SI491N1: IdealEqSpanCertificate' Table ![![1, 2, 4, 1, -2]] 
 ![![491, 0, 0, 0, 0], ![450, 1, 0, 0, 0], ![387, 0, 1, 0, 0], ![98, 0, 0, 1, 0], ![45, 0, 0, 0, 1]] where
  M :=![![![1, 2, 4, 1, -2], ![-40, -19, 4, 10, 2], ![20, -6, -19, 3, 10], ![120, 70, -8, -29, 2], ![20, 68, 70, -9, -29]]]
  hmulB := by decide  
  f := ![![![-74189, -20960, 17420, -10757, 8936]], ![![-67630, -19107, 15880, -9806, 8146]], ![![-58913, -16644, 13833, -8542, 7096]], ![![-14462, -4086, 3396, -2097, 1742]], ![![-7215, -2038, 1694, -1046, 869]]]
  g := ![![![-5, 2, 4, 1, -2], ![12, -19, 4, 10, 2], ![19, -6, -19, 3, 10], ![-52, 70, -8, -29, 2], ![-113, 68, 70, -9, -29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI491N1 : Nat.card (O ⧸ I491N1) = 491 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI491N1)

lemma isPrimeI491N1 : Ideal.IsPrime I491N1 := prime_ideal_of_norm_prime hp491.out _ NI491N1
def MulI491N0 : IdealMulLeCertificate' Table 
  ![![74189, 20960, -17420, 10757, -8936]] ![![1, 2, 4, 1, -2]]
  ![![491, 0, 0, 0, 0]] where
 M := ![![![-491, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I499N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1771, 605, -486, 295, -232]] i)))

def SI499N0: IdealEqSpanCertificate' Table ![![1771, 605, -486, 295, -232]] 
 ![![499, 0, 0, 0, 0], ![0, 499, 0, 0, 0], ![0, 0, 499, 0, 0], ![113, 198, 128, 1, 0], ![7, 475, 281, 0, 1]] where
  M :=![![![1771, 605, -486, 295, -232], ![-4640, -1499, 1210, -740, 590], ![5900, 1825, -1499, 915, -740], ![-5080, -1490, 1220, -759, 620], ![6200, 1790, -1490, 910, -759]]]
  hmulB := by decide  
  f := ![![![-31, -15, 4, 5, -2]], ![![-40, -51, -30, 10, 10]], ![![100, 25, -51, -35, 10]], ![![3, -17, -24, -4, 6]], ![![17, -35, -57, -10, 15]]]
  g := ![![![-60, 105, 54, 295, -232], ![150, -271, -140, -740, 590], ![-185, 345, 179, 915, -740], ![153, -292, -152, -759, 620], ![-183, 365, 191, 910, -759]]]
  hle1 := by decide   
  hle2 := by decide  


def P499P0 : CertificateIrreducibleZModOfList' 499 3 2 8 [275, 433, 47, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [257, 11, 70], [195, 487, 429], [0, 1]]
 g := ![![[440, 318, 239], [179, 236, 253], [491, 183], [476, 296], [464, 488, 267], [153, 351, 323], [484, 252, 213], [1]], ![[389, 123, 335, 74], [421, 85, 320, 245], [383, 451], [335, 293], [186, 319, 44, 4], [267, 351, 215, 320], [253, 11, 168, 299], [155, 79, 217, 187]], ![[264, 470, 397, 160], [121, 33, 161, 18], [42, 449], [249, 150], [418, 381, 371, 408], [152, 84, 333, 432], [39, 496, 253, 338], [256, 81, 53, 312]]]
 h' := ![![[257, 11, 70], [176, 247, 85], [455, 78, 420], [115, 267, 217], [144, 48, 337], [340, 124, 457], [133, 345, 306], [224, 66, 452], [0, 1]], ![[195, 487, 429], [160, 310, 302], [173, 60, 420], [447, 379, 118], [261, 237, 314], [209, 346, 202], [435, 20, 19], [399, 466, 194], [257, 11, 70]], ![[0, 1], [443, 441, 112], [255, 361, 158], [223, 352, 164], [264, 214, 347], [113, 29, 339], [364, 134, 174], [193, 466, 352], [195, 487, 429]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [382, 483], []]
 b := ![[], [32, 213, 43], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI499N0 : CertifiedPrimeIdeal' SI499N0 499 where
  n := 3
  hpos := by decide
  P := [275, 433, 47, 1]
  hirr := P499P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-755725, 221970, 708804, -393380, -86358]
  a := ![0, -10, 4, -20, 6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![88779, 238740, 150958, -393380, -86358]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI499N0 : Ideal.IsPrime I499N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI499N0 B_one_repr
lemma NI499N0 : Nat.card (O ⧸ I499N0) = 124251499 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI499N0

def I499N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 15, -4, -5, 2]] i)))

def SI499N1: IdealEqSpanCertificate' Table ![![31, 15, -4, -5, 2]] 
 ![![499, 0, 0, 0, 0], ![0, 499, 0, 0, 0], ![437, 371, 1, 0, 0], ![48, 302, 0, 1, 0], ![261, 257, 0, 0, 1]] where
  M :=![![![31, 15, -4, -5, 2], ![40, 51, 30, -10, -10], ![-100, -25, 51, 35, -10], ![-120, -110, -40, 61, 40], ![400, 160, -110, -60, 61]]]
  hmulB := by decide  
  f := ![![![-1771, -605, 486, -295, 232]], ![![4640, 1499, -1210, 740, -590]], ![![1887, 581, -471, 290, -234]], ![![2648, 852, -688, 421, -336]], ![![1451, 452, -366, 225, -181]]]
  g := ![![![3, 5, -4, -5, 2], ![-20, -11, 30, -10, -10], ![-43, -54, 51, 35, -10], ![8, -28, -40, 61, 40], ![71, 87, -110, -60, 61]]]
  hle1 := by decide   
  hle2 := by decide  


def P499P1 : CertificateIrreducibleZModOfList' 499 2 2 8 [109, 282, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [217, 498], [0, 1]]
 g := ![![[291, 293], [57, 186], [412], [156], [], [396, 439], [14, 486], [217, 1]], ![[0, 206], [0, 313], [412], [156], [], [350, 60], [187, 13], [434, 498]]]
 h' := ![![[217, 498], [274, 185], [448, 175], [461, 419], [0, 125], [249], [470, 44], [299, 74], [0, 1]], ![[0, 1], [0, 314], [0, 324], [67, 80], [179, 374], [249], [38, 455], [389, 425], [217, 498]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [215]]
 b := ![[], [437, 357]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI499N1 : CertifiedPrimeIdeal' SI499N1 499 where
  n := 2
  hpos := by decide
  P := [109, 282, 1]
  hirr := P499P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4104, 197, -833, 622, -1545]
  a := ![13, 0, -3, 1, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1486, 1039, -833, 622, -1545]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI499N1 : Ideal.IsPrime I499N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI499N1 B_one_repr
lemma NI499N1 : Nat.card (O ⧸ I499N1) = 249001 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI499N1
def MulI499N0 : IdealMulLeCertificate' Table 
  ![![1771, 605, -486, 295, -232]] ![![31, 15, -4, -5, 2]]
  ![![499, 0, 0, 0, 0]] where
 M := ![![![-499, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC499 : ContainsPrimesAboveP 499 ![I499N0, I499N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI499N0
    exact isPrimeI499N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 499 (by decide) (𝕀 ⊙ MulI499N0)
instance hp503 : Fact (Nat.Prime 503) := {out := by norm_num}

def I503N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![27, 59, 54, 14, 0]] i)))

def SI503N0: IdealEqSpanCertificate' Table ![![27, 59, 54, 14, 0]] 
 ![![503, 0, 0, 0, 0], ![0, 503, 0, 0, 0], ![0, 0, 503, 0, 0], ![469, 112, 435, 1, 0], ![203, 20, 15, 0, 1]] where
  M :=![![![27, 59, 54, 14, 0], ![0, 81, 118, 108, 28], ![280, 227, 81, 104, 108], ![1080, 788, 168, -27, 90], ![900, 1164, 788, 123, -27]]]
  hmulB := by decide  
  f := ![![![4069, 405, -460, 318, -360]], ![![-7200, -711, 810, -560, 636]], ![![6360, 621, -711, 492, -560]], ![![7687, 756, -863, 597, -678]], ![![1549, 154, -175, 121, -137]]]
  g := ![![![-13, -3, -12, 14, 0], ![-112, -25, -94, 108, 28], ![-140, -27, -93, 104, 108], ![-9, 4, 21, -27, 90], ![-102, -24, -104, 123, -27]]]
  hle1 := by decide   
  hle2 := by decide  


def P503P0 : CertificateIrreducibleZModOfList' 503 3 2 8 [27, 305, 334, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [391, 81, 376], [281, 421, 127], [0, 1]]
 g := ![![[414, 312, 473], [432, 280, 384], [471, 52, 141], [403, 143], [496, 437, 27], [25, 427, 384], [479, 46, 393], [1]], ![[26, 42, 260, 154], [399, 149, 193, 484], [349, 397, 377, 271], [476, 143], [147, 109, 161, 462], [34, 25, 297, 300], [499, 216, 283, 271], [412, 167, 419, 336]], ![[488, 221, 487, 127], [224, 294, 461, 358], [400, 74, 51, 261], [], [277, 309, 379, 295], [256, 165, 271, 218], [353, 15, 446, 442], [460, 67, 488, 167]]]
 h' := ![![[391, 81, 376], [408, 55, 305], [361, 335, 348], [193, 333, 101], [189, 303, 326], [331, 362, 193], [145, 268, 348], [476, 198, 169], [0, 1]], ![[281, 421, 127], [97, 154, 197], [224, 155, 345], [410, 468, 230], [206, 159, 177], [349, 9, 69], [470, 261, 303], [396, 120, 230], [391, 81, 376]], ![[0, 1], [165, 294, 1], [208, 13, 313], [132, 205, 172], [254, 41], [496, 132, 241], [279, 477, 355], [363, 185, 104], [281, 421, 127]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [303, 325], []]
 b := ![[], [91, 205, 260], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI503N0 : CertifiedPrimeIdeal' SI503N0 503 where
  n := 3
  hpos := by decide
  P := [27, 305, 334, 1]
  hirr := P503P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-98945, -5302, 47874, -107634, 50644]
  a := ![-1, -4, 2, -5, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![79723, 21942, 91668, -107634, 50644]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI503N0 : Ideal.IsPrime I503N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI503N0 B_one_repr
lemma NI503N0 : Nat.card (O ⧸ I503N0) = 127263527 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI503N0

def I503N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, 3, 6, -1, -2]] i)))

def SI503N1: IdealEqSpanCertificate' Table ![![-7, 3, 6, -1, -2]] 
 ![![503, 0, 0, 0, 0], ![252, 1, 0, 0, 0], ![440, 0, 1, 0, 0], ![267, 0, 0, 1, 0], ![59, 0, 0, 0, 1]] where
  M :=![![![-7, 3, 6, -1, -2], ![-40, -25, 6, 14, -2], ![-20, -29, -25, 7, 14], ![160, 74, -32, -39, 8], ![80, 112, 74, -36, -39]]]
  hmulB := by decide  
  f := ![![![8471, 2499, -1948, 1257, -1004]], ![![4204, 1241, -966, 624, -498]], ![![7460, 2201, -1715, 1107, -884]], ![![4459, 1317, -1024, 662, -528]], ![![1043, 309, -238, 155, -123]]]
  g := ![![![-6, 3, 6, -1, -2], ![0, -25, 6, 14, -2], ![31, -29, -25, 7, 14], ![11, 74, -32, -39, 8], ![-97, 112, 74, -36, -39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI503N1 : Nat.card (O ⧸ I503N1) = 503 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI503N1)

lemma isPrimeI503N1 : Ideal.IsPrime I503N1 := prime_ideal_of_norm_prime hp503.out _ NI503N1

def I503N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-27, -22, -6, 9, 4]] i)))

def SI503N2: IdealEqSpanCertificate' Table ![![-27, -22, -6, 9, 4]] 
 ![![503, 0, 0, 0, 0], ![387, 1, 0, 0, 0], ![314, 0, 1, 0, 0], ![162, 0, 0, 1, 0], ![342, 0, 0, 0, 1]] where
  M :=![![![-27, -22, -6, 9, 4], ![80, 15, -44, -16, 18], ![180, 126, 15, -53, -16], ![-200, -6, 148, 31, -62], ![-620, -398, -6, 179, 31]]]
  hmulB := by decide  
  f := ![![![-4029, 164, 766, -173, 474]], ![![-3081, 131, 590, -131, 364]], ![![-2522, 108, 483, -107, 298]], ![![-1286, 62, 252, -53, 154]], ![![-2726, 128, 530, -113, 325]]]
  g := ![![![15, -22, -6, 9, 4], ![9, 15, -44, -16, 18], ![-78, 126, 15, -53, -16], ![-56, -6, 148, 31, -62], ![230, -398, -6, 179, 31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI503N2 : Nat.card (O ⧸ I503N2) = 503 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI503N2)

lemma isPrimeI503N2 : Ideal.IsPrime I503N2 := prime_ideal_of_norm_prime hp503.out _ NI503N2
def MulI503N0 : IdealMulLeCertificate' Table 
  ![![27, 59, 54, 14, 0]] ![![-7, 3, 6, -1, -2]]
  ![![-1389, -1924, -1282, 631, 696]] where
 M := ![![![-1389, -1924, -1282, 631, 696]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI503N1 : IdealMulLeCertificate' Table 
  ![![-1389, -1924, -1282, 631, 696]] ![![-27, -22, -6, 9, 4]]
  ![![503, 0, 0, 0, 0]] where
 M := ![![![-904897, -440628, 162972, 230374, -37222]]]
 hmul := by decide  
 g := ![![![![-1799, -876, 324, 458, -74]]]]
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

def I509N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, 7, 4, 5, 0]] i)))

def SI509N0: IdealEqSpanCertificate' Table ![![9, 7, 4, 5, 0]] 
 ![![509, 0, 0, 0, 0], ![0, 509, 0, 0, 0], ![314, 29, 1, 0, 0], ![56, 80, 0, 1, 0], ![330, 253, 0, 0, 1]] where
  M :=![![![9, 7, 4, 5, 0], ![0, 13, 14, 8, 10], ![100, 67, 13, 9, 8], ![80, 98, 60, 5, 4], ![40, 94, 98, 58, 5]]]
  hmulB := by decide  
  f := ![![![3101, 329, -362, 249, -278]], ![![-5560, -597, 658, -446, 498]], ![![1606, 170, -187, 129, -144]], ![![-536, -58, 64, -43, 48]], ![![-750, -83, 92, -60, 67]]]
  g := ![![![-3, -1, 4, 5, 0], ![-16, -7, 14, 8, 10], ![-14, -6, 13, 9, 8], ![-40, -6, 60, 5, 4], ![-70, -17, 98, 58, 5]]]
  hle1 := by decide   
  hle2 := by decide  


def P509P0 : CertificateIrreducibleZModOfList' 509 2 2 8 [342, 243, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [266, 508], [0, 1]]
 g := ![![[282, 64], [465], [281, 56], [108, 412], [100, 237], [231, 181], [174, 62], [266, 1]], ![[0, 445], [465], [416, 453], [265, 97], [26, 272], [22, 328], [378, 447], [23, 508]]]
 h' := ![![[266, 508], [417, 8], [99, 90], [221, 51], [412, 260], [402, 42], [45, 118], [139, 172], [0, 1]], ![[0, 1], [0, 501], [116, 419], [44, 458], [348, 249], [376, 467], [384, 391], [81, 337], [266, 508]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [360]]
 b := ![[], [492, 180]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI509N0 : CertifiedPrimeIdeal' SI509N0 509 where
  n := 2
  hpos := by decide
  P := [342, 243, 1]
  hirr := P509P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-40, -1021, 2354, -2902, 2380]
  a := ![3, -4, 7, -8, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2676, -863, 2354, -2902, 2380]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI509N0 : Ideal.IsPrime I509N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI509N0 B_one_repr
lemma NI509N0 : Nat.card (O ⧸ I509N0) = 259081 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI509N0

def I509N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-829, -100, 104, -71, 76]] i)))

def SI509N1: IdealEqSpanCertificate' Table ![![-829, -100, 104, -71, 76]] 
 ![![509, 0, 0, 0, 0], ![0, 509, 0, 0, 0], ![50, 338, 1, 0, 0], ![406, 52, 0, 1, 0], ![454, 442, 0, 0, 1]] where
  M :=![![![-829, -100, 104, -71, 76], ![1520, 187, -200, 132, -142], ![-1420, -192, 187, -129, 132], ![560, 82, -92, 55, -58], ![-580, -114, 82, -63, 55]]]
  hmulB := by decide  
  f := ![![![119, 58, -24, -35, 6]], ![![120, 167, 116, -54, -70]], ![![90, 116, 75, -39, -46]], ![![106, 62, -8, -33, -2]], ![![214, 198, 78, -79, -55]]]
  g := ![![![-23, -128, 104, -71, 76], ![44, 243, -200, 132, -142], ![-36, -226, 187, -129, 132], ![18, 106, -92, 55, -58], ![-8, -96, 82, -63, 55]]]
  hle1 := by decide   
  hle2 := by decide  


def P509P1 : CertificateIrreducibleZModOfList' 509 2 2 8 [59, 455, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [54, 508], [0, 1]]
 g := ![![[163, 342], [107], [206, 150], [471, 211], [196, 21], [396, 387], [223, 125], [54, 1]], ![[307, 167], [107], [162, 359], [158, 298], [312, 488], [425, 122], [356, 384], [108, 508]]]
 h' := ![![[54, 508], [76, 191], [62, 427], [206, 349], [143, 138], [50, 408], [77, 204], [377, 312], [0, 1]], ![[0, 1], [210, 318], [215, 82], [219, 160], [469, 371], [195, 101], [404, 305], [428, 197], [54, 508]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [98]]
 b := ![[], [204, 49]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI509N1 : CertifiedPrimeIdeal' SI509N1 509 where
  n := 2
  hpos := by decide
  P := [59, 455, 1]
  hirr := P509P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![635, 97, 920, -333, 2596]
  a := ![1, 0, 2, -1, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2139, -2831, 920, -333, 2596]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI509N1 : Ideal.IsPrime I509N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI509N1 B_one_repr
lemma NI509N1 : Nat.card (O ⧸ I509N1) = 259081 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI509N1

def I509N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, 1, -2, 0, 0]] i)))

def SI509N2: IdealEqSpanCertificate' Table ![![9, 1, -2, 0, 0]] 
 ![![509, 0, 0, 0, 0], ![284, 1, 0, 0, 0], ![392, 0, 1, 0, 0], ![184, 0, 0, 1, 0], ![340, 0, 0, 0, 1]] where
  M :=![![![9, 1, -2, 0, 0], ![0, 7, 2, -4, 0], ![0, 1, 7, 2, -4], ![-40, -24, 0, 11, 2], ![20, -8, -24, -1, 11]]]
  hmulB := by decide  
  f := ![![![-299, -51, 176, -44, 72]], ![![-164, -27, 98, -24, 40]], ![![-232, -39, 137, -34, 56]], ![![-104, -16, 64, -15, 26]], ![![-200, -32, 120, -29, 49]]]
  g := ![![![1, 1, -2, 0, 0], ![-4, 7, 2, -4, 0], ![-4, 1, 7, 2, -4], ![8, -24, 0, 11, 2], ![16, -8, -24, -1, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI509N2 : Nat.card (O ⧸ I509N2) = 509 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI509N2)

lemma isPrimeI509N2 : Ideal.IsPrime I509N2 := prime_ideal_of_norm_prime hp509.out _ NI509N2
def MulI509N0 : IdealMulLeCertificate' Table 
  ![![9, 7, 4, 5, 0]] ![![-829, -100, 104, -71, 76]]
  ![![299, 51, -176, 44, -72]] where
 M := ![![![299, 51, -176, 44, -72]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI509N1 : IdealMulLeCertificate' Table 
  ![![299, 51, -176, 44, -72]] ![![9, 1, -2, 0, 0]]
  ![![509, 0, 0, 0, 0]] where
 M := ![![![-509, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC509 : ContainsPrimesAboveP 509 ![I509N0, I509N1, I509N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI509N0
    exact isPrimeI509N1
    exact isPrimeI509N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 509 (by decide) (𝕀 ⊙ MulI509N0 ⊙ MulI509N1)
instance hp521 : Fact (Nat.Prime 521) := {out := by norm_num}

def I521N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![521, 0, 0, 0, 0]] i)))

def SI521N0: IdealEqSpanCertificate' Table ![![521, 0, 0, 0, 0]] 
 ![![521, 0, 0, 0, 0], ![0, 521, 0, 0, 0], ![0, 0, 521, 0, 0], ![0, 0, 0, 521, 0], ![0, 0, 0, 0, 521]] where
  M :=![![![521, 0, 0, 0, 0], ![0, 521, 0, 0, 0], ![0, 0, 521, 0, 0], ![0, 0, 0, 521, 0], ![0, 0, 0, 0, 521]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P521P0 : CertificateIrreducibleZModOfList' 521 5 2 9 [391, 16, 339, 385, 30, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [103, 303, 416, 313, 106], [354, 420, 515, 178, 267], [312, 73, 434, 400, 39], [243, 245, 198, 151, 109], [0, 1]]
 g := ![![[109, 91, 180, 462, 160], [436, 330, 121, 290], [361, 279, 376, 21], [413, 223, 136, 284, 495], [379, 322, 121, 1], [32, 64, 220, 36], [450, 515, 491, 1], [], []], ![[475, 471, 389, 53, 292, 189, 125, 464], [503, 380, 366, 355], [373, 56, 281, 263], [24, 220, 261, 240, 260, 283, 336, 234], [471, 71, 461, 144], [132, 399, 433, 485], [13, 235, 193, 144], [229, 424, 187, 286], [162, 18, 196, 295]], ![[16, 57, 473, 103, 417, 370, 1, 427], [8, 380, 411, 242], [394, 406, 85, 499], [401, 264, 512, 36, 16, 58, 52, 424], [504, 288, 315, 417], [503, 280, 208, 20], [278, 428, 228, 202], [53, 402, 81, 45], [417, 226, 265, 433]], ![[105, 175, 514, 92, 77, 505, 317, 205], [233, 75, 393, 123], [503, 424, 300, 417], [164, 411, 409, 493, 411, 108, 307, 150], [488, 94, 403, 148], [473, 312, 149, 263], [62, 257, 74, 309], [276, 418, 519, 258], [235, 8, 158, 479]], ![[164, 267, 102, 375, 244, 142, 290, 107], [127, 325, 15, 185], [187, 26, 295, 466], [88, 279, 486, 131, 144, 140, 482, 178], [309, 311, 90, 198], [373, 46, 370, 16], [410, 381, 118, 256], [500, 401, 520, 18], [377, 165, 29, 419]]]
 h' := ![![[103, 303, 416, 313, 106], [438, 494, 354, 349, 224], [248, 271, 76, 482, 281], [27, 299, 272, 476, 313], [492, 277, 411, 235, 449], [14, 127, 356, 185, 520], [148, 356, 467, 282, 6], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[354, 420, 515, 178, 267], [291, 380, 410, 282, 244], [248, 451, 479, 357, 462], [70, 72, 362, 118, 28], [201, 451, 407, 489, 378], [457, 258, 437, 83, 509], [392, 519, 194, 123, 368], [113, 502, 367, 181, 509], [409, 167, 336, 413, 478], [103, 303, 416, 313, 106]], ![[312, 73, 434, 400, 39], [336, 2, 222, 80, 423], [410, 175, 392, 436, 387], [374, 379, 355, 369, 127], [342, 30, 374, 245, 91], [220, 343, 514, 102, 377], [146, 434, 272, 88, 123], [146, 208, 308, 87, 108], [302, 174, 145, 479, 76], [354, 420, 515, 178, 267]], ![[243, 245, 198, 151, 109], [269, 84, 42, 368, 290], [459, 342, 15, 406, 57], [162, 142, 191, 229, 144], [3, 102, 32, 413, 416], [474, 456, 450, 281, 80], [45, 310, 507, 4, 28], [454, 504, 217, 399, 440], [249, 110, 156, 263, 193], [312, 73, 434, 400, 39]], ![[0, 1], [461, 82, 14, 484, 382], [86, 324, 80, 403, 376], [493, 150, 383, 371, 430], [445, 182, 339, 181, 229], [161, 379, 327, 391, 77], [327, 465, 123, 24, 517], [13, 349, 150, 375, 505], [212, 70, 404, 408, 295], [243, 245, 198, 151, 109]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56, 146, 172, 384], [], [], []]
 b := ![[], [445, 363, 406, 74, 134], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI521N0 : CertifiedPrimeIdeal' SI521N0 521 where
  n := 5
  hpos := by decide
  P := [391, 16, 339, 385, 30, 1]
  hirr := P521P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![53663, 1563, -19277, 29176, -10941]
  a := ![4, 1, -1, 2, -1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![103, 3, -37, 56, -21]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI521N0 : Ideal.IsPrime I521N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI521N0 B_one_repr
lemma NI521N0 : Nat.card (O ⧸ I521N0) = 38387392786601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI521N0

def PBC521 : ContainsPrimesAboveP 521 ![I521N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI521N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![521, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 521 (by decide) 𝕀

instance hp523 : Fact (Nat.Prime 523) := {out := by norm_num}

def I523N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![523, 0, 0, 0, 0]] i)))

def SI523N0: IdealEqSpanCertificate' Table ![![523, 0, 0, 0, 0]] 
 ![![523, 0, 0, 0, 0], ![0, 523, 0, 0, 0], ![0, 0, 523, 0, 0], ![0, 0, 0, 523, 0], ![0, 0, 0, 0, 523]] where
  M :=![![![523, 0, 0, 0, 0], ![0, 523, 0, 0, 0], ![0, 0, 523, 0, 0], ![0, 0, 0, 523, 0], ![0, 0, 0, 0, 523]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P523P0 : CertificateIrreducibleZModOfList' 523 5 2 9 [120, 83, 91, 252, 69, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [159, 263, 514, 335, 344], [515, 479, 392, 463, 478], [161, 37, 522, 363, 320], [142, 266, 141, 408, 427], [0, 1]]
 g := ![![[404, 381, 287, 76, 130], [81, 376, 273, 327, 68], [68, 56, 16, 112], [390, 121, 449, 323, 395], [394, 171, 415, 281], [25, 274, 411, 158], [102, 325, 454, 1], [], []], ![[124, 476, 332, 294, 115, 463, 308, 8], [340, 4, 359, 283, 480, 345, 389, 447], [502, 89, 506, 371], [125, 197, 394, 513, 379, 236, 386, 48], [156, 474, 361, 443], [132, 235, 268, 250], [266, 234, 165, 54], [286, 70, 193, 422], [5, 0, 252, 138]], ![[169, 28, 113, 74, 407, 390, 28, 196], [373, 43, 285, 117, 289, 79, 112, 511], [226, 217, 478, 114], [366, 250, 502, 121, 92, 174, 9, 9], [22, 442, 16, 290], [402, 51, 327, 410], [147, 450, 213, 150], [134, 264, 350, 420], [409, 190, 86, 456]], ![[378, 518, 483, 495, 491, 159, 22, 39], [44, 67, 169, 432, 250, 469, 460, 447], [292, 342, 252, 23], [178, 304, 362, 239, 268, 128, 195, 61], [480, 270, 299, 254], [362, 214, 377, 190], [26, 324, 355, 345], [268, 389, 403, 456], [490, 190, 238, 415]], ![[281, 396, 490, 18, 90, 278, 10, 34], [297, 348, 517, 296, 377, 91, 409, 243], [199, 75, 175, 490], [218, 208, 407, 120, 279, 368, 65, 39], [287, 436, 224, 166], [1, 420, 508, 150], [456, 372, 517, 444], [216, 194, 10, 63], [218, 232, 178, 325]]]
 h' := ![![[159, 263, 514, 335, 344], [217, 449, 64, 150, 201], [411, 356, 192, 514, 157], [270, 256, 383, 301, 482], [89, 449, 63, 407, 75], [204, 361, 460, 6, 430], [312, 127, 265, 13, 415], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[515, 479, 392, 463, 478], [236, 299, 116, 511, 317], [396, 247, 422, 268, 117], [299, 241, 330, 322, 246], [249, 63, 91, 207, 492], [294, 335, 465, 316, 135], [114, 437, 281, 345, 36], [261, 136, 288, 347, 454], [100, 62, 48, 300, 435], [159, 263, 514, 335, 344]], ![[161, 37, 522, 363, 320], [507, 14, 456, 501, 230], [285, 251, 442, 201, 240], [124, 479, 210, 140, 239], [472, 277, 259, 422, 124], [180, 297, 499, 30, 142], [178, 504, 309, 360, 55], [6, 198, 501, 161, 408], [146, 441, 345, 247, 233], [515, 479, 392, 463, 478]], ![[142, 266, 141, 408, 427], [333, 68, 129, 187, 182], [314, 205, 319, 82, 72], [248, 306, 107, 418, 447], [24, 260, 180, 101, 116], [162, 114, 188, 391, 192], [453, 423, 371, 158, 425], [459, 195, 76, 53, 297], [70, 221, 514, 105, 478], [161, 37, 522, 363, 320]], ![[0, 1], [286, 216, 281, 220, 116], [106, 510, 194, 504, 460], [336, 287, 16, 388, 155], [454, 520, 453, 432, 239], [199, 462, 480, 303, 147], [169, 78, 343, 170, 115], [180, 517, 181, 485, 409], [280, 322, 138, 394, 423], [142, 266, 141, 408, 427]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [370, 442, 64, 161], [], [], []]
 b := ![[], [201, 392, 243, 444, 296], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI523N0 : CertifiedPrimeIdeal' SI523N0 523 where
  n := 5
  hpos := by decide
  P := [120, 83, 91, 252, 69, 1]
  hirr := P523P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1134530592788, -1329339453874, -857331877516, -446574484361, -227093700248]
  a := ![7, 2, -24, 2, -23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2169274556, -2541758038, -1639257892, -853870907, -434213576]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI523N0 : Ideal.IsPrime I523N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI523N0 B_one_repr
lemma NI523N0 : Nat.card (O ⧸ I523N0) = 39129873538843 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI523N0

def PBC523 : ContainsPrimesAboveP 523 ![I523N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI523N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![523, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 523 (by decide) 𝕀



lemma PB547I10_primes (p : ℕ) :
  p ∈ Set.range ![467, 479, 487, 491, 499, 503, 509, 521, 523] ↔ Nat.Prime p ∧ 463 < p ∧ p ≤ 523 := by
  rw [← List.mem_ofFn']
  convert primes_range 463 523 (by omega)

def PB547I10 : PrimesBelowBoundCertificateInterval O 463 523 547 where
  m := 9
  g := ![1, 2, 3, 2, 2, 3, 3, 1, 1]
  P := ![467, 479, 487, 491, 499, 503, 509, 521, 523]
  hP := PB547I10_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I467N0]
    · exact ![I479N0, I479N1]
    · exact ![I487N0, I487N1, I487N2]
    · exact ![I491N0, I491N1]
    · exact ![I499N0, I499N1]
    · exact ![I503N0, I503N1, I503N2]
    · exact ![I509N0, I509N1, I509N2]
    · exact ![I521N0]
    · exact ![I523N0]
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
    · exact ![22211833167107]
    · exact ![109902239, 229441]
    · exact ![115501303, 487, 487]
    · exact ![58120048561, 491]
    · exact ![124251499, 249001]
    · exact ![127263527, 503, 503]
    · exact ![259081, 259081, 509]
    · exact ![38387392786601]
    · exact ![39129873538843]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI467N0
    · dsimp ; intro j
      fin_cases j
      exact NI479N0
      exact NI479N1
    · dsimp ; intro j
      fin_cases j
      exact NI487N0
      exact NI487N1
      exact NI487N2
    · dsimp ; intro j
      fin_cases j
      exact NI491N0
      exact NI491N1
    · dsimp ; intro j
      fin_cases j
      exact NI499N0
      exact NI499N1
    · dsimp ; intro j
      fin_cases j
      exact NI503N0
      exact NI503N1
      exact NI503N2
    · dsimp ; intro j
      fin_cases j
      exact NI509N0
      exact NI509N1
      exact NI509N2
    · dsimp ; intro j
      fin_cases j
      exact NI521N0
    · dsimp ; intro j
      fin_cases j
      exact NI523N0
  β := ![I487N1, I487N2, I491N1, I503N1, I503N2, I509N2]
  Il := ![[], [], [I487N1, I487N2], [I491N1], [], [I503N1, I503N2], [I509N2], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
