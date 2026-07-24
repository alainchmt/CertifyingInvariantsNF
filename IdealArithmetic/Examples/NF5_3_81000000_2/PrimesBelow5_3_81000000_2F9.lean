
import IdealArithmetic.Examples.NF5_3_81000000_2.RI5_3_81000000_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp421 : Fact (Nat.Prime 421) := {out := by norm_num}

def I421N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-235, -511, -261, 2, 34]] i)))

def SI421N0: IdealEqSpanCertificate' Table ![![-235, -511, -261, 2, 34]] 
 ![![421, 0, 0, 0, 0], ![0, 421, 0, 0, 0], ![406, 6, 1, 0, 0], ![90, 370, 0, 1, 0], ![46, 195, 0, 0, 1]] where
  M :=![![![-235, -511, -261, 2, 34], ![204, 275, 1, -23, 4], ![24, 264, 312, 29, -46], ![-276, -666, -397, -10, 58], ![162, 165, -59, -10, 13]]]
  hmulB := by decide  
  f := ![![![12509, 15289, 10921, 640, -1632]], ![![-9792, -11971, -8551, -503, 1280]], ![![11942, 14596, 10426, 611, -1558]], ![![-5946, -7270, -5193, -306, 778]], ![![-3172, -3878, -2770, -163, 415]]]
  g := ![![![247, -15, -261, 2, 34], ![4, 19, 1, -23, 4], ![-302, -8, 312, 29, -46], ![378, -14, -397, -10, 58], ![58, 4, -59, -10, 13]]]
  hle1 := by decide   
  hle2 := by decide  


def P421P0 : CertificateIrreducibleZModOfList' 421 2 2 8 [178, 44, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [377, 420], [0, 1]]
 g := ![![[180, 272], [132], [122, 124], [240], [377], [405, 81], [3], [377, 1]], ![[0, 149], [132], [139, 297], [240], [377], [209, 340], [3], [333, 420]]]
 h' := ![![[377, 420], [323, 170], [176, 72], [97, 185], [372, 161], [322, 279], [411, 412], [254, 74], [0, 1]], ![[0, 1], [0, 251], [376, 349], [377, 236], [24, 260], [255, 142], [386, 9], [366, 347], [377, 420]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [216]]
 b := ![[], [271, 108]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI421N0 : CertifiedPrimeIdeal' SI421N0 421 where
  n := 2
  hpos := by decide
  P := [178, 44, 1]
  hirr := P421P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3400, 9178, 12700, 7127, 3377]
  a := ![0, -1, -3, -1, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-14132, -7987, 12700, 7127, 3377]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI421N0 : Ideal.IsPrime I421N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI421N0 B_one_repr
lemma NI421N0 : Nat.card (O ⧸ I421N0) = 177241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI421N0

def I421N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![217, 551, 352, 9, -48]] i)))

def SI421N1: IdealEqSpanCertificate' Table ![![217, 551, 352, 9, -48]] 
 ![![421, 0, 0, 0, 0], ![0, 421, 0, 0, 0], ![270, 173, 1, 0, 0], ![21, 232, 0, 1, 0], ![120, 64, 0, 0, 1]] where
  M :=![![![217, 551, 352, 9, -48], ![-288, -503, -160, 16, 18], ![108, -18, -217, -34, 32], ![192, 588, 428, 7, -68], ![-258, -405, -104, -7, -9]]]
  hmulB := by decide  
  f := ![![![961, 1807, 1268, 443, -350]], ![![-2100, -4289, -3000, -1182, 886]], ![![-234, -577, -401, -194, 134]], ![![-1143, -2345, -1640, -650, 486]], ![![-6, -53, -36, -29, 17]]]
  g := ![![![-212, -141, 352, 9, -48], ![96, 53, -160, 16, 18], ![132, 103, -217, -34, 32], ![-255, -168, 428, 7, -68], ![69, 47, -104, -7, -9]]]
  hle1 := by decide   
  hle2 := by decide  


def P421P1 : CertificateIrreducibleZModOfList' 421 2 2 8 [165, 50, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [371, 420], [0, 1]]
 g := ![![[332, 74], [119], [105, 114], [190], [146], [92, 114], [275], [371, 1]], ![[0, 347], [119], [299, 307], [190], [146], [286, 307], [275], [321, 420]]]
 h' := ![![[371, 420], [38, 186], [357, 31], [280, 172], [62, 78], [397, 355], [365, 249], [251, 230], [0, 1]], ![[0, 1], [0, 235], [70, 390], [100, 249], [372, 343], [329, 66], [124, 172], [118, 191], [371, 420]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [367]]
 b := ![[], [167, 394]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI421N1 : CertifiedPrimeIdeal' SI421N1 421 where
  n := 2
  hpos := by decide
  P := [165, 50, 1]
  hirr := P421P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1722, -8264, 794, -1653, 1467]
  a := ![3, -64, 2, -1, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-849, 342, 794, -1653, 1467]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI421N1 : Ideal.IsPrime I421N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI421N1 B_one_repr
lemma NI421N1 : Nat.card (O ⧸ I421N1) = 177241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI421N1

def I421N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 11, 7, 2, -2]] i)))

def SI421N2: IdealEqSpanCertificate' Table ![![5, 11, 7, 2, -2]] 
 ![![421, 0, 0, 0, 0], ![242, 1, 0, 0, 0], ![376, 0, 1, 0, 0], ![365, 0, 0, 1, 0], ![273, 0, 0, 0, 1]] where
  M :=![![![5, 11, 7, 2, -2], ![-12, -25, -17, -7, 4], ![24, 48, 28, 11, -14], ![-84, -186, -151, -70, 22], ![54, 99, 23, -4, -63]]]
  hmulB := by decide  
  f := ![![![-17323, -20909, -14847, -864, 2220]], ![![-9926, -11981, -8507, -495, 1272]], ![![-15496, -18704, -13282, -773, 1986]], ![![-14999, -18103, -12854, -748, 1922]], ![![-11229, -13554, -9624, -560, 1439]]]
  g := ![![![-13, 11, 7, 2, -2], ![33, -25, -17, -7, 4], ![-53, 48, 28, 11, -14], ![288, -186, -151, -70, 22], ![-33, 99, 23, -4, -63]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI421N2 : Nat.card (O ⧸ I421N2) = 421 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI421N2)

lemma isPrimeI421N2 : Ideal.IsPrime I421N2 := prime_ideal_of_norm_prime hp421.out _ NI421N2
def MulI421N0 : IdealMulLeCertificate' Table 
  ![![-235, -511, -261, 2, 34]] ![![217, 551, 352, 9, -48]]
  ![![59597, 119652, 52997, -1641, -6712]] where
 M := ![![![59597, 119652, 52997, -1641, -6712]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI421N1 : IdealMulLeCertificate' Table 
  ![![59597, 119652, 52997, -1641, -6712]] ![![5, 11, 7, 2, -2]]
  ![![421, 0, 0, 0, 0]] where
 M := ![![![-90515, -151139, -39574, 6315, 4210]]]
 hmul := by decide  
 g := ![![![![-215, -359, -94, 15, 10]]]]
 hle2 := by decide  


def PBC421 : ContainsPrimesAboveP 421 ![I421N0, I421N1, I421N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI421N0
    exact isPrimeI421N1
    exact isPrimeI421N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 421 (by decide) (𝕀 ⊙ MulI421N0 ⊙ MulI421N1)
instance hp431 : Fact (Nat.Prime 431) := {out := by norm_num}

def I431N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7897, 9684, 6940, 436, -1012]] i)))

def SI431N0: IdealEqSpanCertificate' Table ![![7897, 9684, 6940, 436, -1012]] 
 ![![431, 0, 0, 0, 0], ![0, 431, 0, 0, 0], ![0, 0, 431, 0, 0], ![0, 0, 0, 431, 0], ![341, 263, 356, 158, 1]] where
  M :=![![![7897, 9684, 6940, 436, -1012], ![-6072, -7283, -5060, -144, 872], ![5232, 7008, 5653, 1044, -288], ![-1728, 912, 3732, 3637, 2088], ![3648, 11292, 15108, 8652, 3781]]]
  hmulB := by decide  
  f := ![![![-25, -12, 28, 4, -4]], ![![-24, -85, -68, 0, 8]], ![![48, 96, 35, -12, 0]], ![![0, 48, 84, 35, -24]], ![![5, 35, 40, 6, -7]]]
  g := ![![![819, 640, 852, 372, -1012], ![-704, -549, -732, -320, 872], ![240, 192, 251, 108, -288], ![-1656, -1272, -1716, -757, 2088], ![-2983, -2281, -3088, -1366, 3781]]]
  hle1 := by decide   
  hle2 := by decide  


def P431P0 : CertificateIrreducibleZModOfList' 431 4 2 8 [106, 121, 408, 52, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [43, 106, 252, 113], [231, 312, 426, 86], [105, 12, 184, 232], [0, 1]]
 g := ![![[394, 60, 209, 50], [182, 62, 48, 12], [134, 183, 83, 424], [110, 265, 177, 197], [131, 342, 389], [260, 400, 287, 410], [141, 379, 1], []], ![[290, 103, 233, 81, 418, 237], [205, 76, 162, 196, 271, 186], [32, 82, 178, 27, 39, 142], [74, 189, 317, 275, 321, 85], [378, 115, 169], [307, 313, 412, 323, 224, 215], [153, 21, 6], [251, 170, 395, 24, 248, 340]], ![[427, 10, 251, 430, 101, 70], [286, 387, 169, 76, 144, 31], [285, 346, 299, 344, 278, 117], [225, 278, 249, 205, 423, 266], [193, 312, 190], [99, 378, 241, 59, 401, 193], [212, 321, 263], [233, 30, 389, 418, 286, 331]], ![[141, 61, 278, 411, 198, 304], [179, 147, 87, 305, 91, 194], [411, 427, 30, 28, 31, 190], [141, 399, 425, 361, 331, 357], [153, 48, 177], [403, 351, 195, 19, 128, 99], [130, 308, 4], [367, 121, 408, 349, 90, 236]]]
 h' := ![![[43, 106, 252, 113], [103, 213, 145, 353], [19, 259, 139, 359], [408, 422, 219, 83], [51, 70, 199, 285], [24, 198, 325, 151], [139, 88, 378, 402], [0, 0, 0, 1], [0, 1]], ![[231, 312, 426, 86], [364, 53, 183, 403], [342, 399, 250, 236], [358, 303, 164, 343], [45, 99, 368, 272], [106, 353, 72, 418], [205, 343, 374, 274], [319, 410, 327, 303], [43, 106, 252, 113]], ![[105, 12, 184, 232], [190, 22, 285, 9], [375, 166, 226, 259], [210, 44, 166, 191], [428, 347, 78, 295], [206, 29, 17, 173], [32, 403, 282, 314], [91, 413, 233, 129], [231, 312, 426, 86]], ![[0, 1], [171, 143, 249, 97], [77, 38, 247, 8], [186, 93, 313, 245], [205, 346, 217, 10], [112, 282, 17, 120], [147, 28, 259, 303], [278, 39, 302, 429], [105, 12, 184, 232]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [365, 91, 185], []]
 b := ![[], [], [368, 3, 1, 63], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI431N0 : CertifiedPrimeIdeal' SI431N0 431 where
  n := 4
  hpos := by decide
  P := [106, 121, 408, 52, 1]
  hirr := P431P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![308501968, 835958181, 1069140406, 584174647, 245079368]
  a := ![1, -3, -1, -1, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-193186920, -147610013, -199951542, -88488087, 245079368]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI431N0 : Ideal.IsPrime I431N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI431N0 B_one_repr
lemma NI431N0 : Nat.card (O ⧸ I431N0) = 34507149121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI431N0

def I431N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![25, 12, -28, -4, 4]] i)))

def SI431N1: IdealEqSpanCertificate' Table ![![25, 12, -28, -4, 4]] 
 ![![431, 0, 0, 0, 0], ![115, 1, 0, 0, 0], ![136, 0, 1, 0, 0], ![307, 0, 0, 1, 0], ![166, 0, 0, 0, 1]] where
  M :=![![![25, 12, -28, -4, 4], ![24, 85, 68, 0, -8], ![-48, -96, -35, 12, 0], ![0, -48, -84, -35, 24], ![96, 228, 156, 36, -35]]]
  hmulB := by decide  
  f := ![![![-7897, -9684, -6940, -436, 1012]], ![![-2093, -2567, -1840, -116, 268]], ![![-2504, -3072, -2203, -140, 320]], ![![-5621, -6900, -4952, -319, 716]], ![![-3050, -3756, -2708, -188, 381]]]
  g := ![![![7, 12, -28, -4, 4], ![-41, 85, 68, 0, -8], ![28, -96, -35, 12, 0], ![55, -48, -84, -35, 24], ![-122, 228, 156, 36, -35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI431N1 : Nat.card (O ⧸ I431N1) = 431 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI431N1)

lemma isPrimeI431N1 : Ideal.IsPrime I431N1 := prime_ideal_of_norm_prime hp431.out _ NI431N1
def MulI431N0 : IdealMulLeCertificate' Table 
  ![![7897, 9684, 6940, 436, -1012]] ![![25, 12, -28, -4, 4]]
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

def I433N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![433, 0, 0, 0, 0]] i)))

def SI433N0: IdealEqSpanCertificate' Table ![![433, 0, 0, 0, 0]] 
 ![![433, 0, 0, 0, 0], ![0, 433, 0, 0, 0], ![0, 0, 433, 0, 0], ![0, 0, 0, 433, 0], ![0, 0, 0, 0, 433]] where
  M :=![![![433, 0, 0, 0, 0], ![0, 433, 0, 0, 0], ![0, 0, 433, 0, 0], ![0, 0, 0, 433, 0], ![0, 0, 0, 0, 433]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P433P0 : CertificateIrreducibleZModOfList' 433 5 2 8 [307, 182, 89, 119, 240, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [15, 306, 22, 363, 88], [110, 13, 177, 263, 249], [304, 302, 259, 133, 62], [197, 244, 408, 107, 34], [0, 1]]
 g := ![![[196, 5, 258, 415, 17], [163, 196, 25, 16], [165, 53, 4, 398], [390, 119, 42, 44], [317, 273, 255, 295, 36], [219, 242, 123, 148, 406], [193, 1], []], ![[355, 321, 408, 301, 245, 373, 412, 286], [79, 146, 193, 127], [153, 366, 110, 16], [411, 94, 332, 128], [114, 67, 1, 414, 393, 421, 308, 72], [397, 432, 110, 32, 141, 363, 295, 155], [410, 411, 138, 286], [155, 66, 168, 167, 88, 219, 21, 363]], ![[160, 409, 213, 57, 93, 405, 149, 87], [341, 210, 79, 99], [332, 429, 151, 3], [43, 239, 76, 72], [344, 186, 353, 286, 57, 280, 390, 97], [31, 313, 230, 134, 333, 188, 289, 377], [152, 337, 16, 334], [231, 85, 405, 284, 232, 13, 122, 67]], ![[75, 80, 419, 412, 351, 318, 266, 183], [317, 326, 102, 109], [240, 153, 425, 254], [293, 373, 136, 139], [11, 395, 309, 367, 176, 10, 404, 245], [273, 117, 71, 360, 226, 203, 81, 386], [191, 210, 74, 98], [246, 404, 120, 65, 35, 89, 217, 178]], ![[119, 141, 96, 242, 291, 49, 127, 397], [205, 415, 37, 215], [386, 279, 44, 425], [304, 391, 304, 99], [152, 418, 357, 128, 5, 341, 123, 306], [219, 55, 298, 372, 370, 294, 379, 430], [305, 126, 194, 33], [98, 369, 381, 193, 301, 98, 373, 334]]]
 h' := ![![[15, 306, 22, 363, 88], [99, 366, 350, 350, 59], [221, 208, 361, 429, 4], [189, 44, 178, 410, 239], [106, 154, 183, 311, 386], [315, 297, 287, 59, 6], [70, 73, 394, 326, 325], [0, 0, 0, 1], [0, 1]], ![[110, 13, 177, 263, 249], [212, 295, 59, 251, 368], [330, 264, 108, 238, 89], [132, 414, 257, 264, 429], [343, 283, 356, 176, 349], [340, 68, 138, 210, 92], [337, 242, 311, 289, 321], [389, 33, 349, 121, 252], [15, 306, 22, 363, 88]], ![[304, 302, 259, 133, 62], [124, 129, 31, 103, 4], [428, 194, 64, 166, 287], [233, 317, 219, 259, 51], [193, 274, 117, 309, 370], [76, 6, 169, 184, 169], [311, 368, 410, 105, 180], [53, 207, 5, 41, 154], [110, 13, 177, 263, 249]], ![[197, 244, 408, 107, 34], [67, 330, 394, 388, 226], [83, 196, 187, 31, 242], [256, 273, 7, 309, 285], [24, 345, 411, 385, 48], [305, 352, 270, 234, 169], [245, 352, 270, 6, 301], [378, 189, 94, 137, 143], [304, 302, 259, 133, 62]], ![[0, 1], [49, 179, 32, 207, 209], [369, 4, 146, 2, 244], [82, 251, 205, 57, 295], [258, 243, 232, 118, 146], [51, 143, 2, 179, 430], [359, 264, 347, 140, 172], [116, 4, 418, 133, 317], [197, 244, 408, 107, 34]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44, 123, 139, 239], [], [], []]
 b := ![[], [81, 7, 19, 3, 386], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI433N0 : CertifiedPrimeIdeal' SI433N0 433 where
  n := 5
  hpos := by decide
  P := [307, 182, 89, 119, 240, 1]
  hirr := P433P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![43573543733492, 118085151519668, 151048914145153, 82537952444761, 34642115970111]
  a := ![1, 19, 4, -1, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![100631740724, 272713975796, 348842757841, 190618827817, 80004886767]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI433N0 : Ideal.IsPrime I433N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI433N0 B_one_repr
lemma NI433N0 : Nat.card (O ⧸ I433N0) = 15220870177393 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI433N0

def PBC433 : ContainsPrimesAboveP 433 ![I433N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI433N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![433, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 433 (by decide) 𝕀

instance hp439 : Fact (Nat.Prime 439) := {out := by norm_num}

def I439N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-35845, -43829, -31312, -1843, 4684]] i)))

def SI439N0: IdealEqSpanCertificate' Table ![![-35845, -43829, -31312, -1843, 4684]] 
 ![![439, 0, 0, 0, 0], ![0, 439, 0, 0, 0], ![0, 0, 439, 0, 0], ![0, 0, 0, 439, 0], ![5, 163, 222, 264, 1]] where
  M :=![![![-35845, -43829, -31312, -1843, 4684], ![28104, 34415, 24588, 1476, -3686], ![-22116, -27186, -19399, -1214, 2952], ![17712, 22164, 15880, 1265, -2428], ![3774, 4239, 3204, 49, -211]]]
  hmulB := by decide  
  f := ![![![-79, -103, 4, 9, -2]], ![![-12, -109, -124, -10, 18]], ![![108, 258, 151, 2, -20]], ![![-120, -192, -40, 11, 4]], ![![-23, -27, 6, 4, -1]]]
  g := ![![![-135, -1839, -2440, -2821, 4684], ![106, 1447, 1920, 2220, -3686], ![-84, -1158, -1537, -1778, 2952], ![68, 952, 1264, 1463, -2428], ![11, 88, 114, 127, -211]]]
  hle1 := by decide   
  hle2 := by decide  


def P439P0 : CertificateIrreducibleZModOfList' 439 4 2 8 [71, 187, 217, 190, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [27, 2, 255, 318], [383, 89, 111, 41], [278, 347, 73, 80], [0, 1]]
 g := ![![[80, 273, 380, 282], [134, 64, 191, 315], [73, 165, 105, 146], [103, 188, 364], [67, 200, 270, 127], [88, 86, 191, 286], [324, 249, 1], []], ![[263, 251, 31, 180, 256, 421], [112, 26, 437, 82, 350, 15], [101, 305, 38, 118, 259, 394], [422, 320, 271], [11, 9, 172, 95, 117, 132], [152, 78, 416, 437, 335, 310], [63, 118, 140], [185, 54, 162, 106, 83, 243]], ![[320, 209, 236, 207, 431, 136], [20, 43, 134, 103, 59, 202], [418, 138, 245, 29, 258, 346], [8, 72, 140], [347, 186, 157, 211, 254, 410], [238, 86, 67, 168, 113, 257], [393, 54, 325], [427, 316, 362, 114, 428, 437]], ![[11, 202, 73, 167, 186, 289], [134, 110, 364, 7, 171, 141], [199, 220, 224, 302, 212, 52], [148, 247, 212], [324, 19, 130, 160, 234, 123], [320, 217, 1, 59, 149, 315], [219, 106, 143], [205, 98, 410, 271, 78, 126]]]
 h' := ![![[27, 2, 255, 318], [144, 12, 272, 54], [85, 62, 86, 321], [66, 361, 244, 407], [72, 357, 43, 398], [337, 73, 90, 38], [263, 314, 271, 116], [0, 0, 0, 1], [0, 1]], ![[383, 89, 111, 41], [309, 311, 249, 325], [370, 234, 89, 64], [90, 198, 363, 2], [229, 184, 403, 195], [229, 342, 199, 310], [408, 245, 398, 52], [402, 187, 194, 225], [27, 2, 255, 318]], ![[278, 347, 73, 80], [248, 428, 417, 244], [401, 286, 431, 218], [116, 264, 161, 146], [95, 87, 329, 214], [373, 402, 130, 154], [201, 387, 257, 257], [397, 141, 130, 312], [383, 89, 111, 41]], ![[0, 1], [287, 127, 379, 255], [429, 296, 272, 275], [282, 55, 110, 323], [80, 250, 103, 71], [362, 61, 20, 376], [385, 371, 391, 14], [224, 111, 115, 340], [278, 347, 73, 80]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [245, 20, 240], []]
 b := ![[], [], [389, 224, 29, 219], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI439N0 : CertifiedPrimeIdeal' SI439N0 439 where
  n := 4
  hpos := by decide
  P := [71, 187, 217, 190, 1]
  hirr := P439P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![35452614140, 96146411976, 123134375814, 67307872634, 28335474341]
  a := ![-1, 0, -4, 2, -9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-241969835, -10301904113, -14048612592, -16886691010, 28335474341]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI439N0 : Ideal.IsPrime I439N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI439N0 B_one_repr
lemma NI439N0 : Nat.card (O ⧸ I439N0) = 37141383841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI439N0

def I439N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-79, -103, 4, 9, -2]] i)))

def SI439N1: IdealEqSpanCertificate' Table ![![-79, -103, 4, 9, -2]] 
 ![![439, 0, 0, 0, 0], ![350, 1, 0, 0, 0], ![420, 0, 1, 0, 0], ![65, 0, 0, 1, 0], ![268, 0, 0, 0, 1]] where
  M :=![![![-79, -103, 4, 9, -2], ![-12, -109, -124, -10, 18], ![108, 258, 151, 2, -20], ![-120, -192, -40, 11, 4], ![-42, -159, -136, -7, 21]]]
  hmulB := by decide  
  f := ![![![-35845, -43829, -31312, -1843, 4684]], ![![-28514, -34865, -24908, -1466, 3726]], ![![-34344, -41994, -30001, -1766, 4488]], ![![-5267, -6439, -4600, -270, 688]], ![![-21874, -26747, -19108, -1125, 2859]]]
  g := ![![![78, -103, 4, 9, -2], ![196, -109, -124, -10, 18], ![-338, 258, 151, 2, -20], ![187, -192, -40, 11, 4], ![245, -159, -136, -7, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI439N1 : Nat.card (O ⧸ I439N1) = 439 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI439N1)

lemma isPrimeI439N1 : Ideal.IsPrime I439N1 := prime_ideal_of_norm_prime hp439.out _ NI439N1
def MulI439N0 : IdealMulLeCertificate' Table 
  ![![-35845, -43829, -31312, -1843, 4684]] ![![-79, -103, 4, 9, -2]]
  ![![439, 0, 0, 0, 0]] where
 M := ![![![439, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC439 : ContainsPrimesAboveP 439 ![I439N0, I439N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI439N0
    exact isPrimeI439N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 439 (by decide) (𝕀 ⊙ MulI439N0)


lemma PB441I9_primes (p : ℕ) :
  p ∈ Set.range ![421, 431, 433, 439] ↔ Nat.Prime p ∧ 419 < p ∧ p ≤ 440 := by
  rw [← List.mem_ofFn']
  convert primes_range 419 440 (by omega)

def PB441I9 : PrimesBelowBoundCertificateInterval O 419 440 441 where
  m := 4
  g := ![3, 2, 1, 2]
  P := ![421, 431, 433, 439]
  hP := PB441I9_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I421N0, I421N1, I421N2]
    · exact ![I431N0, I431N1]
    · exact ![I433N0]
    · exact ![I439N0, I439N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC421
    · exact PBC431
    · exact PBC433
    · exact PBC439
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![177241, 177241, 421]
    · exact ![34507149121, 431]
    · exact ![15220870177393]
    · exact ![37141383841, 439]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI421N0
      exact NI421N1
      exact NI421N2
    · dsimp ; intro j
      fin_cases j
      exact NI431N0
      exact NI431N1
    · dsimp ; intro j
      fin_cases j
      exact NI433N0
    · dsimp ; intro j
      fin_cases j
      exact NI439N0
      exact NI439N1
  β := ![I421N2, I431N1, I439N1]
  Il := ![[I421N2], [I431N1], [], [I439N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
