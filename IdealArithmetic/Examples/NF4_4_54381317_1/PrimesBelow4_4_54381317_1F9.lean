
import IdealArithmetic.Examples.NF4_4_54381317_1.RI4_4_54381317_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic

set_option linter.all false

open Classical Polynomial

noncomputable section 
instance hp467 : Fact (Nat.Prime 467) := {out := by norm_num}
def I467N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![467, 0, 0, 0], ![-226, -67, -4, 1]] i)))

def SI467N0: IdealEqSpanCertificate timesTableO I467N0
 ![![467, 0, 0, 0], ![-226, -67, -4, 1]] 
 ![![467, 0, 0, 0], ![0, 467, 0, 0], ![172, 372, 1, 0], ![462, 20, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![467, 0, 0, 0], ![0, 467, 0, 0], ![0, 0, 467, 0], ![0, 0, 0, 467]], ![![-226, -67, -4, 1], ![383, 106, 13, -3], ![-1149, -613, -134, 10], ![3830, 2171, 187, -124]]]
  hmulB := by decide
  f := ![![![20950293, 5693754, 797280, -182182], ![-10962358, -32013784, 0, 0]], ![![-100086, -27196, -3812, 871], ![52771, 153176, 0, 0]], ![![7636366, 2075371, 290607, -66405], ![-3995649, -11668928, 0, 0]], ![![20721668, 5631619, 788580, -180194], ![-10842793, -31664464, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-172, -372, 467, 0], ![-462, -20, 0, 467]], ![![0, 3, -4, 1], ![-1, -10, 13, -3], ![37, 105, -134, 10], ![62, -139, 187, -124]]]
  hle1 := by decide
  hle2 := by decide

lemma NI467N0 : Nat.card (O ⧸ I467N0) = 218089 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI467N0)

def MemCI467N0 : IdealMemCertificate B I467N0
  ![![467, 0, 0, 0], ![0, 467, 0, 0], ![172, 372, 1, 0], ![462, 20, 0, 1]] ![33024, 29353, 7912, 312] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI467N0
 g := ![-3152, -6253, 7912, 312]
 hmem := by decide

def P467P0 : CertificateIrreducibleZModOfList' 467 2 2 8 [86, 348, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [119, 466], [0, 1]]
 g := ![![[319, 112], [309, 410], [361], [88], [179, 208], [30], [346, 22], [119, 1]],![[104, 355], [64, 57], [361], [88], [180, 259], [30], [162, 445], [238, 466]]]
 h' := ![![[119, 466], [45, 255], [132, 133], [193, 448], [17, 337], [367, 312], [132, 253], [40, 65], [0, 1]],![[0, 1], [35, 212], [81, 334], [267, 19], [425, 130], [135, 155], [351, 214], [303, 402], [119, 466]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [317]]
 b := ![[], [26, 392]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI467N0 : CertifiedPrimeIdeal O 467 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I467N0
  hcard := NI467N0
  P := [86, 348, 1]
  f := ofList [86, 348, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P467P0
  hneq := by decide
  hlen := by decide
  c := ![33024, 29353, 7912, 312]
  a := ![0, -1, -1, -1]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI467N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI467N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI467N0 : Ideal.IsPrime I467N0 := CertifiedPrimeIdeal.isPrime PI467N0
def I467N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![467, 0, 0, 0], ![144, 1, 0, 0]] i)))

def SI467N1: IdealEqSpanCertificate timesTableO I467N1
 ![![467, 0, 0, 0], ![144, 1, 0, 0]] 
 ![![467, 0, 0, 0], ![144, 1, 0, 0], ![279, 0, 1, 0], ![453, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![467, 0, 0, 0], ![0, 467, 0, 0], ![0, 0, 467, 0], ![0, 0, 0, 467]], ![![144, 1, 0, 0], ![0, 144, 1, 0], ![0, 0, 144, 1], ![383, 332, 80, 145]]]
  hmulB := by decide
  f := ![![![14689, -762, 1330554, 9240], ![-47634, 2802, -4315080, 0]], ![![4464, -257, 414718, 2880], ![-14476, 934, -1344960, 0]], ![![8685, -516, 794876, 5520], ![-28164, 1869, -2577840, 0]], ![![14055, -722, 1290666, 8963], ![-45578, 2658, -4185720, 0]]]
  g := ![![![1, 0, 0, 0], ![-144, 467, 0, 0], ![-279, 0, 467, 0], ![-453, 0, 0, 467]], ![![0, 1, 0, 0], ![-45, 144, 1, 0], ![-87, 0, 144, 1], ![-290, 332, 80, 145]]]
  hle1 := by decide
  hle2 := by decide

lemma NI467N1 : Nat.card (O ⧸ I467N1) = 467 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI467N1)

lemma isPrimeI467N1 : Ideal.IsPrime I467N1 := prime_ideal_of_norm_prime hp467.out _ NI467N1
def I467N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![467, 0, 0, 0], ![-50, 1, 0, 0]] i)))

def SI467N2: IdealEqSpanCertificate timesTableO I467N2
 ![![467, 0, 0, 0], ![-50, 1, 0, 0]] 
 ![![467, 0, 0, 0], ![417, 1, 0, 0], ![302, 0, 1, 0], ![156, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![467, 0, 0, 0], ![0, 467, 0, 0], ![0, 0, 467, 0], ![0, 0, 0, 467]], ![![-50, 1, 0, 0], ![0, -50, 1, 0], ![0, 0, -50, 1], ![383, 332, 80, -49]]]
  hmulB := by decide
  f := ![![![44351, -613987, 12412, -3], ![414229, -5726354, 1401, 0]], ![![39651, -548143, 11097, -3], ![370332, -5112249, 1401, 0]], ![![28706, -397024, 8029, -2], ![268108, -3702842, 934, 0]], ![![14868, -205092, 4146, -1], ![138864, -1912782, 468, 0]]]
  g := ![![![1, 0, 0, 0], ![-417, 467, 0, 0], ![-302, 0, 467, 0], ![-156, 0, 0, 467]], ![![-1, 1, 0, 0], ![44, -50, 1, 0], ![32, 0, -50, 1], ![-331, 332, 80, -49]]]
  hle1 := by decide
  hle2 := by decide

lemma NI467N2 : Nat.card (O ⧸ I467N2) = 467 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI467N2)

lemma isPrimeI467N2 : Ideal.IsPrime I467N2 := prime_ideal_of_norm_prime hp467.out _ NI467N2
def MulI467N0 : IdealMulEqCertificate timesTableO (I467N0) I467N1
  ![![467, 0, 0, 0], ![-226, -67, -4, 1]] ![![467, 0, 0, 0], ![144, 1, 0, 0]]
  ![![467, 0, 0, 0], ![-18618, -9542, -563, 141]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![218089, 0, 0, 0], ![67248, 467, 0, 0]], ![![-105542, -31289, -1868, 467], ![-32161, -9542, -563, 141]]]
 hmul := by decide
 f :=  ![![![![708263012927778438, -50743084411635130, 93163770285332383564, 646973094115155321], ![-2296780958269062348, 180558561874967711, -302136533929859515080, 0]], ![![98978081964240, 0, 0, 0], ![52771, 0, 0, 0]]], ![![![-28236492561601691412, 2022986799238606138, -3714182526344630565984, -25793032568540781105], ![91566321070059670812, -7198371785984945947, 12045350155491639448440, 0]], ![![-3945983094037200, 0, 0, 0], ![-2103834, 0, 0, 0]]]]
 g :=  ![![![![467, 0, 0, 0], ![0, 0, 0, 0]], ![![144, 1, 0, 0], ![0, 0, 0, 0]]], ![![![18392, 9475, 559, -140], ![467, 0, 0, 0]], ![![18589, 9542, 563, -141], ![468, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI467N1 : IdealMulEqCertificate timesTableO (I467N0*I467N1) I467N2
  ![![467, 0, 0, 0], ![-18618, -9542, -563, 141]] ![![467, 0, 0, 0], ![-50, 1, 0, 0]]
  ![![467, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI467N0
 hI2 := rfl
 M :=  ![![![218089, 0, 0, 0], ![-23350, 467, 0, 0]], ![![-8694606, -4456114, -262921, 65847], ![984903, 505294, 29888, -7472]]]
 hmul := by decide
 f :=  ![![![![574038880429133, -7806820059003986, 157678488223841, -35434228109], ![5361522899612052, -72808469017951562, 16547692285408, 0]], ![![654195, 0, 0, 0], ![0, 0, 0, 0]]]]
 g :=  ![![![![467, 0, 0, 0]], ![![-50, 1, 0, 0]]], ![![![-18618, -9542, -563, 141]], ![![2109, 1082, 64, -16]]]]
 hle1 := by decide
 hle2 := by decide

def PBC467 : IsPrimesAboveP 467 ![I467N0, I467N1, I467N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI467N0
    exact isPrimeI467N1
    exact isPrimeI467N2
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI467N1, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp479 : Fact (Nat.Prime 479) := {out := by norm_num}
def I479N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![479, 0, 0, 0]] i)))

def SI479N0: IdealEqSpanCertificate timesTableO I479N0
 ![![479, 0, 0, 0]] 
 ![![479, 0, 0, 0], ![0, 479, 0, 0], ![0, 0, 479, 0], ![0, 0, 0, 479]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![479, 0, 0, 0], ![0, 479, 0, 0], ![0, 0, 479, 0], ![0, 0, 0, 479]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0]], ![![0, 1, 0, 0]], ![![0, 0, 1, 0]], ![![0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI479N0 : Nat.card (O ⧸ I479N0) = 52643172481 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI479N0)

def MemCI479N0 : IdealMemCertificate B I479N0
  ![![479, 0, 0, 0], ![0, 479, 0, 0], ![0, 0, 479, 0], ![0, 0, 0, 479]] ![23909483518197, 21462717294126, 5978921123412, 494872717842] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI479N0
 g := ![49915414443, 44807342994, 12482090028, 1033137198]
 hmem := by decide

def P479P0 : CertificateIrreducibleZModOfList' 479 4 2 8 [398, 408, 231, 450, 1] where
 m := 1
 P := ![2]
 exp := ![2] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [311, 171, 239, 121], [94, 307, 31, 72], [103, 0, 209, 286], [0, 1]]
 g := ![![[335, 444, 378, 61], [244, 166, 118, 414], [276, 233, 310, 428], [187, 3, 74, 150], [56, 107, 445, 50], [247, 381, 64], [45, 131, 29, 1], []],![[55, 243, 206, 420, 235, 240], [164, 384, 37, 176, 394, 375], [108, 152, 456, 270, 246, 366], [263, 77, 387, 364, 394, 121], [155, 120, 278, 126, 213, 80], [302, 52, 70], [16, 397, 113, 222, 416, 225], [32, 270, 62, 459, 436, 219]],![[183, 367, 97, 409, 437, 21], [457, 95, 248, 131, 89, 366], [378, 247, 414, 160, 85, 321], [82, 276, 1, 45, 430, 168], [197, 67, 37, 48, 122, 396], [11, 352, 167], [289, 43, 1, 237, 241, 326], [453, 289, 55, 283, 467, 107]],![[29, 155, 324, 439, 149, 26], [319, 249, 323, 14, 246, 281], [243, 33, 75, 444, 258, 465], [245, 48, 336, 266, 453, 434], [386, 200, 354, 243, 322, 87], [80, 297, 213], [81, 124, 320, 464, 415, 254], [267, 409, 157, 355, 222, 254]]]
 h' := ![![[311, 171, 239, 121], [125, 334, 153, 260], [322, 338, 403, 53], [298, 438, 12, 334], [225, 95, 171, 234], [370, 195, 176, 23], [292, 394, 297, 8], [0, 0, 0, 1], [0, 1]],![[94, 307, 31, 72], [430, 146, 64, 231], [124, 475, 258, 310], [393, 6, 251, 26], [249, 134, 192, 478], [216, 376, 16, 8], [396, 8, 202, 301], [186, 371, 259, 132], [311, 171, 239, 121]],![[103, 0, 209, 286], [342, 385, 64, 244], [89, 112, 423, 413], [226, 54, 361, 316], [50, 173, 223, 233], [246, 176, 373, 325], [68, 360, 261, 330], [287, 233, 53, 153], [94, 307, 31, 72]],![[0, 1], [361, 93, 198, 223], [176, 33, 353, 182], [412, 460, 334, 282], [292, 77, 372, 13], [350, 211, 393, 123], [455, 196, 198, 319], [200, 354, 167, 193], [103, 0, 209, 286]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [341, 96, 187], []]
 b := ![[], [], [355, 321, 63, 350], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI479N0 : CertifiedPrimeIdeal O 479 where 
  r := 4
  n := 4
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I479N0
  hcard := NI479N0
  P := [398, 408, 231, 450, 1]
  f := ofList [398, 408, 231, 450, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P479P0
  hneq := by decide
  hlen := by decide
  c := ![23909483518197, 21462717294126, 5978921123412, 494872717842]
  a := ![-2, 3, -64, 1]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI479N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI479N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI479N0 : Ideal.IsPrime I479N0 := CertifiedPrimeIdeal.isPrime PI479N0
def PBC479 : IsPrimesAboveP 479 ![I479N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI479N0
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    unfold I479N0
    rw [Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp487 : Fact (Nat.Prime 487) := {out := by norm_num}
def I487N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![487, 0, 0, 0]] i)))

def SI487N0: IdealEqSpanCertificate timesTableO I487N0
 ![![487, 0, 0, 0]] 
 ![![487, 0, 0, 0], ![0, 487, 0, 0], ![0, 0, 487, 0], ![0, 0, 0, 487]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![487, 0, 0, 0], ![0, 487, 0, 0], ![0, 0, 487, 0], ![0, 0, 0, 487]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0]], ![![0, 1, 0, 0]], ![![0, 0, 1, 0]], ![![0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI487N0 : Nat.card (O ⧸ I487N0) = 56249134561 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI487N0)

def MemCI487N0 : IdealMemCertificate B I487N0
  ![![487, 0, 0, 0], ![0, 487, 0, 0], ![0, 0, 487, 0], ![0, 0, 0, 487]] ![2841248632161, 2711871744154, 832896923888, 81758963047] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI487N0
 g := ![5834186103, 5568525142, 1710260624, 167882881]
 hmem := by decide

def P487P0 : CertificateIrreducibleZModOfList' 487 4 2 8 [474, 269, 445, 144, 1] where
 m := 1
 P := ![2]
 exp := ![2] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [431, 60, 206, 349], [34, 397, 411, 279], [365, 29, 357, 346], [0, 1]]
 g := ![![[183, 351, 255, 342], [44, 324, 124, 21], [339, 109, 284, 16], [476, 184, 129], [451, 471, 120], [309, 97, 114, 64], [110, 324, 343, 1], []],![[271, 424, 315, 445, 224, 360], [108, 205, 59, 478, 363, 483], [386, 247, 230, 466, 336, 335], [104, 182, 214], [13, 43, 196], [83, 152, 142, 47, 368, 456], [213, 31, 11, 111, 206, 458], [76, 427, 364, 18, 375, 267]],![[301, 117, 340, 160, 23, 97], [387, 159, 46, 43, 255, 72], [457, 17, 471, 443, 258, 439], [30, 453, 142], [205, 293, 334], [78, 251, 102, 203, 155, 382], [420, 96, 130, 109, 440, 351], [57, 17, 448, 83, 118, 361]],![[415, 103, 357, 218, 434, 446], [361, 41, 115, 280, 486, 26], [419, 265, 0, 406, 365, 94], [435, 376, 382], [48, 415, 144], [159, 391, 202, 49, 3, 371], [482, 404, 146, 214, 430, 228], [26, 181, 387, 297, 175, 438]]]
 h' := ![![[431, 60, 206, 349], [85, 257, 211, 130], [24, 74, 193, 316], [409, 163, 80, 4], [50, 65, 305, 398], [121, 430, 481, 347], [456, 433, 330, 479], [0, 0, 0, 1], [0, 1]],![[34, 397, 411, 279], [404, 458, 236, 318], [354, 410, 83, 409], [361, 377, 317, 29], [38, 233, 45, 431], [48, 170, 366, 14], [118, 97, 69, 336], [205, 251, 43, 363], [431, 60, 206, 349]],![[365, 29, 357, 346], [29, 114, 166, 261], [46, 87, 136, 405], [27, 331, 19, 472], [245, 188, 212, 248], [263, 472, 240, 114], [197, 271, 304, 154], [111, 32, 383, 227], [34, 397, 411, 279]],![[0, 1], [249, 145, 361, 265], [198, 403, 75, 331], [223, 103, 71, 469], [110, 1, 412, 384], [66, 389, 374, 12], [253, 173, 271, 5], [26, 204, 61, 383], [365, 29, 357, 346]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [94, 430, 188], []]
 b := ![[], [], [480, 333, 426, 29], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI487N0 : CertifiedPrimeIdeal O 487 where 
  r := 4
  n := 4
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I487N0
  hcard := NI487N0
  P := [474, 269, 445, 144, 1]
  f := ofList [474, 269, 445, 144, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P487P0
  hneq := by decide
  hlen := by decide
  c := ![2841248632161, 2711871744154, 832896923888, 81758963047]
  a := ![-1, 1, 1, -3]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI487N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI487N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI487N0 : Ideal.IsPrime I487N0 := CertifiedPrimeIdeal.isPrime PI487N0
def PBC487 : IsPrimesAboveP 487 ![I487N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI487N0
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    unfold I487N0
    rw [Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp491 : Fact (Nat.Prime 491) := {out := by norm_num}
def I491N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![491, 0, 0, 0], ![-232, 1, 0, 0]] i)))

def SI491N0: IdealEqSpanCertificate timesTableO I491N0
 ![![491, 0, 0, 0], ![-232, 1, 0, 0]] 
 ![![491, 0, 0, 0], ![259, 1, 0, 0], ![186, 0, 1, 0], ![435, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![491, 0, 0, 0], ![0, 491, 0, 0], ![0, 0, 491, 0], ![0, 0, 0, 491]], ![![-232, 1, 0, 0], ![0, -232, 1, 0], ![0, 0, -232, 1], ![383, 332, 80, -231]]]
  hmulB := by decide
  f := ![![![106257, 4414, 6124779, -26400], ![224878, 10311, 12962400, 0]], ![![56377, 2309, 3247989, -14000], ![119314, 5401, 6874000, 0]], ![![40478, 1682, 2319992, -10000], ![85666, 3929, 4910000, 0]], ![![94105, 3880, 5426230, -23389], ![199160, 9070, 11484000, 0]]]
  g := ![![![1, 0, 0, 0], ![-259, 491, 0, 0], ![-186, 0, 491, 0], ![-435, 0, 0, 491]], ![![-1, 1, 0, 0], ![122, -232, 1, 0], ![87, 0, -232, 1], ![0, 332, 80, -231]]]
  hle1 := by decide
  hle2 := by decide

lemma NI491N0 : Nat.card (O ⧸ I491N0) = 491 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI491N0)

lemma isPrimeI491N0 : Ideal.IsPrime I491N0 := prime_ideal_of_norm_prime hp491.out _ NI491N0
def I491N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![491, 0, 0, 0], ![-116, 1, 0, 0]] i)))

def SI491N1: IdealEqSpanCertificate timesTableO I491N1
 ![![491, 0, 0, 0], ![-116, 1, 0, 0]] 
 ![![491, 0, 0, 0], ![375, 1, 0, 0], ![292, 0, 1, 0], ![484, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![491, 0, 0, 0], ![0, 491, 0, 0], ![0, 0, 491, 0], ![0, 0, 0, 491]], ![![-116, 1, 0, 0], ![0, -116, 1, 0], ![0, 0, -116, 1], ![383, 332, 80, -115]]]
  hmulB := by decide
  f := ![![![80737, -6515488, 59178, -26], ![341736, -27575542, 12766, 0]], ![![61713, -4976120, 45213, -20], ![261213, -21060463, 9820, 0]], ![![48284, -3874700, 35255, -16], ![204372, -16398908, 7856, 0]], ![![79508, -6422650, 58378, -26], ![336534, -27182626, 12767, 0]]]
  g := ![![![1, 0, 0, 0], ![-375, 491, 0, 0], ![-292, 0, 491, 0], ![-484, 0, 0, 491]], ![![-1, 1, 0, 0], ![88, -116, 1, 0], ![68, 0, -116, 1], ![-187, 332, 80, -115]]]
  hle1 := by decide
  hle2 := by decide

lemma NI491N1 : Nat.card (O ⧸ I491N1) = 491 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI491N1)

lemma isPrimeI491N1 : Ideal.IsPrime I491N1 := prime_ideal_of_norm_prime hp491.out _ NI491N1
def I491N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![491, 0, 0, 0], ![-114, 1, 0, 0]] i)))

def SI491N2: IdealEqSpanCertificate timesTableO I491N2
 ![![491, 0, 0, 0], ![-114, 1, 0, 0]] 
 ![![491, 0, 0, 0], ![377, 1, 0, 0], ![261, 0, 1, 0], ![294, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![491, 0, 0, 0], ![0, 491, 0, 0], ![0, 0, 491, 0], ![0, 0, 0, 491]], ![![-114, 1, 0, 0], ![0, -114, 1, 0], ![0, 0, -114, 1], ![383, 332, 80, -113]]]
  hmulB := by decide
  f := ![![![8893, 834, 1921576, -16856], ![38298, 3928, 8276296, 0]], ![![6955, 623, 1481082, -12992], ![29952, 2946, 6379072, 0]], ![![4815, 528, 1021435, -8960], ![20736, 2456, 4399360, 0]], ![![5526, 548, 1150597, -10093], ![23798, 2569, 4955664, 0]]]
  g := ![![![1, 0, 0, 0], ![-377, 491, 0, 0], ![-261, 0, 491, 0], ![-294, 0, 0, 491]], ![![-1, 1, 0, 0], ![87, -114, 1, 0], ![60, 0, -114, 1], ![-229, 332, 80, -113]]]
  hle1 := by decide
  hle2 := by decide

lemma NI491N2 : Nat.card (O ⧸ I491N2) = 491 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI491N2)

lemma isPrimeI491N2 : Ideal.IsPrime I491N2 := prime_ideal_of_norm_prime hp491.out _ NI491N2
def I491N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![491, 0, 0, 0], ![-30, 1, 0, 0]] i)))

def SI491N3: IdealEqSpanCertificate timesTableO I491N3
 ![![491, 0, 0, 0], ![-30, 1, 0, 0]] 
 ![![491, 0, 0, 0], ![461, 1, 0, 0], ![82, 0, 1, 0], ![5, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![491, 0, 0, 0], ![0, 491, 0, 0], ![0, 0, 491, 0], ![0, 0, 0, 491]], ![![-30, 1, 0, 0], ![0, -30, 1, 0], ![0, 0, -30, 1], ![383, 332, 80, -29]]]
  hmulB := by decide
  f := ![![![9751, -295, 55979, -1866], ![159575, 491, 916206, 0]], ![![9181, -276, 55979, -1866], ![150247, 491, 916206, 0]], ![![1682, -26, 9329, -311], ![27526, 492, 152701, 0]], ![![145, -3, 570, -19], ![2373, 30, 9330, 0]]]
  g := ![![![1, 0, 0, 0], ![-461, 491, 0, 0], ![-82, 0, 491, 0], ![-5, 0, 0, 491]], ![![-1, 1, 0, 0], ![28, -30, 1, 0], ![5, 0, -30, 1], ![-324, 332, 80, -29]]]
  hle1 := by decide
  hle2 := by decide

lemma NI491N3 : Nat.card (O ⧸ I491N3) = 491 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI491N3)

lemma isPrimeI491N3 : Ideal.IsPrime I491N3 := prime_ideal_of_norm_prime hp491.out _ NI491N3
def MulI491N0 : IdealMulEqCertificate timesTableO (I491N0) I491N1
  ![![491, 0, 0, 0], ![-232, 1, 0, 0]] ![![491, 0, 0, 0], ![-116, 1, 0, 0]]
  ![![491, 0, 0, 0], ![-77, -1, -4, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![241081, 0, 0, 0], ![-56956, 491, 0, 0]], ![![-113912, 491, 0, 0], ![26912, -348, 1, 0]]]
 hmul := by decide
 f :=  ![![![![-1497966947056716511545, 121088335675516882278541, -1099003605934604933358, 476292815172326564], ![-6340532407766120555797, 512483036932935998860078, -233859772249612378960, 0]], ![![-50448180285554, 0, 0, 0], ![-64812, 17693676, 0, 0]]], ![![![234904201097315409891, -18988508932022441269968, 172340627783800260016, -74690021336105302], ![994292766408780738640, -80365203386626715398196, 36672800476027708933, 0]], ![![7911048711773, 0, 0, 0], ![10164, -2774640, 0, 0]]]]
 g :=  ![![![![22762678671, 15528021620, 4783280000, -175355060], ![-3640656980, -29913330480, 0, 0]], ![![-5377846070, -3668606513, -1130084214, 41428890], ![860131836, 7067238942, 0, 0]]], ![![![-10755586906, -7337141153, -2260146294, 82856970], ![1720245996, 14134339422, 0, 0]], ![![2541084602, 1733452238, 533975779, -19575554], ![-406420274, -3339339096, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI491N1 : IdealMulEqCertificate timesTableO (I491N0*I491N1) I491N2
  ![![491, 0, 0, 0], ![-77, -1, -4, 1]] ![![491, 0, 0, 0], ![-114, 1, 0, 0]]
  ![![491, 0, 0, 0], ![15453, 8118, 477, -119]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI491N0
 hI2 := rfl
 M :=  ![![![241081, 0, 0, 0], ![-55974, 491, 0, 0]], ![![-37807, -491, -1964, 491], ![9161, 369, 535, -117]]]
 hmul := by decide
 f :=  ![![![![23308761447679453, 2094076284464608, 5139498582213025957, -45083530662049698], ![100379935128473260, 9899602167404931, 22135996811349977640, 0]], ![![16743716419632, 0, 0, 0], ![-18658, 0, 0, 0]]], ![![![733586925140731495, 65905989298434594, 161753294792340208649, -1418895152670317837], ![3159215821999581442, 311566049118673338, 696676992993124152800, 0]], ![![526968001765240, 0, 0, 0], ![-587214, 0, 0, 0]]]]
 g :=  ![![![![-14962, -8118, -477, 119], ![491, 0, 0, 0]], ![![-114, 1, 0, 0], ![0, 0, 0, 0]]], ![![![-77, -1, -4, 1], ![0, 0, 0, 0]], ![![-2090, -1107, -64, 16], ![67, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI491N2 : IdealMulEqCertificate timesTableO (I491N0*I491N1*I491N2) I491N3
  ![![491, 0, 0, 0], ![15453, 8118, 477, -119]] ![![491, 0, 0, 0], ![-30, 1, 0, 0]]
  ![![491, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI491N1
 hI2 := rfl
 M :=  ![![![241081, 0, 0, 0], ![-14730, 491, 0, 0]], ![![7587423, 3985938, 234207, -58429], ![-509167, -267595, -15712, 3928]]]
 hmul := by decide
 f :=  ![![![![22493661276826634, -484056922107352, 2164923383724962277, -72164408066404566], ![368146207460864990, 4349116336360740, 35432724349337676567, 0]], ![![-94680381, 0, 0, 0], ![0, 0, 0, 0]]]]
 g :=  ![![![![491, 0, 0, 0]], ![![-30, 1, 0, 0]]], ![![![15453, 8118, 477, -119]], ![![-1037, -545, -32, 8]]]]
 hle1 := by decide
 hle2 := by decide

def PBC491 : IsPrimesAboveP 491 ![I491N0, I491N1, I491N2, I491N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI491N0
    exact isPrimeI491N1
    exact isPrimeI491N2
    exact isPrimeI491N3
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI491N2, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp499 : Fact (Nat.Prime 499) := {out := by norm_num}
def I499N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1010, 523, 34, -8]] i)))

def SI499N0: IdealEqSpanCertificate timesTableO I499N0
 ![![1010, 523, 34, -8]] 
 ![![499, 0, 0, 0], ![0, 499, 0, 0], ![427, 318, 1, 0], ![441, 101, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![1010, 523, 34, -8], ![-3064, -1646, -117, 26], ![9958, 5568, 434, -91], ![-34853, -20254, -1712, 343]]]
  hmulB := by decide
  f := ![![![170, 90, 7, -1]], ![![-383, -162, 10, 6]], ![![-94, -23, 13, 3]], ![![85, 62, 14, 1]]]
  g := ![![![-20, -19, 34, -8], ![71, 66, -117, 26], ![-271, -247, 434, -91], ![1092, 981, -1712, 343]]]
  hle1 := by decide
  hle2 := by decide

lemma NI499N0 : Nat.card (O ⧸ I499N0) = 249001 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI499N0)

def MemCI499N0 : IdealMemCertificate B I499N0
  ![![499, 0, 0, 0], ![0, 499, 0, 0], ![427, 318, 1, 0], ![441, 101, 0, 1]] ![30165, 25160, 5939, 685] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI499N0
 g := ![-5627, -3873, 5939, 685]
 hmem := by decide

def P499P0 : CertificateIrreducibleZModOfList' 499 2 2 8 [291, 353, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [146, 498], [0, 1]]
 g := ![![[255, 487], [424, 209], [387], [116], [478, 39], [369, 436], [174, 497], [146, 1]],![[0, 12], [0, 290], [387], [116], [184, 460], [153, 63], [381, 2], [292, 498]]]
 h' := ![![[146, 498], [368, 59], [107, 447], [335, 285], [123, 409], [405, 187], [264, 89], [428, 67], [0, 1]],![[0, 1], [0, 440], [0, 52], [29, 214], [456, 90], [262, 312], [284, 410], [230, 432], [146, 498]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [447]]
 b := ![[], [401, 473]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI499N0 : CertifiedPrimeIdeal O 499 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I499N0
  hcard := NI499N0
  P := [291, 353, 1]
  f := ofList [291, 353, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P499P0
  hneq := by decide
  hlen := by decide
  c := ![30165, 25160, 5939, 685]
  a := ![0, -1, -1, 1]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI499N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI499N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI499N0 : Ideal.IsPrime I499N0 := CertifiedPrimeIdeal.isPrime PI499N0
def I499N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![170, 90, 7, -1]] i)))

def SI499N1: IdealEqSpanCertificate timesTableO I499N1
 ![![170, 90, 7, -1]] 
 ![![499, 0, 0, 0], ![0, 499, 0, 0], ![137, 180, 1, 0], ![290, 172, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![170, 90, 7, -1], ![-383, -162, 10, 6], ![2298, 1609, 318, 16], ![6128, 7610, 2889, 334]]]
  hmulB := by decide
  f := ![![![1010, 523, 34, -8]], ![![-3064, -1646, -117, 26]], ![![-808, -439, -32, 7]], ![![-539, -304, -24, 5]]]
  g := ![![![-1, -2, 7, -1], ![-7, -6, 10, 6], ![-92, -117, 318, 16], ![-975, -1142, 2889, 334]]]
  hle1 := by decide
  hle2 := by decide

lemma NI499N1 : Nat.card (O ⧸ I499N1) = 249001 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI499N1)

def MemCI499N1 : IdealMemCertificate B I499N1
  ![![499, 0, 0, 0], ![0, 499, 0, 0], ![137, 180, 1, 0], ![290, 172, 0, 1]] ![280613, 243557, 62796, 4100] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI499N1
 g := ![-19061, -23577, 62796, 4100]
 hmem := by decide

def P499P1 : CertificateIrreducibleZModOfList' 499 2 2 8 [472, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [489, 498], [0, 1]]
 g := ![![[129, 462], [492, 158], [26], [371], [125, 294], [5, 350], [169, 161], [489, 1]],![[0, 37], [409, 341], [26], [371], [179, 205], [497, 149], [56, 338], [479, 498]]]
 h' := ![![[489, 498], [310, 31], [324, 34], [488, 32], [381, 462], [135, 113], [72, 208], [229, 127], [0, 1]],![[0, 1], [0, 468], [483, 465], [168, 467], [252, 37], [3, 386], [487, 291], [456, 372], [489, 498]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [451]]
 b := ![[], [379, 475]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI499N1 : CertifiedPrimeIdeal O 499 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I499N1
  hcard := NI499N1
  P := [472, 10, 1]
  f := ofList [472, 10, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P499P1
  hneq := by decide
  hlen := by decide
  c := ![280613, 243557, 62796, 4100]
  a := ![19, 1, -1, 3]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI499N1
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI499N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI499N1 : Ideal.IsPrime I499N1 := CertifiedPrimeIdeal.isPrime PI499N1
def MulI499N0 : IdealMulEqCertificate timesTableO (I499N0) I499N1
  ![![1010, 523, 34, -8]] ![![170, 90, 7, -1]]
  ![![499, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![499, 0, 0, 0]]]
 hmul := by decide
 f :=  ![![![![1, 0, 0, 0]]]]
 g :=  ![![![![1, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def PBC499 : IsPrimesAboveP 499 ![I499N0, I499N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI499N0
    exact isPrimeI499N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI499N0, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp503 : Fact (Nat.Prime 503) := {out := by norm_num}
def I503N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-398, -201, -12, 3]] i)))

def SI503N0: IdealEqSpanCertificate timesTableO I503N0
 ![![-398, -201, -12, 3]] 
 ![![503, 0, 0, 0], ![0, 503, 0, 0], ![488, 166, 1, 0], ![478, 94, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![-398, -201, -12, 3], ![1149, 598, 39, -9], ![-3447, -1839, -122, 30], ![11490, 6513, 561, -92]]]
  hmulB := by decide
  f := ![![![-391, -201, -12, 3]], ![![1149, 605, 39, -9]], ![![-7, 1, 1, 0]], ![![-134, -65, -3, 1]]]
  g := ![![![8, 3, -12, 3], ![-27, -10, 39, -9], ![83, 31, -122, 30], ![-434, -155, 561, -92]]]
  hle1 := by decide
  hle2 := by decide

lemma NI503N0 : Nat.card (O ⧸ I503N0) = 253009 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI503N0)

def MemCI503N0 : IdealMemCertificate B I503N0
  ![![503, 0, 0, 0], ![0, 503, 0, 0], ![488, 166, 1, 0], ![478, 94, 0, 1]] ![125554, 112292, 30968, 3217] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI503N0
 g := ![-32852, -10598, 30968, 3217]
 hmem := by decide

def P503P0 : CertificateIrreducibleZModOfList' 503 2 2 8 [8, 462, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [41, 502], [0, 1]]
 g := ![![[435, 63], [349, 196], [68, 379], [468], [269, 184], [200, 346], [218, 237], [41, 1]],![[0, 440], [337, 307], [14, 124], [468], [268, 319], [302, 157], [378, 266], [82, 502]]]
 h' := ![![[41, 502], [226, 338], [462, 14], [263, 224], [363, 233], [412, 297], [268, 445], [175, 164], [0, 1]],![[0, 1], [0, 165], [30, 489], [393, 279], [359, 270], [14, 206], [405, 58], [360, 339], [41, 502]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [388]]
 b := ![[], [47, 194]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI503N0 : CertifiedPrimeIdeal O 503 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I503N0
  hcard := NI503N0
  P := [8, 462, 1]
  f := ofList [8, 462, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P503P0
  hneq := by decide
  hlen := by decide
  c := ![125554, 112292, 30968, 3217]
  a := ![-1, 0, 1, 2]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI503N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI503N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI503N0 : Ideal.IsPrime I503N0 := CertifiedPrimeIdeal.isPrime PI503N0
def I503N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 6, 1, 0]] i)))

def SI503N1: IdealEqSpanCertificate timesTableO I503N1
 ![![7, 6, 1, 0]] 
 ![![503, 0, 0, 0], ![160, 1, 0, 0], ![53, 0, 1, 0], ![71, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![7, 6, 1, 0], ![0, 7, 6, 1], ![383, 332, 87, 7], ![2681, 2707, 892, 94]]]
  hmulB := by decide
  f := ![![![619, 655, 81, -13]], ![![187, 201, 25, -4]], ![![117, 104, 12, -2]], ![![-154, -65, -4, 1]]]
  g := ![![![-2, 6, 1, 0], ![-3, 7, 6, 1], ![-115, 332, 87, 7], ![-963, 2707, 892, 94]]]
  hle1 := by decide
  hle2 := by decide

lemma NI503N1 : Nat.card (O ⧸ I503N1) = 503 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI503N1)

lemma isPrimeI503N1 : Ideal.IsPrime I503N1 := prime_ideal_of_norm_prime hp503.out _ NI503N1
def I503N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-163, -76, -3, 1]] i)))

def SI503N2: IdealEqSpanCertificate timesTableO I503N2
 ![![-163, -76, -3, 1]] 
 ![![503, 0, 0, 0], ![176, 1, 0, 0], ![210, 0, 1, 0], ![262, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![-163, -76, -3, 1], ![383, 169, 4, -2], ![-766, -281, 9, 2], ![766, -102, -121, 11]]]
  hmulB := by decide
  f := ![![![-661, -342, -28, 3]], ![![-229, -119, -10, 1]], ![![-295, -157, -15, 1]], ![![-441, -281, -49, -2]]]
  g := ![![![27, -76, -3, 1], ![-59, 169, 4, -2], ![92, -281, 9, 2], ![82, -102, -121, 11]]]
  hle1 := by decide
  hle2 := by decide

lemma NI503N2 : Nat.card (O ⧸ I503N2) = 503 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI503N2)

lemma isPrimeI503N2 : Ideal.IsPrime I503N2 := prime_ideal_of_norm_prime hp503.out _ NI503N2
def MulI503N0 : IdealMulEqCertificate timesTableO (I503N0) I503N1
  ![![-398, -201, -12, 3]] ![![7, 6, 1, 0]]
  ![![661, 342, 28, -3]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![661, 342, 28, -3]]]
 hmul := by decide
 f :=  ![![![![1, 0, 0, 0]]]]
 g :=  ![![![![1, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI503N1 : IdealMulEqCertificate timesTableO (I503N0*I503N1) I503N2
  ![![661, 342, 28, -3]] ![![-163, -76, -3, 1]]
  ![![503, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI503N0
 hI2 := rfl
 M :=  ![![![-503, 0, 0, 0]]]
 hmul := by decide
 f :=  ![![![![-1, 0, 0, 0]]]]
 g :=  ![![![![-1, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def PBC503 : IsPrimesAboveP 503 ![I503N0, I503N1, I503N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI503N0
    exact isPrimeI503N1
    exact isPrimeI503N2
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI503N1, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp509 : Fact (Nat.Prime 509) := {out := by norm_num}
def I509N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-392, -201, -12, 3]] i)))

def SI509N0: IdealEqSpanCertificate timesTableO I509N0
 ![![-392, -201, -12, 3]] 
 ![![509, 0, 0, 0], ![0, 509, 0, 0], ![500, 170, 1, 0], ![3, 104, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![-392, -201, -12, 3], ![1149, 604, 39, -9], ![-3447, -1839, -116, 30], ![11490, 6513, 561, -86]]]
  hmulB := by decide
  f := ![![![-397, -201, -12, 3]], ![![1149, 599, 39, -9]], ![![-13, -1, 1, 0]], ![![255, 134, 9, -2]]]
  g := ![![![11, 3, -12, 3], ![-36, -10, 39, -9], ![107, 29, -116, 30], ![-528, -157, 561, -86]]]
  hle1 := by decide
  hle2 := by decide

lemma NI509N0 : Nat.card (O ⧸ I509N0) = 259081 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI509N0)

def MemCI509N0 : IdealMemCertificate B I509N0
  ![![509, 0, 0, 0], ![0, 509, 0, 0], ![500, 170, 1, 0], ![3, 104, 0, 1]] ![122703, 109100, 28780, 2536] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI509N0
 g := ![-28045, -9916, 28780, 2536]
 hmem := by decide

def P509P0 : CertificateIrreducibleZModOfList' 509 2 2 8 [46, 292, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [217, 508], [0, 1]]
 g := ![![[117, 133], [391], [283, 97], [185, 126], [164, 332], [423, 30], [99, 415], [217, 1]],![[474, 376], [391], [463, 412], [41, 383], [439, 177], [316, 479], [61, 94], [434, 508]]]
 h' := ![![[217, 508], [166, 79], [216, 30], [143, 383], [91, 178], [393, 29], [27, 368], [198, 215], [0, 1]],![[0, 1], [3, 430], [109, 479], [287, 126], [33, 331], [69, 480], [479, 141], [25, 294], [217, 508]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [373, 271]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI509N0 : CertifiedPrimeIdeal O 509 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I509N0
  hcard := NI509N0
  P := [46, 292, 1]
  f := ofList [46, 292, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P509P0
  hneq := by decide
  hlen := by decide
  c := ![122703, 109100, 28780, 2536]
  a := ![-5, 0, 0, 2]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI509N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI509N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI509N0 : Ideal.IsPrime I509N0 := CertifiedPrimeIdeal.isPrime PI509N0
def I509N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![509, 0, 0, 0], ![136, 1, 0, 0]] i)))

def SI509N1: IdealEqSpanCertificate timesTableO I509N1
 ![![509, 0, 0, 0], ![136, 1, 0, 0]] 
 ![![509, 0, 0, 0], ![136, 1, 0, 0], ![337, 0, 1, 0], ![487, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![509, 0, 0, 0], ![0, 509, 0, 0], ![0, 0, 509, 0], ![0, 0, 0, 509]], ![![136, 1, 0, 0], ![0, 136, 1, 0], ![0, 0, 136, 1], ![383, 332, 80, 137]]]
  hmulB := by decide
  f := ![![![31961, -2336381, -18405, -9], ![-119615, 8745129, 4581, 0]], ![![8296, -624315, -4999, -3], ![-31048, 2336819, 1527, 0]], ![![21253, -1546980, -12192, -6], ![-79540, 5790385, 3054, 0]], ![![30691, -2235442, -17663, -9], ![-114862, 8367315, 4582, 0]]]
  g := ![![![1, 0, 0, 0], ![-136, 509, 0, 0], ![-337, 0, 509, 0], ![-487, 0, 0, 509]], ![![0, 1, 0, 0], ![-37, 136, 1, 0], ![-91, 0, 136, 1], ![-272, 332, 80, 137]]]
  hle1 := by decide
  hle2 := by decide

lemma NI509N1 : Nat.card (O ⧸ I509N1) = 509 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI509N1)

lemma isPrimeI509N1 : Ideal.IsPrime I509N1 := prime_ideal_of_norm_prime hp509.out _ NI509N1
def I509N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![509, 0, 0, 0], ![202, 1, 0, 0]] i)))

def SI509N2: IdealEqSpanCertificate timesTableO I509N2
 ![![509, 0, 0, 0], ![202, 1, 0, 0]] 
 ![![509, 0, 0, 0], ![202, 1, 0, 0], ![425, 0, 1, 0], ![171, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![509, 0, 0, 0], ![0, 509, 0, 0], ![0, 0, 509, 0], ![0, 0, 0, 509]], ![![202, 1, 0, 0], ![0, 202, 1, 0], ![0, 0, 202, 1], ![383, 332, 80, 203]]]
  hmulB := by decide
  f := ![![![23635, -803641, -4585, -3], ![-59553, 2025311, 1527, 0]], ![![8888, -318914, -1983, -2], ![-22395, 803711, 1018, 0]], ![![19675, -670947, -3928, -3], ![-49575, 1690899, 1527, 0]], ![![7845, -269955, -1539, -1], ![-19767, 680331, 510, 0]]]
  g := ![![![1, 0, 0, 0], ![-202, 509, 0, 0], ![-425, 0, 509, 0], ![-171, 0, 0, 509]], ![![0, 1, 0, 0], ![-81, 202, 1, 0], ![-169, 0, 202, 1], ![-266, 332, 80, 203]]]
  hle1 := by decide
  hle2 := by decide

lemma NI509N2 : Nat.card (O ⧸ I509N2) = 509 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI509N2)

lemma isPrimeI509N2 : Ideal.IsPrime I509N2 := prime_ideal_of_norm_prime hp509.out _ NI509N2
def MulI509N0 : IdealMulEqCertificate timesTableO (I509N0) I509N1
  ![![-392, -201, -12, 3]] ![![509, 0, 0, 0], ![136, 1, 0, 0]]
  ![![509, 0, 0, 0], ![-17218, -9250, -531, 133]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![-199528, -102309, -6108, 1527], ![-52163, -26732, -1593, 399]]]
 hmul := by decide
 f :=  ![![![![-38542869057144967577, 78666279149081828403978, 578430607001474354838, -17856063], ![144252355515344033061, -294421178964986514718074, 9088736070, 0]]], ![![![1294990097883608154223, -2643084311766458093028485, -19434513483392466508896, 599940413], ![-4846690881049680518385, 9892167363088295728176594, -305369670210, 0]]]]
 g :=  ![![![![16826, 9049, 519, -130], ![509, 0, 0, 0]], ![![-1, 2, 0, 0], ![3, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI509N1 : IdealMulEqCertificate timesTableO (I509N0*I509N1) I509N2
  ![![509, 0, 0, 0], ![-17218, -9250, -531, 133]] ![![509, 0, 0, 0], ![202, 1, 0, 0]]
  ![![509, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI509N0
 hI2 := rfl
 M :=  ![![![259081, 0, 0, 0], ![102818, 509, 0, 0]], ![![-8763962, -4708250, -270279, 67697], ![-3427097, -1841562, -105872, 26468]]]
 hmul := by decide
 f :=  ![![![![26735478522335, -893688666410893, -5025139743835, -2980515960], ![-67365286622685, 2252253480544511, 1512674497176, 0]], ![![33143808, 0, 0, 0], ![0, 0, 0, 0]]]]
 g :=  ![![![![509, 0, 0, 0]], ![![202, 1, 0, 0]]], ![![![-17218, -9250, -531, 133]], ![![-6733, -3618, -208, 52]]]]
 hle1 := by decide
 hle2 := by decide

def PBC509 : IsPrimesAboveP 509 ![I509N0, I509N1, I509N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI509N0
    exact isPrimeI509N1
    exact isPrimeI509N2
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI509N1, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp521 : Fact (Nat.Prime 521) := {out := by norm_num}
def I521N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![521, 0, 0, 0], ![-244, 190, -4, 1]] i)))

def SI521N0: IdealEqSpanCertificate timesTableO I521N0
 ![![521, 0, 0, 0], ![-244, 190, -4, 1]] 
 ![![521, 0, 0, 0], ![0, 521, 0, 0], ![348, 362, 1, 0], ![106, 75, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![521, 0, 0, 0], ![0, 521, 0, 0], ![0, 0, 521, 0], ![0, 0, 0, 521]], ![![-244, 190, -4, 1], ![383, 88, 270, -3], ![-1149, -613, -152, 267], ![102261, 87495, 20747, 115]]]
  hmulB := by decide
  f := ![![![13001383, 5034258, 10563144, -109419], ![-4334199, -20447166, 0, 0]], ![![-30739, -11983, -25030, 259], ![10420, 48453, 0, 0]], ![![8662854, 3354298, 7038221, -72906], ![-2887800, -13623942, 0, 0]], ![![2640881, 1022433, 2145522, -22225], ![-880077, -4153101, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-348, -362, 521, 0], ![-106, -75, 0, 521]], ![![2, 3, -4, 1], ![-179, -187, 270, -3], ![45, 66, -152, 267], ![-13685, -14264, 20747, 115]]]
  hle1 := by decide
  hle2 := by decide

lemma NI521N0 : Nat.card (O ⧸ I521N0) = 271441 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI521N0)

def MemCI521N0 : IdealMemCertificate B I521N0
  ![![521, 0, 0, 0], ![0, 521, 0, 0], ![348, 362, 1, 0], ![106, 75, 0, 1]] ![81047, 64141, 14081, -1734] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI521N0
 g := ![-8897, -9411, 14081, -1734]
 hmem := by decide

def P521P0 : CertificateIrreducibleZModOfList' 521 2 2 9 [267, 358, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [163, 520], [0, 1]]
 g := ![![[15, 441], [327], [71], [484, 88], [84], [198], [71], [519], [1]],![[0, 80], [327], [71], [240, 433], [84], [198], [71], [519], [1]]]
 h' := ![![[163, 520], [224, 21], [199, 484], [501, 160], [135, 296], [224, 105], [214, 77], [446, 160], [254, 163], [0, 1]],![[0, 1], [0, 500], [420, 37], [10, 361], [451, 225], [146, 416], [261, 444], [476, 361], [252, 358], [163, 520]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [149]]
 b := ![[], [50, 335]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI521N0 : CertifiedPrimeIdeal O 521 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I521N0
  hcard := NI521N0
  P := [267, 358, 1]
  f := ofList [267, 358, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P521P0
  hneq := by decide
  hlen := by decide
  c := ![81047, 64141, 14081, -1734]
  a := ![-10, 2, 13, -1]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI521N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI521N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI521N0 : Ideal.IsPrime I521N0 := CertifiedPrimeIdeal.isPrime PI521N0
def I521N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![521, 0, 0, 0], ![-190, 140, -4, 1]] i)))

def SI521N1: IdealEqSpanCertificate timesTableO I521N1
 ![![521, 0, 0, 0], ![-190, 140, -4, 1]] 
 ![![521, 0, 0, 0], ![0, 521, 0, 0], ![207, 158, 1, 0], ![117, 251, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![521, 0, 0, 0], ![0, 521, 0, 0], ![0, 0, 521, 0], ![0, 0, 0, 521]], ![![-190, 140, -4, 1], ![383, 142, 220, -3], ![-1149, -613, -98, 217], ![83111, 70895, 16747, 119]]]
  hmulB := by decide
  f := ![![![10169075, 4770076, 6340756, -81973], ![-2475271, -15061068, 0, 0]], ![![-23188, -10911, -14476, 187], ![5731, 34386, 0, 0]], ![![4033231, 1891934, 2514873, -32512], ![-981832, -5973528, 0, 0]], ![![2272587, 1065871, 1416960, -18319], ![-552810, -3365670, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-207, -158, 521, 0], ![-117, -251, 0, 521]], ![![1, 1, -4, 1], ![-86, -65, 220, -3], ![-12, -76, -98, 217], ![-6521, -5000, 16747, 119]]]
  hle1 := by decide
  hle2 := by decide

lemma NI521N1 : Nat.card (O ⧸ I521N1) = 271441 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI521N1)

def MemCI521N1 : IdealMemCertificate B I521N1
  ![![521, 0, 0, 0], ![0, 521, 0, 0], ![207, 158, 1, 0], ![117, 251, 0, 1]] ![39850, 37881, 10660, 909] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI521N1
 g := ![-4363, -3598, 10660, 909]
 hmem := by decide

def P521P1 : CertificateIrreducibleZModOfList' 521 2 2 9 [164, 236, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [285, 520], [0, 1]]
 g := ![![[281, 2], [285], [355], [111, 124], [511], [468], [90], [470], [1]],![[330, 519], [285], [355], [23, 397], [511], [468], [90], [470], [1]]]
 h' := ![![[285, 520], [146, 272], [51, 90], [31, 462], [25, 327], [307, 135], [439, 301], [353, 353], [357, 285], [0, 1]],![[0, 1], [37, 249], [172, 431], [409, 59], [482, 194], [228, 386], [259, 220], [405, 168], [306, 236], [285, 520]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [465]]
 b := ![[], [343, 493]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI521N1 : CertifiedPrimeIdeal O 521 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I521N1
  hcard := NI521N1
  P := [164, 236, 1]
  f := ofList [164, 236, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P521P1
  hneq := by decide
  hlen := by decide
  c := ![39850, 37881, 10660, 909]
  a := ![1, 1, -4, -1]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI521N1
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI521N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI521N1 : Ideal.IsPrime I521N1 := CertifiedPrimeIdeal.isPrime PI521N1
def MulI521N0 : IdealMulEqCertificate timesTableO (I521N0) I521N1
  ![![521, 0, 0, 0], ![-244, 190, -4, 1]] ![![521, 0, 0, 0], ![-190, 140, -4, 1]]
  ![![521, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![271441, 0, 0, 0], ![-98990, 72940, -2084, 521]], ![![-127124, 98990, -2084, 521], ![206837, 66167, 59915, -1563]]]
 hmul := by decide
 f :=  ![![![![1259442684227109148601050, 590787466715103888770156, 785310520972956043311194, -10152407371860529237880], ![-306593587628214738020279, -1865332521461311262873568, 0, 0]], ![![263983616531687520, -50215845, 0, 0], ![0, 0, 0, 0]]]]
 g :=  ![![![![521, 0, 0, 0]], ![![-190, 140, -4, 1]]], ![![![-244, 190, -4, 1]], ![![397, 127, 115, -3]]]]
 hle1 := by decide
 hle2 := by decide

def PBC521 : IsPrimesAboveP 521 ![I521N0, I521N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI521N0
    exact isPrimeI521N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI521N0, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp523 : Fact (Nat.Prime 523) := {out := by norm_num}
def I523N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![523, 0, 0, 0]] i)))

def SI523N0: IdealEqSpanCertificate timesTableO I523N0
 ![![523, 0, 0, 0]] 
 ![![523, 0, 0, 0], ![0, 523, 0, 0], ![0, 0, 523, 0], ![0, 0, 0, 523]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![523, 0, 0, 0], ![0, 523, 0, 0], ![0, 0, 523, 0], ![0, 0, 0, 523]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0]], ![![0, 1, 0, 0]], ![![0, 0, 1, 0]], ![![0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI523N0 : Nat.card (O ⧸ I523N0) = 74818113841 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI523N0)

def MemCI523N0 : IdealMemCertificate B I523N0
  ![![523, 0, 0, 0], ![0, 523, 0, 0], ![0, 0, 523, 0], ![0, 0, 0, 523]] ![39648351241, 38186524401, 11887894077, 1192306112] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI523N0
 g := ![75809467, 73014387, 22730199, 2279744]
 hmem := by decide

def P523P0 : CertificateIrreducibleZModOfList' 523 4 2 9 [53, 34, 203, 504, 1] where
 m := 1
 P := ![2]
 exp := ![2] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [454, 493, 54, 414], [52, 286, 486, 73], [36, 266, 506, 36], [0, 1]]
 g := ![![[248, 379, 19, 323], [324, 357, 77, 509], [302, 440, 112], [119, 284, 411, 158], [177, 44, 240], [289, 170, 369], [74, 191, 361], [1], []],![[2, 131, 47, 116, 278, 322], [399, 32, 403, 78, 200, 222], [450, 154, 475], [269, 82, 7, 176, 466, 101], [18, 302, 451], [86, 158, 13], [188, 448, 462], [128, 458, 177], [369, 60, 375]],![[60, 25, 17, 233, 463, 454], [405, 394, 356, 219, 411, 428], [355, 488, 183], [229, 163, 107, 410, 480, 309], [280, 450, 221], [112, 57, 468], [111, 112, 301], [162, 170, 161], [61, 140, 99]],![[313, 290, 331, 442, 483, 230], [207, 264, 277, 504, 507, 195], [288, 108, 435], [349, 340, 17, 6, 342, 279], [333, 160, 451], [218, 293, 478], [46, 480, 169], [397, 223, 158], [121, 388, 250]]]
 h' := ![![[454, 493, 54, 414], [87, 114, 511, 37], [122, 411, 494, 472], [492, 253, 365, 482], [0, 362, 465, 108], [155, 460, 250, 401], [456, 379, 330, 328], [470, 489, 320, 19], [0, 0, 1], [0, 1]],![[52, 286, 486, 73], [250, 466, 223, 476], [341, 92, 39, 131], [260, 168, 188, 39], [183, 45, 300, 387], [406, 159, 410, 187], [439, 240, 409, 333], [107, 401, 113, 463], [371, 443, 180, 159], [454, 493, 54, 414]],![[36, 266, 506, 36], [273, 112, 43, 128], [196, 126, 142, 450], [62, 37, 332, 461], [67, 194, 287, 48], [273, 4, 133, 271], [45, 12, 323, 94], [341, 321, 166, 54], [517, 376, 120, 256], [52, 286, 486, 73]],![[0, 1], [54, 354, 269, 405], [279, 417, 371, 516], [199, 65, 161, 64], [297, 445, 517, 503], [393, 423, 253, 187], [502, 415, 507, 291], [96, 358, 447, 510], [113, 227, 222, 108], [36, 266, 506, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [138, 214, 476], []]
 b := ![[], [], [493, 17, 522, 452], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI523N0 : CertifiedPrimeIdeal O 523 where 
  r := 4
  n := 4
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I523N0
  hcard := NI523N0
  P := [53, 34, 203, 504, 1]
  f := ofList [53, 34, 203, 504, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P523P0
  hneq := by decide
  hlen := by decide
  c := ![39648351241, 38186524401, 11887894077, 1192306112]
  a := ![-3, 1, -1, 1]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI523N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI523N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI523N0 : Ideal.IsPrime I523N0 := CertifiedPrimeIdeal.isPrime PI523N0
def PBC523 : IsPrimesAboveP 523 ![I523N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI523N0
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    unfold I523N0
    rw [Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp541 : Fact (Nat.Prime 541) := {out := by norm_num}
def I541N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![541, 0, 0, 0], ![168, 1, 0, 0]] i)))

def SI541N0: IdealEqSpanCertificate timesTableO I541N0
 ![![541, 0, 0, 0], ![168, 1, 0, 0]] 
 ![![541, 0, 0, 0], ![168, 1, 0, 0], ![449, 0, 1, 0], ![308, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![541, 0, 0, 0], ![0, 541, 0, 0], ![0, 0, 541, 0], ![0, 0, 0, 541]], ![![168, 1, 0, 0], ![0, 168, 1, 0], ![0, 0, 168, 1], ![383, 332, 80, 169]]]
  hmulB := by decide
  f := ![![![25537, -2368, 4692225, 27930], ![-82232, 8115, -15110130, 0]], ![![7896, -793, 1468315, 8740], ![-25426, 2705, -4728340, 0]], ![![21221, -2058, 3894227, 23180], ![-68334, 7034, -12540380, 0]], ![![14420, -1374, 2671359, 15901], ![-46434, 4701, -8602440, 0]]]
  g := ![![![1, 0, 0, 0], ![-168, 541, 0, 0], ![-449, 0, 541, 0], ![-308, 0, 0, 541]], ![![0, 1, 0, 0], ![-53, 168, 1, 0], ![-140, 0, 168, 1], ![-265, 332, 80, 169]]]
  hle1 := by decide
  hle2 := by decide

lemma NI541N0 : Nat.card (O ⧸ I541N0) = 541 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI541N0)

lemma isPrimeI541N0 : Ideal.IsPrime I541N0 := prime_ideal_of_norm_prime hp541.out _ NI541N0
def I541N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![541, 0, 0, 0], ![203, 1, 0, 0]] i)))

def SI541N1: IdealEqSpanCertificate timesTableO I541N1
 ![![541, 0, 0, 0], ![203, 1, 0, 0]] 
 ![![541, 0, 0, 0], ![203, 1, 0, 0], ![448, 0, 1, 0], ![485, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![541, 0, 0, 0], ![0, 541, 0, 0], ![0, 0, 541, 0], ![0, 0, 0, 541]], ![![203, 1, 0, 0], ![0, 203, 1, 0], ![0, 0, 203, 1], ![383, 332, 80, 204]]]
  hmulB := by decide
  f := ![![![2640, -14197, -273, -1], ![-7033, 37870, 541, 0]], ![![609, -5275, -229, -1], ![-1622, 14066, 541, 0]], ![![2310, -11560, -260, -1], ![-6154, 30838, 541, 0]], ![![2808, -12699, -266, -1], ![-7481, 33880, 542, 0]]]
  g := ![![![1, 0, 0, 0], ![-203, 541, 0, 0], ![-448, 0, 541, 0], ![-485, 0, 0, 541]], ![![0, 1, 0, 0], ![-77, 203, 1, 0], ![-169, 0, 203, 1], ![-373, 332, 80, 204]]]
  hle1 := by decide
  hle2 := by decide

lemma NI541N1 : Nat.card (O ⧸ I541N1) = 541 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI541N1)

lemma isPrimeI541N1 : Ideal.IsPrime I541N1 := prime_ideal_of_norm_prime hp541.out _ NI541N1
def I541N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![541, 0, 0, 0], ![-190, 1, 0, 0]] i)))

def SI541N2: IdealEqSpanCertificate timesTableO I541N2
 ![![541, 0, 0, 0], ![-190, 1, 0, 0]] 
 ![![541, 0, 0, 0], ![351, 1, 0, 0], ![147, 0, 1, 0], ![339, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![541, 0, 0, 0], ![0, 541, 0, 0], ![0, 0, 541, 0], ![0, 0, 0, 541]], ![![-190, 1, 0, 0], ![0, -190, 1, 0], ![0, 0, -190, 1], ![383, 332, 80, -189]]]
  hmulB := by decide
  f := ![![![84931, -11889887, 69606, -37], ![241827, -33853616, 20017, 0]], ![![55101, -7713910, 45158, -24], ![156891, -21963518, 12984, 0]], ![![23247, -3230692, 18903, -10], ![66192, -9198622, 5410, 0]], ![![52959, -7450492, 43582, -23], ![150792, -21213502, 12444, 0]]]
  g := ![![![1, 0, 0, 0], ![-351, 541, 0, 0], ![-147, 0, 541, 0], ![-339, 0, 0, 541]], ![![-1, 1, 0, 0], ![123, -190, 1, 0], ![51, 0, -190, 1], ![-118, 332, 80, -189]]]
  hle1 := by decide
  hle2 := by decide

lemma NI541N2 : Nat.card (O ⧸ I541N2) = 541 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI541N2)

lemma isPrimeI541N2 : Ideal.IsPrime I541N2 := prime_ideal_of_norm_prime hp541.out _ NI541N2
def I541N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![541, 0, 0, 0], ![-182, 1, 0, 0]] i)))

def SI541N3: IdealEqSpanCertificate timesTableO I541N3
 ![![541, 0, 0, 0], ![-182, 1, 0, 0]] 
 ![![541, 0, 0, 0], ![359, 1, 0, 0], ![418, 0, 1, 0], ![336, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![541, 0, 0, 0], ![0, 541, 0, 0], ![0, 0, 541, 0], ![0, 0, 0, 541]], ![![-182, 1, 0, 0], ![0, -182, 1, 0], ![0, 0, -182, 1], ![383, 332, 80, -181]]]
  hmulB := by decide
  f := ![![![100829, -12773678, 77462, -40], ![299714, -37968462, 21640, 0]], ![![67159, -8476291, 51485, -27], ![199630, -25194911, 14607, 0]], ![![78140, -9869379, 59867, -31], ![232271, -29335724, 16771, 0]], ![![62832, -7933300, 48138, -25], ![186768, -23580926, 13526, 0]]]
  g := ![![![1, 0, 0, 0], ![-359, 541, 0, 0], ![-418, 0, 541, 0], ![-336, 0, 0, 541]], ![![-1, 1, 0, 0], ![120, -182, 1, 0], ![140, 0, -182, 1], ![-169, 332, 80, -181]]]
  hle1 := by decide
  hle2 := by decide

lemma NI541N3 : Nat.card (O ⧸ I541N3) = 541 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI541N3)

lemma isPrimeI541N3 : Ideal.IsPrime I541N3 := prime_ideal_of_norm_prime hp541.out _ NI541N3
def MulI541N0 : IdealMulEqCertificate timesTableO (I541N0) I541N1
  ![![541, 0, 0, 0], ![168, 1, 0, 0]] ![![541, 0, 0, 0], ![203, 1, 0, 0]]
  ![![-362, -201, -12, 3]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![292681, 0, 0, 0], ![109823, 541, 0, 0]], ![![90888, 541, 0, 0], ![34104, 371, 1, 0]]]
 hmul := by decide
 f :=  ![![![![64492914973571629563, -278103947243152295203, -1529381100341322352, -777565495743289], ![-171821911446168155467, 742000599845642450658, 420662933197132957, 0]], ![![-64398673393561811, 0, 0, 0], ![37286, -7361925, 0, 0]]]]
 g :=  ![![![![231007, 108741, 6492, -1623]], ![![85532, 40234, 2397, -600]]], ![![![70587, 33199, 1977, -495]], ![![26136, 12284, 730, -183]]]]
 hle1 := by decide
 hle2 := by decide

def MulI541N1 : IdealMulEqCertificate timesTableO (I541N0*I541N1) I541N2
  ![![-362, -201, -12, 3]] ![![541, 0, 0, 0], ![-190, 1, 0, 0]]
  ![![541, 0, 0, 0], ![25113, 13302, 773, -193]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI541N0
 hI2 := rfl
 M :=  ![![![-195842, -108741, -6492, 1623], ![69929, 38824, 2319, -579]]]
 hmul := by decide
 f :=  ![![![![13240237198867, 22911254876123163, -120585921057470, 12170], ![37699833287298, 65236982041136412, -6583973, 0]]], ![![![615609832611064, 1065267454608688634, -5606687974145202, 565849], ![1752867997066237, 3033218135848934826, -306124313, 0]]]]
 g :=  ![![![![-362, -201, -12, 3], ![0, 0, 0, 0]], ![![-10, -2, 0, 0], ![3, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI541N2 : IdealMulEqCertificate timesTableO (I541N0*I541N1*I541N2) I541N3
  ![![541, 0, 0, 0], ![25113, 13302, 773, -193]] ![![541, 0, 0, 0], ![-182, 1, 0, 0]]
  ![![541, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI541N1
 hI2 := rfl
 M :=  ![![![292681, 0, 0, 0], ![-98462, 541, 0, 0]], ![![13586133, 7196382, 418193, -104413], ![-4644485, -2459927, -142824, 35706]]]
 hmul := by decide
 f :=  ![![![![129560485129238, -16447388629594467, 99575684220659, -50610384018], ![385118265440261, -48888200550233858, 27374852327683, 0]], ![![-27800135, 0, 0, 0], ![0, 0, 0, 0]]]]
 g :=  ![![![![541, 0, 0, 0]], ![![-182, 1, 0, 0]]], ![![![25113, 13302, 773, -193]], ![![-8585, -4547, -264, 66]]]]
 hle1 := by decide
 hle2 := by decide

def PBC541 : IsPrimesAboveP 541 ![I541N0, I541N1, I541N2, I541N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI541N0
    exact isPrimeI541N1
    exact isPrimeI541N2
    exact isPrimeI541N3
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI541N2, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl

