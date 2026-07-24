
import IdealArithmetic.Examples.NF5_3_1012500000_1.RI5_3_1012500000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp467 : Fact (Nat.Prime 467) := {out := by norm_num}

def I467N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-125, -213, 68, -27, 25]] i)))

def SI467N0: IdealEqSpanCertificate' Table ![![-125, -213, 68, -27, 25]] 
 ![![467, 0, 0, 0, 0], ![0, 467, 0, 0, 0], ![28, 96, 1, 0, 0], ![5, 133, 0, 1, 0], ![55, 341, 0, 0, 1]] where
  M :=![![![-125, -213, 68, -27, 25], ![150, 250, -82, 39, -27], ![-162, -255, 73, -123, 39], ![120, 198, -48, 79, -40], ![-42, -141, 64, 309, -2]]]
  hmulB := by decide  
  f := ![![![509, 651, 370, 237, 49]], ![![294, 1244, 1328, 627, 237]], ![![94, 303, 303, 147, 53]], ![![89, 361, 382, 181, 68]], ![![277, 992, 1020, 489, 180]]]
  g := ![![![-7, -25, 68, -27, 25], ![8, 26, -82, 39, -27], ![-8, -9, 73, -123, 39], ![7, 17, -48, 79, -40], ![-7, -100, 64, 309, -2]]]
  hle1 := by decide   
  hle2 := by decide  


def P467P0 : CertificateIrreducibleZModOfList' 467 2 2 8 [311, 350, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [117, 466], [0, 1]]
 g := ![![[351, 202], [264, 366], [267], [447], [446, 75], [387], [124, 139], [117, 1]], ![[168, 265], [122, 101], [267], [447], [348, 392], [387], [42, 328], [234, 466]]]
 h' := ![![[117, 466], [88, 210], [65, 154], [198, 326], [460, 410], [177, 363], [197, 353], [39, 302], [0, 1]], ![[0, 1], [374, 257], [337, 313], [46, 141], [329, 57], [151, 104], [402, 114], [348, 165], [117, 466]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [262]]
 b := ![[], [42, 131]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI467N0 : CertifiedPrimeIdeal' SI467N0 467 where
  n := 2
  hpos := by decide
  P := [311, 350, 1]
  hirr := P467P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1289, 1592, -3178, -4908, -239]
  a := ![0, -1, -4, -1, -6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![274, 2229, -3178, -4908, -239]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI467N0 : Ideal.IsPrime I467N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI467N0 B_one_repr
lemma NI467N0 : Nat.card (O ⧸ I467N0) = 218089 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI467N0

def I467N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![469, 135, -81, 0, -28]] i)))

def SI467N1: IdealEqSpanCertificate' Table ![![469, 135, -81, 0, -28]] 
 ![![467, 0, 0, 0, 0], ![0, 467, 0, 0, 0], ![213, 231, 1, 0, 0], ![99, 133, 0, 1, 0], ![201, 361, 0, 0, 1]] where
  M :=![![![469, 135, -81, 0, -28], ![-168, 49, 4, 18, 0], ![0, -168, 43, -30, 18], ![18, 129, -35, 19, -14], ![-30, 27, -1, 12, -5]]]
  hmulB := by decide  
  f := ![![![59, 165, 155, 72, 26]], ![![156, 449, 454, 246, 72]], ![![105, 300, 298, 156, 48]], ![![57, 163, 162, 85, 26]], ![![147, 421, 420, 222, 67]]]
  g := ![![![50, 62, -81, 0, -28], ![-6, -7, 4, 18, 0], ![-21, -27, 43, -30, 18], ![18, 23, -35, 19, -14], ![0, 1, -1, 12, -5]]]
  hle1 := by decide   
  hle2 := by decide  


def P467P1 : CertificateIrreducibleZModOfList' 467 2 2 8 [222, 434, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [33, 466], [0, 1]]
 g := ![![[145, 406], [449, 43], [462], [262], [446, 141], [421], [148, 286], [33, 1]], ![[0, 61], [0, 424], [462], [262], [429, 326], [421], [246, 181], [66, 466]]]
 h' := ![![[33, 466], [260, 261], [147, 38], [275, 205], [459, 440], [408, 190], [301, 68], [146, 400], [0, 1]], ![[0, 1], [0, 206], [0, 429], [35, 262], [35, 27], [140, 277], [210, 399], [270, 67], [33, 466]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [151]]
 b := ![[], [272, 309]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI467N1 : CertifiedPrimeIdeal' SI467N1 467 where
  n := 2
  hpos := by decide
  P := [222, 434, 1]
  hirr := P467P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![171, -31612, 4798, 2310, 1167]
  a := ![3, -64, 1, -1, 2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3180, -4001, 4798, 2310, 1167]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI467N1 : Ideal.IsPrime I467N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI467N1 B_one_repr
lemma NI467N1 : Nat.card (O ⧸ I467N1) = 218089 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI467N1

def I467N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 1, 3, 22, -4]] i)))

def SI467N2: IdealEqSpanCertificate' Table ![![5, 1, 3, 22, -4]] 
 ![![467, 0, 0, 0, 0], ![140, 1, 0, 0, 0], ![14, 0, 1, 0, 0], ![289, 0, 0, 1, 0], ![116, 0, 0, 0, 1]] where
  M :=![![![5, 1, 3, 22, -4], ![-24, -55, 4, 24, 22], ![132, 306, -155, -444, 24], ![-42, -71, 109, 217, -86], ![-510, -1239, 555, 1758, -17]]]
  hmulB := by decide  
  f := ![![![157291, 447687, 431371, 212846, 74594]], ![![48112, 136943, 131954, 65108, 22818]], ![![7450, 21216, 20447, 10088, 3536]], ![![97271, 276856, 266766, 131627, 46130]], ![![41410, 117873, 113581, 56042, 19641]]]
  g := ![![![-13, 1, 3, 22, -4], ![-4, -55, 4, 24, 22], ![182, 306, -155, -444, 24], ![-95, -71, 109, 217, -86], ![-730, -1239, 555, 1758, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI467N2 : Nat.card (O ⧸ I467N2) = 467 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI467N2)

lemma isPrimeI467N2 : Ideal.IsPrime I467N2 := prime_ideal_of_norm_prime hp467.out _ NI467N2
def MulI467N0 : IdealMulLeCertificate' Table 
  ![![-125, -213, 68, -27, 25]] ![![469, 135, -81, 0, -28]]
  ![![-24077, -41544, 13117, -6087, 4977]] where
 M := ![![![-24077, -41544, 13117, -6087, 4977]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI467N1 : IdealMulLeCertificate' Table 
  ![![-24077, -41544, 13117, -6087, 4977]] ![![5, 1, 3, 22, -4]]
  ![![467, 0, 0, 0, 0]] where
 M := ![![![325499, 540319, -172790, 77989, -63979]]]
 hmul := by decide  
 g := ![![![![697, 1157, -370, 167, -137]]]]
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

def I479N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-121, -152, 203, 19, 53]] i)))

def SI479N0: IdealEqSpanCertificate' Table ![![-121, -152, 203, 19, 53]] 
 ![![479, 0, 0, 0, 0], ![0, 479, 0, 0, 0], ![0, 0, 479, 0, 0], ![113, 177, 13, 1, 0], ![147, 250, 198, 0, 1]] where
  M :=![![![-121, -152, 203, 19, 53], ![318, 674, 226, 207, 19], ![114, 603, 1069, 393, 207], ![150, 235, -103, 55, -38], ![336, 888, 783, 459, 148]]]
  hmulB := by decide  
  f := ![![![-1967, -1050, 465, -85, 167]], ![![1002, 538, -238, 39, -85]], ![![-510, -273, 125, -15, 39]], ![![-107, -56, 25, -6, 9]], ![![-291, -154, 70, -12, 23]]]
  g := ![![![-21, -35, -22, 19, 53], ![-54, -85, -13, 207, 19], ![-156, -252, -94, 393, 207], ![-1, 0, 14, 55, -38], ![-153, -245, -72, 459, 148]]]
  hle1 := by decide   
  hle2 := by decide  


def P479P0 : CertificateIrreducibleZModOfList' 479 3 2 8 [160, 7, 129, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 110, 388], [328, 368, 91], [0, 1]]
 g := ![![[413, 210, 27], [78, 51, 230], [227, 108, 75], [420, 404, 69], [133, 358, 392], [399, 70], [392, 79, 355], [1]], ![[100, 279, 319, 403], [402, 240, 460, 8], [435, 144, 443, 33], [298, 318, 302, 293], [16, 433, 77, 25], [266, 338], [5, 337, 196, 445], [277, 378, 39, 375]], ![[85, 285, 434, 287], [116, 148, 83, 344], [145, 180, 59, 260], [54, 104, 220, 299], [62, 454, 145, 424], [431, 46], [457, 436, 401, 455], [286, 80, 26, 104]]]
 h' := ![![[22, 110, 388], [453, 266, 386], [84, 252, 250], [339, 381, 324], [275, 457, 126], [229, 382, 256], [29, 157, 178], [319, 472, 350], [0, 1]], ![[328, 368, 91], [202, 63, 8], [345, 260, 92], [146, 114, 257], [102, 7, 470], [468, 374, 50], [212, 56, 443], [337, 64, 107], [22, 110, 388]], ![[0, 1], [300, 150, 85], [354, 446, 137], [76, 463, 377], [268, 15, 362], [167, 202, 173], [55, 266, 337], [325, 422, 22], [328, 368, 91]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [222, 188], []]
 b := ![[], [62, 258, 360], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI479N0 : CertifiedPrimeIdeal' SI479N0 479 where
  n := 3
  hpos := by decide
  P := [160, 7, 129, 1]
  hirr := P479P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-74883, -181850, 102264, 286054, -1974]
  a := ![1, -3, -2, -1, -3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-67033, -105052, -6734, 286054, -1974]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI479N0 : Ideal.IsPrime I479N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI479N0 B_one_repr
lemma NI479N0 : Nat.card (O ⧸ I479N0) = 109902239 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI479N0

def I479N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1967, -1050, 465, -85, 167]] i)))

def SI479N1: IdealEqSpanCertificate' Table ![![-1967, -1050, 465, -85, 167]] 
 ![![479, 0, 0, 0, 0], ![0, 479, 0, 0, 0], ![267, 404, 1, 0, 0], ![330, 342, 0, 1, 0], ![474, 107, 0, 0, 1]] where
  M :=![![![-1967, -1050, 465, -85, 167], ![1002, 538, -238, 39, -85], ![-510, -273, 125, -15, 39], ![294, 149, -69, 23, -22], ![240, 138, -75, -33, -4]]]
  hmulB := by decide  
  f := ![![![-121, -152, 203, 19, 53]], ![![318, 674, 226, 207, 19]], ![![201, 485, 306, 186, 46]], ![![144, 377, 301, 161, 50]], ![![-48, 2, 253, 66, 57]]]
  g := ![![![-370, -371, 465, -85, 167], ![192, 193, -238, 39, -85], ![-99, -104, 125, -15, 39], ![45, 47, -69, 23, -22], ![69, 88, -75, -33, -4]]]
  hle1 := by decide   
  hle2 := by decide  


def P479P1 : CertificateIrreducibleZModOfList' 479 2 2 8 [122, 290, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [189, 478], [0, 1]]
 g := ![![[395, 373], [423, 89], [203, 336], [325, 125], [139, 292], [162], [179, 417], [189, 1]], ![[0, 106], [0, 390], [0, 143], [0, 354], [242, 187], [162], [436, 62], [378, 478]]]
 h' := ![![[189, 478], [126, 159], [142, 202], [107, 78], [286, 110], [450, 115], [196, 246], [413, 153], [0, 1]], ![[0, 1], [0, 320], [0, 277], [0, 401], [0, 369], [151, 364], [227, 233], [111, 326], [189, 478]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36]]
 b := ![[], [215, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI479N1 : CertifiedPrimeIdeal' SI479N1 479 where
  n := 2
  hpos := by decide
  P := [122, 290, 1]
  hirr := P479P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3035, 11600, -1457, -9212, 3453]
  a := ![1, 19, 3, -1, 6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3748, 7059, -1457, -9212, 3453]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI479N1 : Ideal.IsPrime I479N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI479N1 B_one_repr
lemma NI479N1 : Nat.card (O ⧸ I479N1) = 229441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI479N1
def MulI479N0 : IdealMulLeCertificate' Table 
  ![![-121, -152, 203, 19, 53]] ![![-1967, -1050, 465, -85, 167]]
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

def I487N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-403, -74, 271, 61, 67]] i)))

def SI487N0: IdealEqSpanCertificate' Table ![![-403, -74, 271, 61, 67]] 
 ![![487, 0, 0, 0, 0], ![0, 487, 0, 0, 0], ![0, 0, 487, 0, 0], ![264, 112, 130, 1, 0], ![386, 413, 300, 0, 1]] where
  M :=![![![-403, -74, 271, 61, 67], ![402, 602, 410, 237, 61], ![366, 1317, 1351, 651, 237], ![54, -5, -47, -11, -10], ![468, 1206, 1115, 549, 196]]]
  hmulB := by decide  
  f := ![![![35, 60, -19, 13, -7]], ![![-42, -70, 18, -27, 13]], ![![78, 153, -41, -45, -27]], ![![30, 57, -17, -11, -8]], ![![40, 82, -25, -40, -11]]]
  g := ![![![-87, -71, -57, 61, 67], ![-176, -105, -100, 237, 61], ![-540, -348, -317, 651, 237], ![14, 11, 9, -11, -10], ![-452, -290, -265, 549, 196]]]
  hle1 := by decide   
  hle2 := by decide  


def P487P0 : CertificateIrreducibleZModOfList' 487 3 2 8 [25, 181, 42, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [202, 411, 387], [243, 75, 100], [0, 1]]
 g := ![![[401, 435, 261], [290, 245, 394], [433, 2, 388], [25, 397], [131, 91], [450, 481, 168], [127, 43, 303], [1]], ![[232, 292, 380, 305], [393, 44, 424, 326], [383, 391, 393, 37], [383, 15], [119, 288], [333, 419, 277, 131], [152, 218, 434, 406], [333, 252, 280, 298]], ![[423, 353, 81, 166], [100, 346, 470, 144], [297, 98, 288, 60], [411, 84], [316, 50], [28, 50, 25, 441], [364, 149, 11, 442], [410, 226, 401, 189]]]
 h' := ![![[202, 411, 387], [55, 458, 47], [376, 258, 260], [122, 37, 444], [100, 70, 408], [438, 241, 86], [234, 426, 46], [462, 306, 445], [0, 1]], ![[243, 75, 100], [272, 106, 94], [3, 182, 31], [204, 40, 380], [195, 486, 224], [107, 330, 369], [282, 158, 297], [374, 482, 340], [202, 411, 387]], ![[0, 1], [231, 410, 346], [384, 47, 196], [49, 410, 150], [265, 418, 342], [183, 403, 32], [34, 390, 144], [403, 186, 189], [243, 75, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 400], []]
 b := ![[], [142, 350, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI487N0 : CertifiedPrimeIdeal' SI487N0 487 where
  n := 3
  hpos := by decide
  P := [25, 181, 42, 1]
  hirr := P487P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1649215, -3881486, 2148534, 6228088, -521218]
  a := ![-1, 0, -2, 2, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2966477, -998284, -1337038, 6228088, -521218]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI487N0 : Ideal.IsPrime I487N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI487N0 B_one_repr
lemma NI487N0 : Nat.card (O ⧸ I487N0) = 115501303 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI487N0

def I487N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![35, 60, -19, 13, -7]] i)))

def SI487N1: IdealEqSpanCertificate' Table ![![35, 60, -19, 13, -7]] 
 ![![487, 0, 0, 0, 0], ![0, 487, 0, 0, 0], ![166, 197, 1, 0, 0], ![473, 279, 0, 1, 0], ![75, 114, 0, 0, 1]] where
  M :=![![![35, 60, -19, 13, -7], ![-42, -70, 18, -27, 13], ![78, 153, -41, -45, -27], ![-66, -131, 51, 85, 6], ![-84, -216, 25, 153, 76]]]
  hmulB := by decide  
  f := ![![![-403, -74, 271, 61, 67]], ![![402, 602, 410, 237, 61]], ![![26, 221, 261, 118, 48]], ![![-161, 273, 498, 195, 100]], ![![33, 132, 140, 66, 25]]]
  g := ![![![-5, 2, -19, 13, -7], ![18, 5, 18, -27, 13], ![62, 49, -41, -45, -27], ![-101, -71, 51, 85, 6], ![-169, -116, 25, 153, 76]]]
  hle1 := by decide   
  hle2 := by decide  


def P487P1 : CertificateIrreducibleZModOfList' 487 2 2 8 [129, 222, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [265, 486], [0, 1]]
 g := ![![[81, 336], [373, 447], [370, 164], [382], [442], [237, 271], [337, 50], [265, 1]], ![[0, 151], [0, 40], [0, 323], [382], [442], [463, 216], [438, 437], [43, 486]]]
 h' := ![![[265, 486], [96, 290], [483, 272], [469, 250], [424, 384], [108, 429], [357, 324], [392, 455], [0, 1]], ![[0, 1], [0, 197], [0, 215], [0, 237], [401, 103], [322, 58], [18, 163], [191, 32], [265, 486]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [401]]
 b := ![[], [97, 444]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI487N1 : CertifiedPrimeIdeal' SI487N1 487 where
  n := 2
  hpos := by decide
  P := [129, 222, 1]
  hirr := P487P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-711, -2288, -636, 236, 228]
  a := ![0, 0, -6, -10, -4]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-49, 64, -636, 236, 228]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI487N1 : Ideal.IsPrime I487N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI487N1 B_one_repr
lemma NI487N1 : Nat.card (O ⧸ I487N1) = 237169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI487N1
def MulI487N0 : IdealMulLeCertificate' Table 
  ![![-403, -74, 271, 61, 67]] ![![35, 60, -19, 13, -7]]
  ![![487, 0, 0, 0, 0]] where
 M := ![![![487, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I491N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4051, -6826, 2073, -1017, 927]] i)))

def SI491N0: IdealEqSpanCertificate' Table ![![-4051, -6826, 2073, -1017, 927]] 
 ![![491, 0, 0, 0, 0], ![0, 491, 0, 0, 0], ![0, 0, 491, 0, 0], ![386, 69, 228, 1, 0], ![444, 473, 335, 0, 1]] where
  M :=![![![-4051, -6826, 2073, -1017, 927], ![5562, 9854, -3298, -1197, -1017], ![-6102, -9693, 5225, 2109, -1197], ![1854, 837, -1169, 6707, 950], ![5160, 8922, -11459, -22005, 8360]]]
  hmulB := by decide  
  f := ![![![-66353, -37960, 12367, -4317, 5001]], ![![30006, 8662, -16546, -2865, -4317]], ![![-25902, -34749, -20843, -12975, -2865]], ![![-59954, -44749, -2285, -9820, 1993]], ![![-48768, -49727, -19024, -15537, -1600]]]
  g := ![![![-47, -764, -156, -1017, 927], ![1872, 1168, 1243, -1197, -1017], ![-588, 837, -152, 2109, -1197], ![-6128, -1856, -3765, 6707, 950], ![9750, -4943, 4491, -22005, 8360]]]
  hle1 := by decide   
  hle2 := by decide  


def P491P0 : CertificateIrreducibleZModOfList' 491 3 2 8 [235, 246, 440, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [367, 334, 92], [175, 156, 399], [0, 1]]
 g := ![![[222, 14, 220], [267, 485, 197], [236, 468], [383, 328, 168], [266, 395], [313, 42, 243], [196, 30, 146], [1]], ![[310, 281, 121, 348], [255, 171, 64, 446], [22, 401], [157, 378, 354, 198], [259, 27], [29, 31, 279, 486], [57, 380, 432, 186], [282, 393, 402, 453]], ![[172, 180, 52, 37], [324, 36, 284, 12], [226, 80], [369, 466, 254, 144], [108, 37], [249, 266, 393, 363], [276, 284, 185, 106], [348, 70, 229, 38]]]
 h' := ![![[367, 334, 92], [103, 94, 165], [50, 132, 213], [339, 235, 307], [34, 488, 64], [95, 37, 229], [94, 450, 456], [256, 245, 51], [0, 1]], ![[175, 156, 399], [3, 229, 18], [287, 78, 200], [208, 307, 281], [264, 41, 379], [47, 401, 339], [361, 59, 97], [435, 457, 54], [367, 334, 92]], ![[0, 1], [444, 168, 308], [114, 281, 78], [14, 440, 394], [93, 453, 48], [374, 53, 414], [26, 473, 429], [327, 280, 386], [175, 156, 399]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [212, 268], []]
 b := ![[], [477, 487, 360], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI491N0 : CertifiedPrimeIdeal' SI491N0 491 where
  n := 3
  hpos := by decide
  P := [235, 246, 440, 1]
  hirr := P491P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-341816, -1159374, 238188, 1152930, 407529]
  a := ![13, -1, -2, 1, -6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1275592, -556971, -812937, 1152930, 407529]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI491N0 : Ideal.IsPrime I491N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI491N0 B_one_repr
lemma NI491N0 : Nat.card (O ⧸ I491N0) = 118370771 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI491N0

def I491N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![77, 112, -87, 3, -25]] i)))

def SI491N1: IdealEqSpanCertificate' Table ![![77, 112, -87, 3, -25]] 
 ![![491, 0, 0, 0, 0], ![148, 1, 0, 0, 0], ![191, 0, 1, 0, 0], ![185, 0, 0, 1, 0], ![371, 0, 0, 0, 1]] where
  M :=![![![77, 112, -87, 3, -25], ![-150, -298, -52, -81, 3], ![18, -105, -385, -123, -81], ![-90, -147, 57, -19, 20], ![-132, -336, -251, -141, -40]]]
  hmulB := by decide  
  f := ![![![12511, 6706, -2957, 507, -1075]], ![![3758, 2014, -888, 153, -323]], ![![4873, 2611, -1152, 198, -418]], ![![4711, 2527, -1114, 188, -405]], ![![9451, 5068, -2232, 384, -815]]]
  g := ![![![18, 112, -87, 3, -25], ![138, -298, -52, -81, 3], ![289, -105, -385, -123, -81], ![14, -147, 57, -19, 20], ![282, -336, -251, -141, -40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI491N1 : Nat.card (O ⧸ I491N1) = 491 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI491N1)

lemma isPrimeI491N1 : Ideal.IsPrime I491N1 := prime_ideal_of_norm_prime hp491.out _ NI491N1

def I491N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5857, 9789, -3109, 1422, -1178]] i)))

def SI491N2: IdealEqSpanCertificate' Table ![![5857, 9789, -3109, 1422, -1178]] 
 ![![491, 0, 0, 0, 0], ![451, 1, 0, 0, 0], ![364, 0, 1, 0, 0], ![117, 0, 0, 1, 0], ![485, 0, 0, 0, 1]] where
  M :=![![![5857, 9789, -3109, 1422, -1178], ![-7068, -11813, 3752, -1716, 1422], ![8532, 14262, -4529, 2064, -1716], ![-5982, -9999, 3177, -1445, 1202], ![-2202, -3687, 1171, -510, 445]]]
  hmulB := by decide  
  f := ![![![904319, 482307, -213689, 38982, -76628]], ![![829711, 442516, -196059, 35766, -70306]], ![![670888, 357810, -158529, 28920, -56848]], ![![215211, 114780, -50854, 9277, -18236]], ![![893051, 476298, -211026, 38496, -75673]]]
  g := ![![![-5850, 9789, -3109, 1422, -1178], ![7059, -11813, 3752, -1716, 1422], ![-8522, 14262, -4529, 2064, -1716], ![5974, -9999, 3177, -1445, 1202], ![2196, -3687, 1171, -510, 445]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI491N2 : Nat.card (O ⧸ I491N2) = 491 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI491N2)

lemma isPrimeI491N2 : Ideal.IsPrime I491N2 := prime_ideal_of_norm_prime hp491.out _ NI491N2
def MulI491N0 : IdealMulLeCertificate' Table 
  ![![-4051, -6826, 2073, -1017, 927]] ![![77, 112, -87, 3, -25]]
  ![![718453, 1200798, -381362, 174390, -144536]] where
 M := ![![![718453, 1200798, -381362, 174390, -144536]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI491N1 : IdealMulLeCertificate' Table 
  ![![718453, 1200798, -381362, 174390, -144536]] ![![5857, 9789, -3109, 1422, -1178]]
  ![![491, 0, 0, 0, 0]] where
 M := ![![![-8257974335, -13801896579, 4383697591, -2004340560, 1660912574]]]
 hmul := by decide  
 g := ![![![![-16818685, -28109769, 8928101, -4082160, 3382714]]]]
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

def I499N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-523, -928, 131, -177, 75]] i)))

def SI499N0: IdealEqSpanCertificate' Table ![![-523, -928, 131, -177, 75]] 
 ![![499, 0, 0, 0, 0], ![0, 499, 0, 0, 0], ![50, 278, 1, 0, 0], ![486, 129, 0, 1, 0], ![48, 219, 0, 0, 1]] where
  M :=![![![-523, -928, 131, -177, 75], ![450, 602, -658, -33, -177], ![-1062, -2205, -631, -663, -33], ![498, 843, -235, 131, -94], ![-132, -588, -953, -381, -184]]]
  hmulB := by decide  
  f := ![![![1175, 598, -267, 99, -99]], ![![-594, -310, 94, -117, 99]], ![![-212, -111, 25, -57, 45]], ![![990, 501, -235, 68, -71]], ![![-150, -84, 17, -36, 35]]]
  g := ![![![151, -62, 131, -177, 75], ![116, 454, -658, -33, -177], ![710, 533, -631, -663, -33], ![-94, 140, -235, 131, -94], ![484, 709, -953, -381, -184]]]
  hle1 := by decide   
  hle2 := by decide  


def P499P0 : CertificateIrreducibleZModOfList' 499 2 2 8 [239, 471, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [28, 498], [0, 1]]
 g := ![![[169, 190], [319, 226], [64], [413], [438, 255], [307, 4], [468, 120], [28, 1]], ![[0, 309], [160, 273], [64], [413], [93, 244], [419, 495], [335, 379], [56, 498]]]
 h' := ![![[28, 498], [106, 317], [356, 274], [282, 491], [108, 122], [479, 442], [423, 2], [294, 46], [0, 1]], ![[0, 1], [0, 182], [44, 225], [58, 8], [31, 377], [380, 57], [479, 497], [85, 453], [28, 498]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [441]]
 b := ![[], [406, 470]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI499N0 : CertifiedPrimeIdeal' SI499N0 499 where
  n := 2
  hpos := by decide
  P := [239, 471, 1]
  hirr := P499P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-129, -1199, 252, -1013, 1103]
  a := ![-1, -3, 1, -1, 2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![855, -365, 252, -1013, 1103]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI499N0 : Ideal.IsPrime I499N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI499N0 B_one_repr
lemma NI499N0 : Nat.card (O ⧸ I499N0) = 249001 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI499N0

def I499N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![469819, 266744, -115226, 23084, -41470]] i)))

def SI499N1: IdealEqSpanCertificate' Table ![![469819, 266744, -115226, 23084, -41470]] 
 ![![499, 0, 0, 0, 0], ![0, 499, 0, 0, 0], ![167, 262, 1, 0, 0], ![26, 349, 0, 1, 0], ![345, 216, 0, 0, 1]] where
  M :=![![![469819, 266744, -115226, 23084, -41470], ![-248820, -152231, 63862, -14148, 23084], ![138504, 97440, -38833, 10104, -14148], ![-83400, -61006, 23988, -6493, 8758], ![-59148, -37608, 15550, -3612, 5633]]]
  hmulB := by decide  
  f := ![![![-1583, -3600, 2426, 6500, -914]], ![![-5484, -15293, 834, 11508, 6500]], ![![-3331, -9050, 1149, 7924, 3130]], ![![-3934, -10905, 774, 8511, 4438]], ![![-3801, -9912, 2420, 10656, 2147]]]
  g := ![![![66973, 62840, -115226, 23084, -41470], ![-37094, -33933, 63862, -14148, 23084], ![22529, 19642, -38833, 10104, -14148], ![-13912, -11967, 23988, -6493, 8758], ![-9029, -8152, 15550, -3612, 5633]]]
  hle1 := by decide   
  hle2 := by decide  


def P499P1 : CertificateIrreducibleZModOfList' 499 2 2 8 [129, 387, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [112, 498], [0, 1]]
 g := ![![[3, 339], [448, 111], [279], [472], [447, 189], [73, 204], [242, 107], [112, 1]], ![[47, 160], [405, 388], [279], [472], [158, 310], [466, 295], [250, 392], [224, 498]]]
 h' := ![![[112, 498], [92, 73], [487, 333], [428, 165], [221, 338], [64, 380], [219, 357], [23, 439], [0, 1]], ![[0, 1], [284, 426], [358, 166], [445, 334], [153, 161], [209, 119], [283, 142], [289, 60], [112, 498]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [307]]
 b := ![[], [386, 403]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI499N1 : CertifiedPrimeIdeal' SI499N1 499 where
  n := 2
  hpos := by decide
  P := [129, 387, 1]
  hirr := P499P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1761, 1162, 880, -2998, 1250]
  a := ![3, 0, 3, -4, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-999, 1096, 880, -2998, 1250]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI499N1 : Ideal.IsPrime I499N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI499N1 B_one_repr
lemma NI499N1 : Nat.card (O ⧸ I499N1) = 249001 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI499N1

def I499N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 253, 243, 120, 42]] i)))

def SI499N2: IdealEqSpanCertificate' Table ![![89, 253, 243, 120, 42]] 
 ![![499, 0, 0, 0, 0], ![458, 1, 0, 0, 0], ![315, 0, 1, 0, 0], ![498, 0, 0, 1, 0], ![271, 0, 0, 0, 1]] where
  M :=![![![89, 253, 243, 120, 42], ![252, 719, 694, 342, 120], ![720, 2052, 1979, 978, 342], ![-18, -51, -49, -25, -8], ![618, 1761, 1691, 828, 293]]]
  hmulB := by decide  
  f := ![![![9671, 5567, -2389, 504, -864]], ![![8866, 5103, -2190, 462, -792]], ![![6111, 3519, -1510, 318, -546]], ![![9648, 5553, -2383, 503, -862]], ![![5249, 3020, -1296, 276, -469]]]
  g := ![![![-528, 253, 243, 120, 42], ![-1504, 719, 694, 342, 120], ![-4293, 2052, 1979, 978, 342], ![107, -51, -49, -25, -8], ![-3668, 1761, 1691, 828, 293]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI499N2 : Nat.card (O ⧸ I499N2) = 499 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI499N2)

lemma isPrimeI499N2 : Ideal.IsPrime I499N2 := prime_ideal_of_norm_prime hp499.out _ NI499N2
def MulI499N0 : IdealMulLeCertificate' Table 
  ![![-523, -928, 131, -177, 75]] ![![469819, 266744, -115226, 23084, -41470]]
  ![![13659347, 22505358, -7167487, 3258397, -2714221]] where
 M := ![![![13659347, 22505358, -7167487, 3258397, -2714221]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI499N1 : IdealMulLeCertificate' Table 
  ![![13659347, 22505358, -7167487, 3258397, -2714221]] ![![89, 253, 243, 120, 42]]
  ![![499, 0, 0, 0, 0]] where
 M := ![![![-9598265, -16437559, 4073836, -2683123, 1721051]]]
 hmul := by decide  
 g := ![![![![-19235, -32941, 8164, -5377, 3449]]]]
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

def I503N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-231763, -124601, 53496, -10551, 19401]] i)))

def SI503N0: IdealEqSpanCertificate' Table ![![-231763, -124601, 53496, -10551, 19401]] 
 ![![503, 0, 0, 0, 0], ![0, 503, 0, 0, 0], ![0, 0, 503, 0, 0], ![67, 133, 218, 1, 0], ![87, 37, 491, 0, 1]] where
  M :=![![![-231763, -124601, 53496, -10551, 19401], ![116406, 59252, -31166, 3411, -10551], ![-63306, -41859, 4547, -7311, 3411], ![35064, 18906, -8032, 1625, -2924], ![24342, 6063, -14668, -2871, -3736]]]
  hmulB := by decide  
  f := ![![![79, 223, -62, -303, -39]], ![![-234, -506, 496, 1239, -303]], ![![-1818, -4779, 955, 4713, 1239]], ![![-835, -2165, 532, 2315, 452]], ![![-1767, -4633, 955, 4614, 1169]]]
  g := ![![![-2411, 1115, -14259, -10551, 19401], ![1602, -8, 8759, 3411, -10551], ![258, 1599, -152, -7311, 3411], ![359, -177, 2134, 1625, -2924], ![1077, 1046, 4862, -2871, -3736]]]
  hle1 := by decide   
  hle2 := by decide  


def P503P0 : CertificateIrreducibleZModOfList' 503 3 2 8 [116, 501, 64, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [388, 373, 245], [51, 129, 258], [0, 1]]
 g := ![![[14, 293, 99], [41, 297, 237], [243, 492, 192], [299, 336], [359, 200, 275], [183, 219, 299], [348, 166, 72], [1]], ![[493, 316, 492, 51], [426, 358, 46, 87], [142, 257, 134, 302], [401, 11], [105, 263, 384, 277], [136, 391, 493, 34], [188, 100, 174, 178], [420, 247, 344, 417]], ![[450, 336, 134, 344], [470, 466, 262, 150], [361, 96, 464, 271], [13, 394], [389, 225, 106, 112], [231, 258, 95, 336], [118, 280, 288, 64], [354, 487, 158, 86]]]
 h' := ![![[388, 373, 245], [274, 234, 213], [483, 74, 339], [485, 99, 156], [105, 497, 237], [401, 400, 148], [375, 429, 430], [387, 2, 439], [0, 1]], ![[51, 129, 258], [133, 405, 303], [274, 163, 495], [367, 312, 115], [46, 435, 432], [326, 243, 396], [327, 182, 118], [268, 368, 282], [388, 373, 245]], ![[0, 1], [118, 367, 490], [91, 266, 172], [87, 92, 232], [452, 74, 337], [208, 363, 462], [114, 395, 458], [41, 133, 285], [51, 129, 258]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [164, 449], []]
 b := ![[], [336, 286, 456], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI503N0 : CertifiedPrimeIdeal' SI503N0 503 where
  n := 3
  hpos := by decide
  P := [116, 501, 64, 1]
  hirr := P503P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![386722, 894886, -530074, -1501816, 180802]
  a := ![1, 1, 1, -1, 4]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![169540, 385580, 473344, -1501816, 180802]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI503N0 : Ideal.IsPrime I503N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI503N0 B_one_repr
lemma NI503N0 : Nat.card (O ⧸ I503N0) = 127263527 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI503N0

def I503N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 223, -62, -303, -39]] i)))

def SI503N1: IdealEqSpanCertificate' Table ![![79, 223, -62, -303, -39]] 
 ![![503, 0, 0, 0, 0], ![0, 503, 0, 0, 0], ![90, 204, 1, 0, 0], ![416, 19, 0, 1, 0], ![131, 322, 0, 0, 1]] where
  M :=![![![79, 223, -62, -303, -39], ![-234, -506, 496, 1239, -303], ![-1818, -4779, 955, 4713, 1239], ![2148, 5184, -2408, -7475, 166], ![5622, 15411, -1498, -12723, -5738]]]
  hmulB := by decide  
  f := ![![![-231763, -124601, 53496, -10551, 19401]], ![![116406, 59252, -31166, 3411, -10551]], ![![5616, 1653, -3059, -519, -801]], ![![-187210, -100774, 43050, -8594, 15641]], ![![14207, 5492, -6048, -570, -1709]]]
  g := ![![![272, 62, -62, -303, -39], ![-1035, -55, 496, 1239, -303], ![-4395, -1368, 955, 4713, 1239], ![6574, 1163, -2408, -7475, 166], ![12296, 4792, -1498, -12723, -5738]]]
  hle1 := by decide   
  hle2 := by decide  


def P503P1 : CertificateIrreducibleZModOfList' 503 2 2 8 [141, 469, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [34, 502], [0, 1]]
 g := ![![[39, 132], [349, 121], [45, 225], [169], [345, 286], [246, 450], [463, 81], [34, 1]], ![[0, 371], [439, 382], [150, 278], [169], [9, 217], [456, 53], [199, 422], [68, 502]]]
 h' := ![![[34, 502], [85, 249], [194, 492], [2, 488], [146, 13], [21, 124], [107, 160], [236, 9], [0, 1]], ![[0, 1], [0, 254], [323, 11], [498, 15], [85, 490], [213, 379], [14, 343], [39, 494], [34, 502]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [486]]
 b := ![[], [396, 243]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI503N1 : CertifiedPrimeIdeal' SI503N1 503 where
  n := 2
  hpos := by decide
  P := [141, 469, 1]
  hirr := P503P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2027, -14, 7, 497, -1]
  a := ![4, 0, 0, 1, 0]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-408, -21, 7, 497, -1]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI503N1 : Ideal.IsPrime I503N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI503N1 B_one_repr
lemma NI503N1 : Nat.card (O ⧸ I503N1) = 253009 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI503N1
def MulI503N0 : IdealMulLeCertificate' Table 
  ![![-231763, -124601, 53496, -10551, 19401]] ![![79, 223, -62, -303, -39]]
  ![![503, 0, 0, 0, 0]] where
 M := ![![![503, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC503 : ContainsPrimesAboveP 503 ![I503N0, I503N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI503N0
    exact isPrimeI503N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 503 (by decide) (𝕀 ⊙ MulI503N0)
instance hp509 : Fact (Nat.Prime 509) := {out := by norm_num}

def I509N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![413, 1235, -356, 81, -147]] i)))

def SI509N0: IdealEqSpanCertificate' Table ![![413, 1235, -356, 81, -147]] 
 ![![509, 0, 0, 0, 0], ![0, 509, 0, 0, 0], ![0, 0, 509, 0, 0], ![0, 0, 0, 509, 0], ![385, 47, 134, 41, 1]] where
  M :=![![![413, 1235, -356, 81, -147], ![-882, -1792, 674, 267, 81], ![486, 333, -361, 1785, 267], ![24, 582, -420, -2947, 164], ![1542, 4563, -8, -3687, -2188]]]
  hmulB := by decide  
  f := ![![![-779, -2215, -2134, -1053, -369]], ![![-2214, -6314, -6088, -3003, -1053]], ![![-6318, -18009, -17363, -8565, -3003]], ![![156, 444, 428, 211, 74]], ![![-2455, -6994, -6742, -3326, -1166]]]
  g := ![![![112, 16, 38, 12, -147], ![-63, -11, -20, -6, 81], ![-201, -24, -71, -18, 267], ![-124, -14, -44, -19, 164], ![1658, 211, 576, 169, -2188]]]
  hle1 := by decide   
  hle2 := by decide  


def P509P0 : CertificateIrreducibleZModOfList' 509 4 2 8 [474, 70, 33, 380, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [21, 22, 258, 508], [219, 418, 429, 33], [398, 68, 331, 477], [0, 1]]
 g := ![![[306, 398, 416, 359], [304, 18, 324], [331, 414, 307, 505], [134, 28, 50, 174], [238, 13, 242, 278], [250, 379, 131, 158], [305, 320, 129, 1], []], ![[268, 268, 491, 209, 402, 280], [309, 263, 237], [0, 131, 290, 164, 230, 500], [232, 501, 336, 116, 271, 102], [194, 179, 438, 288, 303, 4], [103, 503, 101, 104, 502, 493], [204, 166, 69, 207, 231, 224], [484, 20, 46, 173, 136, 508]], ![[228, 342, 188, 158, 366, 40], [409, 334, 118], [149, 446, 456, 275, 335, 476], [332, 319, 103, 113, 56, 250], [102, 164, 173, 89, 103, 299], [268, 254, 342, 200, 99, 124], [153, 18, 450, 23, 339, 377], [110, 126, 429, 68, 167, 307]], ![[453, 412, 444, 380, 110, 157], [429, 89, 94], [268, 168, 376, 384, 467, 487], [421, 428, 431, 448, 5, 171], [152, 208, 335, 195, 181, 46], [127, 252, 199, 22, 164, 316], [63, 160, 146, 346, 101, 481], [194, 69, 17, 467, 23, 317]]]
 h' := ![![[21, 22, 258, 508], [74, 490, 437, 195], [387, 147, 112, 18], [109, 237, 40, 93], [186, 330, 0, 400], [97, 33, 14, 473], [495, 30, 45, 448], [0, 0, 0, 1], [0, 1]], ![[219, 418, 429, 33], [126, 300, 64, 168], [0, 4, 233, 42], [0, 397, 240, 3], [80, 352, 411, 336], [134, 17, 168, 93], [114, 344, 68, 4], [242, 507, 273, 162], [21, 22, 258, 508]], ![[398, 68, 331, 477], [288, 76, 462, 344], [494, 349, 442, 377], [283, 284, 310, 208], [325, 323, 128, 158], [54, 487, 222, 15], [389, 349, 405, 448], [22, 436, 331, 416], [219, 418, 429, 33]], ![[0, 1], [279, 152, 55, 311], [5, 9, 231, 72], [26, 100, 428, 205], [111, 13, 479, 124], [445, 481, 105, 437], [154, 295, 500, 118], [225, 75, 414, 439], [398, 68, 331, 477]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [464, 473, 388], []]
 b := ![[], [], [30, 335, 483, 343], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI509N0 : CertifiedPrimeIdeal' SI509N0 509 where
  n := 4
  hpos := by decide
  P := [474, 70, 33, 380, 1]
  hirr := P509P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![40555839094, 101608943296, -36697234548, -129580198884, -8522848624]
  a := ![7, 2, -24, 0, -23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![6526232926, 986606736, 2171639452, 431938300, -8522848624]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI509N0 : Ideal.IsPrime I509N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI509N0 B_one_repr
lemma NI509N0 : Nat.card (O ⧸ I509N0) = 67122964561 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI509N0

def I509N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-779, -2215, -2134, -1053, -369]] i)))

def SI509N1: IdealEqSpanCertificate' Table ![![-779, -2215, -2134, -1053, -369]] 
 ![![509, 0, 0, 0, 0], ![468, 1, 0, 0, 0], ![355, 0, 1, 0, 0], ![382, 0, 0, 1, 0], ![366, 0, 0, 0, 1]] where
  M :=![![![-779, -2215, -2134, -1053, -369], ![-2214, -6314, -6088, -3003, -1053], ![-6318, -18009, -17363, -8565, -3003], ![156, 444, 428, 211, 74], ![-5406, -15411, -14858, -7329, -2570]]]
  hmulB := by decide  
  f := ![![![413, 1235, -356, 81, -147]], ![![378, 1132, -326, 75, -135]], ![![289, 862, -249, 60, -102]], ![![310, 928, -268, 55, -110]], ![![300, 897, -256, 51, -110]]]
  g := ![![![4579, -2215, -2134, -1053, -369], ![13058, -6314, -6088, -3003, -1053], ![37243, -18009, -17363, -8565, -3003], ![-918, 444, 428, 211, 74], ![31870, -15411, -14858, -7329, -2570]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI509N1 : Nat.card (O ⧸ I509N1) = 509 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI509N1)

lemma isPrimeI509N1 : Ideal.IsPrime I509N1 := prime_ideal_of_norm_prime hp509.out _ NI509N1
def MulI509N0 : IdealMulLeCertificate' Table 
  ![![413, 1235, -356, 81, -147]] ![![-779, -2215, -2134, -1053, -369]]
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

def I521N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11963, -6470, 2851, -531, 1023]] i)))

def SI521N0: IdealEqSpanCertificate' Table ![![-11963, -6470, 2851, -531, 1023]] 
 ![![521, 0, 0, 0, 0], ![0, 521, 0, 0, 0], ![0, 0, 521, 0, 0], ![421, 170, 262, 1, 0], ![79, 443, 425, 0, 1]] where
  M :=![![![-11963, -6470, 2851, -531, 1023], ![6138, 3382, -1478, 285, -531], ![-3186, -1827, 787, -165, 285], ![1878, 1095, -467, 97, -170], ![1428, 786, -337, 93, -128]]]
  hmulB := by decide  
  f := ![![![5, 16, 15, 3, 3]], ![![18, 50, 46, 27, 3]], ![![18, 63, 149, 141, 27]], ![![19, 61, 102, 82, 17]], ![![31, 97, 163, 138, 25]]]
  g := ![![![251, -709, -562, -531, 1023], ![-138, 365, 287, 285, -531], ![84, -192, -148, -165, 285], ![-49, 115, 89, 97, -170], ![-53, 80, 57, 93, -128]]]
  hle1 := by decide   
  hle2 := by decide  


def P521P0 : CertificateIrreducibleZModOfList' 521 3 2 9 [366, 201, 26, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [205, 461, 165], [290, 59, 356], [0, 1]]
 g := ![![[203, 328, 505], [282, 180], [422, 393], [485, 340, 311], [177, 258], [351, 121], [108, 32], [495, 1], []], ![[445, 173, 384, 60], [406, 248], [427, 420], [54, 82, 214, 509], [67, 271], [150, 462], [347, 263], [388, 355], [187, 133]], ![[273, 340, 416, 179], [507, 25], [162, 127], [354, 423, 323, 181], [93, 479], [379, 10], [497, 266], [115, 474], [517, 133]]]
 h' := ![![[205, 461, 165], [140, 20, 102], [162, 150, 152], [151, 247, 262], [98, 86, 467], [354, 470, 193], [356, 230, 11], [138, 171, 475], [0, 0, 1], [0, 1]], ![[290, 59, 356], [150, 438, 461], [136, 122, 374], [480, 451, 466], [34, 470, 63], [344, 459, 367], [226, 413, 45], [496, 402, 493], [154, 108, 59], [205, 461, 165]], ![[0, 1], [466, 63, 479], [424, 249, 516], [63, 344, 314], [323, 486, 512], [388, 113, 482], [125, 399, 465], [444, 469, 74], [120, 413, 461], [290, 59, 356]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [398, 191], []]
 b := ![[], [489, 164, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI521N0 : CertifiedPrimeIdeal' SI521N0 521 where
  n := 3
  hpos := by decide
  P := [366, 201, 26, 1]
  hirr := P521P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1986330, -4525176, 2899602, 7981208, -1206272]
  a := ![1, 3, -8, -1, -9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6270210, -1587240, -3024014, 7981208, -1206272]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI521N0 : Ideal.IsPrime I521N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI521N0 B_one_repr
lemma NI521N0 : Nat.card (O ⧸ I521N0) = 141420761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI521N0

def I521N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![104023, 173858, -55220, 25248, -20922]] i)))

def SI521N1: IdealEqSpanCertificate' Table ![![104023, 173858, -55220, 25248, -20922]] 
 ![![521, 0, 0, 0, 0], ![201, 1, 0, 0, 0], ![237, 0, 1, 0, 0], ![278, 0, 0, 1, 0], ![419, 0, 0, 0, 1]] where
  M :=![![![104023, 173858, -55220, 25248, -20922], ![-125532, -209807, 66638, -30468, 25248], ![151488, 253188, -80417, 36768, -30468], ![-106212, -177516, 56382, -25781, 21362], ![-38976, -65142, 20692, -9456, 7837]]]
  hmulB := by decide  
  f := ![![![-139753, -74938, 32496, -6264, 11742]], ![![-53781, -28841, 12502, -2412, 4518]], ![![-63645, -34134, 14791, -2856, 5346]], ![![-74530, -39964, 17330, -3341, 6262]], ![![-112363, -60256, 26120, -5040, 9439]]]
  g := ![![![-38401, 173858, -55220, 25248, -20922], ![46341, -209807, 66638, -30468, 25248], ![-55923, 253188, -80417, 36768, -30468], ![39210, -177516, 56382, -25781, 21362], ![14387, -65142, 20692, -9456, 7837]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI521N1 : Nat.card (O ⧸ I521N1) = 521 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI521N1)

lemma isPrimeI521N1 : Ideal.IsPrime I521N1 := prime_ideal_of_norm_prime hp521.out _ NI521N1

def I521N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1715, 442, -283, -9, -97]] i)))

def SI521N2: IdealEqSpanCertificate' Table ![![1715, 442, -283, -9, -97]] 
 ![![521, 0, 0, 0, 0], ![314, 1, 0, 0, 0], ![394, 0, 1, 0, 0], ![371, 0, 0, 1, 0], ![154, 0, 0, 0, 1]] where
  M :=![![![1715, 442, -283, -9, -97], ![-582, 260, -10, 75, -9], ![-54, -717, 191, -123, 75], ![102, 537, -149, 89, -58], ![-96, 126, -23, 27, -10]]]
  hmulB := by decide  
  f := ![![![187, 520, 201, -123, -61]], ![![112, 312, 124, -69, -37]], ![![140, 389, 155, -87, -41]], ![![139, 385, 138, -106, -45]], ![![62, 176, 71, -33, -36]]]
  g := ![![![-14, 442, -283, -9, -97], ![-201, 260, -10, 75, -9], ![353, -717, 191, -123, 75], ![-257, 537, -149, 89, -58], ![-75, 126, -23, 27, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI521N2 : Nat.card (O ⧸ I521N2) = 521 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI521N2)

lemma isPrimeI521N2 : Ideal.IsPrime I521N2 := prime_ideal_of_norm_prime hp521.out _ NI521N2
def MulI521N0 : IdealMulLeCertificate' Table 
  ![![-11963, -6470, 2851, -531, 1023]] ![![104023, 173858, -55220, 25248, -20922]]
  ![![16183303, 27047754, -8590793, 3927927, -3254913]] where
 M := ![![![16183303, 27047754, -8590793, 3927927, -3254913]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI521N1 : IdealMulLeCertificate' Table 
  ![![16183303, 27047754, -8590793, 3927927, -3254913]] ![![1715, 442, -283, -9, -97]]
  ![![521, 0, 0, 0, 0]] where
 M := ![![![13189594841, 22044212308, -7001591876, 3201302214, -2652790288]]]
 hmul := by decide  
 g := ![![![![25315921, 42311348, -13438756, 6144534, -5091728]]]]
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

def I523N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![523, 0, 0, 0, 0]] i)))

def SI523N0: IdealEqSpanCertificate' Table ![![523, 0, 0, 0, 0]] 
 ![![523, 0, 0, 0, 0], ![0, 523, 0, 0, 0], ![0, 0, 523, 0, 0], ![0, 0, 0, 523, 0], ![0, 0, 0, 0, 523]] where
  M :=![![![523, 0, 0, 0, 0], ![0, 523, 0, 0, 0], ![0, 0, 523, 0, 0], ![0, 0, 0, 523, 0], ![0, 0, 0, 0, 523]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P523P0 : CertificateIrreducibleZModOfList' 523 5 2 9 [416, 149, 173, 349, 414, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [322, 475, 15, 335, 49], [248, 51, 399, 36, 106], [192, 289, 270, 323, 192], [393, 230, 362, 352, 176], [0, 1]]
 g := ![![[47, 83, 424, 168, 68], [331, 323, 232, 113, 501], [224, 492, 492, 109], [219, 342, 322, 278, 122], [327, 181, 70, 292], [495, 365, 142, 138], [184, 26, 109, 1], [], []], ![[432, 46, 27, 121, 113, 87, 201, 464], [517, 71, 44, 96, 236, 161, 238, 438], [208, 30, 159, 157], [340, 54, 86, 324, 403, 186, 508, 70], [59, 444, 279, 387], [423, 27, 442, 64], [36, 57, 449, 191], [389, 3, 161, 256], [279, 497, 90, 309]], ![[248, 391, 92, 5, 274, 452, 27, 103], [291, 303, 120, 201, 261, 419, 133, 82], [461, 196, 341, 371], [426, 148, 245, 479, 25, 396, 79, 314], [46, 493, 57, 284], [31, 167, 137, 19], [161, 126, 275, 10], [265, 205, 280, 157], [191, 209, 168, 253]], ![[155, 344, 82, 448, 61, 347, 44, 314], [447, 421, 148, 109, 338, 264, 368, 390], [379, 238, 344, 63], [264, 291, 288, 226, 517, 260, 147, 5], [228, 168, 161, 252], [9, 208, 234, 341], [412, 242, 112, 161], [23, 429, 135, 195], [449, 121, 48, 254]], ![[290, 413, 141, 481, 30, 6, 190, 490], [391, 12, 183, 181, 111, 262, 269, 195], [469, 269, 413, 137], [137, 473, 133, 130, 109, 299, 198, 339], [200, 298, 272, 436], [438, 484, 8, 130], [234, 10, 237, 252], [4, 271, 146, 341], [331, 351, 372, 119]]]
 h' := ![![[322, 475, 15, 335, 49], [376, 282, 397, 390, 157], [377, 312, 46, 456, 32], [421, 257, 81, 76, 307], [232, 433, 126, 423, 222], [220, 183, 15, 242, 412], [337, 470, 15, 401, 344], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[248, 51, 399, 36, 106], [151, 440, 425, 497, 354], [397, 22, 464, 500, 378], [197, 198, 74, 471, 334], [435, 309, 380, 130, 109], [38, 403, 166, 454, 99], [156, 303, 186, 180, 8], [79, 368, 383, 371, 387], [172, 47, 213, 393, 507], [322, 475, 15, 335, 49]], ![[192, 289, 270, 323, 192], [97, 170, 144, 420, 359], [449, 338, 169, 114, 237], [303, 182, 35, 180, 246], [385, 180, 419, 175, 204], [167, 300, 200, 31, 303], [281, 258, 495, 104, 217], [248, 318, 10, 398, 202], [353, 372, 12, 140, 334], [248, 51, 399, 36, 106]], ![[393, 230, 362, 352, 176], [83, 93, 138, 350, 15], [174, 227, 12, 39, 352], [320, 258, 141, 30, 423], [508, 12, 113, 429, 448], [167, 430, 130, 318, 323], [487, 408, 310, 97, 276], [181, 313, 206, 349, 256], [181, 15, 399, 102, 481], [192, 289, 270, 323, 192]], ![[0, 1], [350, 61, 465, 435, 161], [301, 147, 355, 460, 47], [405, 151, 192, 289, 259], [121, 112, 8, 412, 63], [393, 253, 12, 1, 432], [437, 130, 40, 264, 201], [194, 47, 447, 451, 200], [17, 89, 421, 411, 247], [393, 230, 362, 352, 176]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25, 353, 144, 172], [], [], []]
 b := ![[], [135, 443, 348, 481, 274], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI523N0 : CertifiedPrimeIdeal' SI523N0 523 where
  n := 5
  hpos := by decide
  P := [416, 149, 173, 349, 414, 1]
  hirr := P523P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1153238962814, 2697152775148, -1547963710427, -4421672895609, 423959217517]
  a := ![3, 0, 7, 5, 8]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2205045818, 5157079876, -2959777649, -8454441483, 810629479]
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



lemma PB1556I10_primes (p : ℕ) :
  p ∈ Set.range ![467, 479, 487, 491, 499, 503, 509, 521, 523] ↔ Nat.Prime p ∧ 463 < p ∧ p ≤ 523 := by
  rw [← List.mem_ofFn']
  convert primes_range 463 523 (by omega)

def PB1556I10 : PrimesBelowBoundCertificateInterval O 463 523 1556 where
  m := 9
  g := ![3, 2, 2, 3, 3, 2, 2, 3, 1]
  P := ![467, 479, 487, 491, 499, 503, 509, 521, 523]
  hP := PB1556I10_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I467N0, I467N1, I467N2]
    · exact ![I479N0, I479N1]
    · exact ![I487N0, I487N1]
    · exact ![I491N0, I491N1, I491N2]
    · exact ![I499N0, I499N1, I499N2]
    · exact ![I503N0, I503N1]
    · exact ![I509N0, I509N1]
    · exact ![I521N0, I521N1, I521N2]
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
    · exact ![218089, 218089, 467]
    · exact ![109902239, 229441]
    · exact ![115501303, 237169]
    · exact ![118370771, 491, 491]
    · exact ![249001, 249001, 499]
    · exact ![127263527, 253009]
    · exact ![67122964561, 509]
    · exact ![141420761, 521, 521]
    · exact ![39129873538843]
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
    · dsimp ; intro j
      fin_cases j
      exact NI487N0
      exact NI487N1
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
  β := ![I467N2, I491N1, I491N2, I499N2, I509N1, I521N1, I521N2]
  Il := ![[I467N2], [], [], [I491N1, I491N2], [I499N2], [], [I509N1], [I521N1, I521N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
