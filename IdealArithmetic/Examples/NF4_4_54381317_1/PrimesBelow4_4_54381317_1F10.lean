
import IdealArithmetic.Examples.NF4_4_54381317_1.RI4_4_54381317_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic

set_option linter.all false

open Classical Polynomial

noncomputable section 
instance hp547 : Fact (Nat.Prime 547) := {out := by norm_num}
def I547N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![547, 0, 0, 0], ![112, -99, -4, 1]] i)))

def SI547N0: IdealEqSpanCertificate timesTableO I547N0
 ![![547, 0, 0, 0], ![112, -99, -4, 1]] 
 ![![547, 0, 0, 0], ![0, 547, 0, 0], ![365, 207, 1, 0], ![478, 182, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![547, 0, 0, 0], ![0, 547, 0, 0], ![0, 0, 547, 0], ![0, 0, 0, 547]], ![![112, -99, -4, 1], ![383, 444, -19, -3], ![-1149, -613, 204, -22], ![-8426, -8453, -2373, 182]]]
  hmulB := by decide
  f := ![![![699153, 809361, -34676, -5467], ![-2735, -997728, 0, 0]], ![![-174872, -202265, 8672, 1366], ![1094, 249432, 0, 0]], ![![400359, 463518, -19857, -3131], ![-1447, -571368, 0, 0]], ![![552762, 639980, -27416, -4323], ![-1958, -788880, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-365, -207, 547, 0], ![-478, -182, 0, 547]], ![![2, 1, -4, 1], ![16, 9, -19, -3], ![-119, -71, 204, -22], ![1409, 822, -2373, 182]]]
  hle1 := by decide
  hle2 := by decide

lemma NI547N0 : Nat.card (O ⧸ I547N0) = 299209 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI547N0)

def MemCI547N0 : IdealMemCertificate B I547N0
  ![![547, 0, 0, 0], ![0, 547, 0, 0], ![365, 207, 1, 0], ![478, 182, 0, 1]] ![33434, 29292, 7851, 251] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI547N0
 g := ![-5397, -3001, 7851, 251]
 hmem := by decide

def P547P0 : CertificateIrreducibleZModOfList' 547 2 2 9 [496, 409, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [138, 546], [0, 1]]
 g := ![![[421, 360], [204, 304], [195], [247], [196], [31, 6], [446], [446], [1]],![[324, 187], [37, 243], [195], [247], [196], [312, 541], [446], [446], [1]]]
 h' := ![![[138, 546], [11, 123], [264, 182], [240, 154], [468, 284], [487, 533], [83, 473], [185, 138], [51, 138], [0, 1]],![[0, 1], [28, 424], [218, 365], [159, 393], [276, 263], [196, 14], [264, 74], [84, 409], [497, 409], [138, 546]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [69]]
 b := ![[], [81, 308]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI547N0 : CertifiedPrimeIdeal O 547 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I547N0
  hcard := NI547N0
  P := [496, 409, 1]
  f := ofList [496, 409, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P547P0
  hneq := by decide
  hlen := by decide
  c := ![33434, 29292, 7851, 251]
  a := ![0, -1, -1, -1]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI547N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI547N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI547N0 : Ideal.IsPrime I547N0 := CertifiedPrimeIdeal.isPrime PI547N0
def I547N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![547, 0, 0, 0], ![-280, 179, -4, 1]] i)))

def SI547N1: IdealEqSpanCertificate timesTableO I547N1
 ![![547, 0, 0, 0], ![-280, 179, -4, 1]] 
 ![![547, 0, 0, 0], ![0, 547, 0, 0], ![492, 339, 1, 0], ![47, 441, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![547, 0, 0, 0], ![0, 547, 0, 0], ![0, 0, 547, 0], ![0, 0, 0, 547]], ![![-280, 179, -4, 1], ![383, 52, 259, -3], ![-1149, -613, -188, 256], ![98048, 83843, 19867, 68]]]
  hmulB := by decide
  f := ![![![21302714, 6433753, 17430433, -186334], ![-8926493, -36950397, 0, 0]], ![![-79539, -24253, -65279, 697], ![33914, 138391, 0, 0]], ![![19111341, 5771898, 15637372, -167166], ![-8008173, -33149325, 0, 0]], ![![1766137, 533342, 1445048, -15448], ![-739915, -3063324, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-492, -339, 547, 0], ![-47, -441, 0, 547]], ![![3, 2, -4, 1], ![-232, -158, 259, -3], ![145, -91, -188, 256], ![-17696, -12214, 19867, 68]]]
  hle1 := by decide
  hle2 := by decide

lemma NI547N1 : Nat.card (O ⧸ I547N1) = 299209 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI547N1)

def MemCI547N1 : IdealMemCertificate B I547N1
  ![![547, 0, 0, 0], ![0, 547, 0, 0], ![492, 339, 1, 0], ![47, 441, 0, 1]] ![1552451, 1298540, 262980, -5850] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI547N1
 g := ![-233197, -155890, 262980, -5850]
 hmem := by decide

def P547P1 : CertificateIrreducibleZModOfList' 547 2 2 9 [4, 311, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [236, 546], [0, 1]]
 g := ![![[488, 137], [244, 294], [444], [1], [216], [361, 517], [530], [449], [1]],![[0, 410], [159, 253], [444], [1], [216], [392, 30], [530], [449], [1]]]
 h' := ![![[236, 546], [118, 273], [166, 29], [322, 93], [202, 1], [197, 444], [244, 254], [408, 146], [543, 236], [0, 1]],![[0, 1], [0, 274], [446, 518], [390, 454], [438, 546], [504, 103], [18, 293], [403, 401], [445, 311], [236, 546]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [96]]
 b := ![[], [353, 48]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI547N1 : CertifiedPrimeIdeal O 547 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I547N1
  hcard := NI547N1
  P := [4, 311, 1]
  f := ofList [4, 311, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P547P1
  hneq := by decide
  hlen := by decide
  c := ![1552451, 1298540, 262980, -5850]
  a := ![-2, 3, -64, 1]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI547N1
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI547N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI547N1 : Ideal.IsPrime I547N1 := CertifiedPrimeIdeal.isPrime PI547N1
def MulI547N0 : IdealMulEqCertificate timesTableO (I547N0) I547N1
  ![![547, 0, 0, 0], ![112, -99, -4, 1]] ![![547, 0, 0, 0], ![-280, 179, -4, 1]]
  ![![547, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![299209, 0, 0, 0], ![-153160, 97913, -2188, 547]], ![![61264, -54153, -2188, 547], ![33367, 101195, -5470, -547]]]
 hmul := by decide
 f :=  ![![![![10964069823435140381618, 3311397924120055130784, 8971152594799474034171, -95902709454222212303], ![-4594478675014628074176, -19017754417285332691323, 0, 0]], ![![-2505382117797556, -99309168, 0, 0], ![0, 0, 0, 0]]]]
 g :=  ![![![![547, 0, 0, 0]], ![![-280, 179, -4, 1]]], ![![![112, -99, -4, 1]], ![![61, 185, -10, -1]]]]
 hle1 := by decide
 hle2 := by decide

def PBC547 : IsPrimesAboveP 547 ![I547N0, I547N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI547N0
    exact isPrimeI547N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI547N0, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp557 : Fact (Nat.Prime 557) := {out := by norm_num}
def I557N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![557, 0, 0, 0], ![27, -67, -4, 1]] i)))

def SI557N0: IdealEqSpanCertificate timesTableO I557N0
 ![![557, 0, 0, 0], ![27, -67, -4, 1]] 
 ![![557, 0, 0, 0], ![0, 557, 0, 0], ![464, 158, 1, 0], ![212, 8, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![557, 0, 0, 0], ![0, 557, 0, 0], ![0, 0, 557, 0], ![0, 0, 0, 557]], ![![27, -67, -4, 1], ![383, 359, 13, -3], ![-1149, -613, 119, 10], ![3830, 2171, 187, 129]]]
  hmulB := by decide
  f := ![![![25749141, 23865708, 859616, -198148], ![-1628668, -37332368, 0, 0]], ![![-54575, -50508, -1818, 419], ![3899, 79094, 0, 0]], ![![21434437, 19866609, 715573, -164945], ![-1355735, -31076700, 0, 0]], ![![9799612, 9082800, 327152, -75411], ![-619928, -14207952, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-464, -158, 557, 0], ![-212, -8, 0, 557]], ![![3, 1, -4, 1], ![-9, -3, 13, -3], ![-105, -35, 119, 10], ![-198, -51, 187, 129]]]
  hle1 := by decide
  hle2 := by decide

lemma NI557N0 : Nat.card (O ⧸ I557N0) = 310249 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI557N0)

def MemCI557N0 : IdealMemCertificate B I557N0
  ![![557, 0, 0, 0], ![0, 557, 0, 0], ![464, 158, 1, 0], ![212, 8, 0, 1]] ![274836, 239890, 62249, 2853] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI557N0
 g := ![-52448, -17268, 62249, 2853]
 hmem := by decide

def P557P0 : CertificateIrreducibleZModOfList' 557 2 2 9 [208, 367, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [190, 556], [0, 1]]
 g := ![![[58, 29], [384], [396, 71], [302, 6], [422], [221, 354], [385], [452], [1]],![[555, 528], [384], [518, 486], [328, 551], [422], [84, 203], [385], [452], [1]]]
 h' := ![![[190, 556], [504, 125], [68, 345], [125, 264], [331, 305], [263, 133], [454, 512], [492, 156], [349, 190], [0, 1]],![[0, 1], [303, 432], [449, 212], [155, 293], [353, 252], [468, 424], [259, 45], [54, 401], [244, 367], [190, 556]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [129]]
 b := ![[], [278, 343]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI557N0 : CertifiedPrimeIdeal O 557 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I557N0
  hcard := NI557N0
  P := [208, 367, 1]
  f := ofList [208, 367, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P557P0
  hneq := by decide
  hlen := by decide
  c := ![274836, 239890, 62249, 2853]
  a := ![-1, 1, 1, -3]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI557N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI557N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI557N0 : Ideal.IsPrime I557N0 := CertifiedPrimeIdeal.isPrime PI557N0
def I557N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![557, 0, 0, 0], ![114, 1, 0, 0]] i)))

def SI557N1: IdealEqSpanCertificate timesTableO I557N1
 ![![557, 0, 0, 0], ![114, 1, 0, 0]] 
 ![![557, 0, 0, 0], ![114, 1, 0, 0], ![372, 0, 1, 0], ![481, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![557, 0, 0, 0], ![0, 557, 0, 0], ![0, 0, 557, 0], ![0, 0, 0, 557]], ![![114, 1, 0, 0], ![0, 114, 1, 0], ![0, 0, 114, 1], ![383, 332, 80, 115]]]
  hmulB := by decide
  f := ![![![31921, -4052, 12321082, 108080], ![-155960, 21166, -60200560, 0]], ![![6498, -855, 2552224, 22388], ![-31748, 4456, -12470116, 0]], ![![21228, -2778, 8228722, 72182], ![-103716, 14483, -40205374, 0]], ![![27437, -3612, 10639928, 93333], ![-134052, 18824, -51986480, 0]]]
  g := ![![![1, 0, 0, 0], ![-114, 557, 0, 0], ![-372, 0, 557, 0], ![-481, 0, 0, 557]], ![![0, 1, 0, 0], ![-24, 114, 1, 0], ![-77, 0, 114, 1], ![-220, 332, 80, 115]]]
  hle1 := by decide
  hle2 := by decide

lemma NI557N1 : Nat.card (O ⧸ I557N1) = 557 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI557N1)

lemma isPrimeI557N1 : Ideal.IsPrime I557N1 := prime_ideal_of_norm_prime hp557.out _ NI557N1
def I557N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![557, 0, 0, 0], ![-273, 1, 0, 0]] i)))

def SI557N2: IdealEqSpanCertificate timesTableO I557N2
 ![![557, 0, 0, 0], ![-273, 1, 0, 0]] 
 ![![557, 0, 0, 0], ![284, 1, 0, 0], ![109, 0, 1, 0], ![236, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![557, 0, 0, 0], ![0, 557, 0, 0], ![0, 0, 557, 0], ![0, 0, 0, 557]], ![![-273, 1, 0, 0], ![0, -273, 1, 0], ![0, 0, -273, 1], ![383, 332, 80, -272]]]
  hmulB := by decide
  f := ![![![99100, 2094, 3177165, -11638], ![202191, 5013, 6482366, 0]], ![![50506, 1180, 1657651, -6072], ![103046, 2785, 3382104, 0]], ![![19790, 474, 621619, -2277], ![40377, 1115, 1268289, 0]], ![![42262, 798, 1346160, -4931], ![86226, 1944, 2746568, 0]]]
  g := ![![![1, 0, 0, 0], ![-284, 557, 0, 0], ![-109, 0, 557, 0], ![-236, 0, 0, 557]], ![![-1, 1, 0, 0], ![139, -273, 1, 0], ![53, 0, -273, 1], ![-69, 332, 80, -272]]]
  hle1 := by decide
  hle2 := by decide

lemma NI557N2 : Nat.card (O ⧸ I557N2) = 557 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI557N2)

lemma isPrimeI557N2 : Ideal.IsPrime I557N2 := prime_ideal_of_norm_prime hp557.out _ NI557N2
def MulI557N0 : IdealMulEqCertificate timesTableO (I557N0) I557N1
  ![![557, 0, 0, 0], ![27, -67, -4, 1]] ![![557, 0, 0, 0], ![114, 1, 0, 0]]
  ![![557, 0, 0, 0], ![-14363, -7279, -443, 111]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![310249, 0, 0, 0], ![63498, 557, 0, 0]], ![![15039, -37319, -2228, 557], ![3461, -7279, -443, 111]]]
 hmul := by decide
 f :=  ![![![![39701561160240177, -9694121110337777997, -88462396931294945, -30027972462649], ![-193980431338165575, 47366837174671179720, 16725595243278703, 0]], ![![-14581545803, 0, 0, 0], ![-187709, 0, 0, 0]]], ![![![-1023757262327472108, 249975733914696500451, 2281119901955002450, 774310983830826], ![5002041973370630811, -1221416542169008424652, -431291593999178212, 0]], ![![376004443540, 0, 0, 0], ![4840331, 0, 0, 0]]]]
 g :=  ![![![![557, 0, 0, 0], ![0, 0, 0, 0]], ![![114, 1, 0, 0], ![0, 0, 0, 0]]], ![![![14390, 7212, 439, -110], ![557, 0, 0, 0]], ![![32, 0, 0, 0], ![1, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI557N1 : IdealMulEqCertificate timesTableO (I557N0*I557N1) I557N2
  ![![557, 0, 0, 0], ![-14363, -7279, -443, 111]] ![![557, 0, 0, 0], ![-273, 1, 0, 0]]
  ![![557, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI557N0
 hI2 := rfl
 M :=  ![![![310249, 0, 0, 0], ![-152061, 557, 0, 0]], ![![-8000191, -4054403, -246751, 61827], ![3963612, 2009656, 122540, -30635]]]
 hmul := by decide
 f :=  ![![![![215719419536, 20503251767, 30161398431996, -110481615254], ![440126376227, 43442569122, 61538250299218, 0]], ![![84660, 0, 0, 0], ![0, 0, 0, 0]]]]
 g :=  ![![![![557, 0, 0, 0]], ![![-273, 1, 0, 0]]], ![![![-14363, -7279, -443, 111]], ![![7116, 3608, 220, -55]]]]
 hle1 := by decide
 hle2 := by decide

def PBC557 : IsPrimesAboveP 557 ![I557N0, I557N1, I557N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI557N0
    exact isPrimeI557N1
    exact isPrimeI557N2
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI557N1, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp563 : Fact (Nat.Prime 563) := {out := by norm_num}
def I563N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![359, 193, 13, -3]] i)))

def SI563N0: IdealEqSpanCertificate timesTableO I563N0
 ![![359, 193, 13, -3]] 
 ![![563, 0, 0, 0], ![0, 563, 0, 0], ![550, 203, 1, 0], ![387, 440, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![359, 193, 13, -3], ![-1149, -637, -47, 10], ![3830, 2171, 163, -37], ![-14171, -8454, -789, 126]]]
  hmulB := by decide
  f := ![![![567, 276, 15, -4]], ![![-1532, -761, -44, 11]], ![![9, -1, -1, 0]], ![![-830, -417, -25, 6]]]
  g := ![![![-10, -2, 13, -3], ![37, 8, -47, 10], ![-127, -26, 163, -37], ![659, 171, -789, 126]]]
  hle1 := by decide
  hle2 := by decide

lemma NI563N0 : Nat.card (O ⧸ I563N0) = 316969 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI563N0)

def MemCI563N0 : IdealMemCertificate B I563N0
  ![![563, 0, 0, 0], ![0, 563, 0, 0], ![550, 203, 1, 0], ![387, 440, 0, 1]] ![29952, 25172, 5951, 673] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI563N0
 g := ![-6223, -2627, 5951, 673]
 hmem := by decide

def P563P0 : CertificateIrreducibleZModOfList' 563 2 2 9 [78, 341, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [222, 562], [0, 1]]
 g := ![![[257, 334], [48, 508], [47], [149], [486, 236], [270, 59], [400], [303], [1]],![[89, 229], [224, 55], [47], [149], [519, 327], [419, 504], [400], [303], [1]]]
 h' := ![![[222, 562], [197, 254], [159, 251], [264, 114], [376, 49], [334, 133], [166, 348], [466, 543], [485, 222], [0, 1]],![[0, 1], [285, 309], [144, 312], [237, 449], [557, 514], [21, 430], [291, 215], [530, 20], [225, 341], [222, 562]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [63]]
 b := ![[], [163, 313]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI563N0 : CertifiedPrimeIdeal O 563 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I563N0
  hcard := NI563N0
  P := [78, 341, 1]
  f := ofList [78, 341, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P563P0
  hneq := by decide
  hlen := by decide
  c := ![29952, 25172, 5951, 673]
  a := ![0, -1, -1, 1]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI563N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI563N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI563N0 : Ideal.IsPrime I563N0 := CertifiedPrimeIdeal.isPrime PI563N0
def I563N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-567, -276, -15, 4]] i)))

def SI563N1: IdealEqSpanCertificate timesTableO I563N1
 ![![-567, -276, -15, 4]] 
 ![![563, 0, 0, 0], ![0, 563, 0, 0], ![246, 359, 1, 0], ![77, 292, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![-567, -276, -15, 4], ![1532, 761, 44, -11], ![-4213, -2120, -119, 33], ![12639, 6743, 520, -86]]]
  hmulB := by decide
  f := ![![![-359, -193, -13, 3]], ![![1149, 637, 47, -10]], ![![569, 318, 24, -5]], ![![572, 319, 24, -5]]]
  g := ![![![5, 7, -15, 4], ![-15, -21, 44, -11], ![40, 55, -119, 33], ![-193, -275, 520, -86]]]
  hle1 := by decide
  hle2 := by decide

lemma NI563N1 : Nat.card (O ⧸ I563N1) = 316969 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI563N1)

def MemCI563N1 : IdealMemCertificate B I563N1
  ![![563, 0, 0, 0], ![0, 563, 0, 0], ![246, 359, 1, 0], ![77, 292, 0, 1]] ![289197, 244025, 62328, 5504] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI563N1
 g := ![-27473, -42165, 62328, 5504]
 hmem := by decide

def P563P1 : CertificateIrreducibleZModOfList' 563 2 2 9 [164, 478, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [85, 562], [0, 1]]
 g := ![![[408, 339], [108, 141], [429], [399], [434, 466], [543, 308], [346], [469], [1]],![[510, 224], [270, 422], [429], [399], [71, 97], [262, 255], [346], [469], [1]]]
 h' := ![![[85, 562], [304, 232], [509, 282], [216, 100], [325, 472], [465, 62], [369, 172], [87, 162], [399, 85], [0, 1]],![[0, 1], [319, 331], [270, 281], [271, 463], [472, 91], [105, 501], [351, 391], [345, 401], [305, 478], [85, 562]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [557]]
 b := ![[], [409, 560]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI563N1 : CertifiedPrimeIdeal O 563 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I563N1
  hcard := NI563N1
  P := [164, 478, 1]
  f := ofList [164, 478, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P563P1
  hneq := by decide
  hlen := by decide
  c := ![289197, 244025, 62328, 5504]
  a := ![19, 1, -1, 3]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI563N1
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI563N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI563N1 : Ideal.IsPrime I563N1 := CertifiedPrimeIdeal.isPrime PI563N1
def MulI563N0 : IdealMulEqCertificate timesTableO (I563N0) I563N1
  ![![359, 193, 13, -3]] ![![-567, -276, -15, 4]]
  ![![563, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![-563, 0, 0, 0]]]
 hmul := by decide
 f :=  ![![![![-1, 0, 0, 0]]]]
 g :=  ![![![![-1, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def PBC563 : IsPrimesAboveP 563 ![I563N0, I563N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI563N0
    exact isPrimeI563N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI563N0, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp569 : Fact (Nat.Prime 569) := {out := by norm_num}
def I569N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![569, 0, 0, 0], ![131, -67, -4, 1]] i)))

def SI569N0: IdealEqSpanCertificate timesTableO I569N0
 ![![569, 0, 0, 0], ![131, -67, -4, 1]] 
 ![![569, 0, 0, 0], ![0, 569, 0, 0], ![207, 262, 1, 0], ![390, 412, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![569, 0, 0, 0], ![0, 569, 0, 0], ![0, 0, 569, 0], ![0, 0, 0, 569]], ![![131, -67, -4, 1], ![383, 463, 13, -3], ![-1149, -613, 223, 10], ![3830, 2171, 187, 233]]]
  hmulB := by decide
  f := ![![![10956978, 13609151, 385532, -89093], ![917797, -16592040, 0, 0]], ![![-30499, -37770, -1069, 247], ![-2276, 46089, 0, 0]], ![![3972057, 4933568, 139763, -32298], ![332868, -6014898, 0, 0]], ![![7488057, 9300497, 263472, -60886], ![627051, -11339028, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-207, -262, 569, 0], ![-390, -412, 0, 569]], ![![1, 1, -4, 1], ![-2, -3, 13, -3], ![-90, -111, 223, 10], ![-221, -251, 187, 233]]]
  hle1 := by decide
  hle2 := by decide

lemma NI569N0 : Nat.card (O ⧸ I569N0) = 323761 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI569N0)

def MemCI569N0 : IdealMemCertificate B I569N0
  ![![569, 0, 0, 0], ![0, 569, 0, 0], ![207, 262, 1, 0], ![390, 412, 0, 1]] ![126160, 112292, 30743, 2767] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI569N0
 g := ![-12859, -15962, 30743, 2767]
 hmem := by decide

def P569P0 : CertificateIrreducibleZModOfList' 569 2 2 9 [389, 237, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [332, 568], [0, 1]]
 g := ![![[103, 471], [63], [448], [159, 153], [318, 122], [123, 288], [130], [407], [1]],![[0, 98], [63], [448], [314, 416], [423, 447], [147, 281], [130], [407], [1]]]
 h' := ![![[332, 568], [443, 374], [292, 72], [170, 192], [340, 405], [518, 182], [190, 433], [395, 301], [180, 332], [0, 1]],![[0, 1], [0, 195], [298, 497], [186, 377], [516, 164], [59, 387], [558, 136], [183, 268], [18, 237], [332, 568]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [259]]
 b := ![[], [125, 414]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI569N0 : CertifiedPrimeIdeal O 569 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I569N0
  hcard := NI569N0
  P := [389, 237, 1]
  f := ofList [389, 237, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P569P0
  hneq := by decide
  hlen := by decide
  c := ![126160, 112292, 30743, 2767]
  a := ![-1, 0, 1, 2]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI569N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI569N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI569N0 : Ideal.IsPrime I569N0 := CertifiedPrimeIdeal.isPrime PI569N0
def I569N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![569, 0, 0, 0], ![-394, -67, -4, 1]] i)))

def SI569N1: IdealEqSpanCertificate timesTableO I569N1
 ![![569, 0, 0, 0], ![-394, -67, -4, 1]] 
 ![![569, 0, 0, 0], ![0, 569, 0, 0], ![339, 306, 1, 0], ![393, 19, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![569, 0, 0, 0], ![0, 569, 0, 0], ![0, 0, 569, 0], ![0, 0, 0, 569]], ![![-394, -67, -4, 1], ![383, -62, 13, -3], ![-1149, -613, -302, 10], ![3830, 2171, 187, -292]]]
  hmulB := by decide
  f := ![![![27440975, -8579258, 1227934, -280936], ![-17999746, -59284110, 0, 0]], ![![-90765, 28426, -4065, 930], ![59745, 196305, 0, 0]], ![![16300229, -5096047, 729397, -166877], ![-10691507, -35214840, 0, 0]], ![![18949916, -5924642, 847979, -194007], ![-12430361, -40940115, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-339, -306, 569, 0], ![-393, -19, 0, 569]], ![![1, 2, -4, 1], ![-5, -7, 13, -3], ![171, 161, -302, 10], ![97, -87, 187, -292]]]
  hle1 := by decide
  hle2 := by decide

lemma NI569N1 : Nat.card (O ⧸ I569N1) = 323761 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI569N1)

def MemCI569N1 : IdealMemCertificate B I569N1
  ![![569, 0, 0, 0], ![0, 569, 0, 0], ![339, 306, 1, 0], ![393, 19, 0, 1]] ![123231, 109100, 28780, 2344] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI569N1
 g := ![-18549, -15364, 28780, 2344]
 hmem := by decide

def P569P1 : CertificateIrreducibleZModOfList' 569 2 2 9 [94, 196, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [373, 568], [0, 1]]
 g := ![![[220, 262], [409], [169], [555, 431], [61, 301], [245, 320], [112], [293], [1]],![[78, 307], [409], [169], [291, 138], [241, 268], [115, 249], [112], [293], [1]]]
 h' := ![![[373, 568], [563, 444], [435, 523], [178, 13], [525, 217], [299, 94], [203, 263], [71, 473], [475, 373], [0, 1]],![[0, 1], [27, 125], [347, 46], [475, 556], [99, 352], [83, 475], [434, 306], [110, 96], [199, 196], [373, 568]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [192]]
 b := ![[], [304, 96]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI569N1 : CertifiedPrimeIdeal O 569 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I569N1
  hcard := NI569N1
  P := [94, 196, 1]
  f := ofList [94, 196, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P569P1
  hneq := by decide
  hlen := by decide
  c := ![123231, 109100, 28780, 2344]
  a := ![-5, 0, 0, 2]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI569N1
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI569N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI569N1 : Ideal.IsPrime I569N1 := CertifiedPrimeIdeal.isPrime PI569N1
def MulI569N0 : IdealMulEqCertificate timesTableO (I569N0) I569N1
  ![![569, 0, 0, 0], ![131, -67, -4, 1]] ![![569, 0, 0, 0], ![-394, -67, -4, 1]]
  ![![569, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![323761, 0, 0, 0], ![-224186, -38123, -2276, 569]], ![![74539, -38123, -2276, 569], ![-68849, 0, 0, 0]]]
 hmul := by decide
 f :=  ![![![![169992035959233, -53147662791967, 7606883699654, -1740359919765], ![-111508148779029, -367257647717986, 0, 0]], ![![-28644, 0, 0, 0], ![0, 0, 0, 0]]]]
 g :=  ![![![![569, 0, 0, 0]], ![![-394, -67, -4, 1]]], ![![![131, -67, -4, 1]], ![![-121, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def PBC569 : IsPrimesAboveP 569 ![I569N0, I569N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI569N0
    exact isPrimeI569N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI569N0, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp571 : Fact (Nat.Prime 571) := {out := by norm_num}
def I571N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![571, 0, 0, 0]] i)))

def SI571N0: IdealEqSpanCertificate timesTableO I571N0
 ![![571, 0, 0, 0]] 
 ![![571, 0, 0, 0], ![0, 571, 0, 0], ![0, 0, 571, 0], ![0, 0, 0, 571]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![571, 0, 0, 0], ![0, 571, 0, 0], ![0, 0, 571, 0], ![0, 0, 0, 571]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0]], ![![0, 1, 0, 0]], ![![0, 0, 1, 0]], ![![0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI571N0 : Nat.card (O ⧸ I571N0) = 106302733681 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI571N0)

def MemCI571N0 : IdealMemCertificate B I571N0
  ![![571, 0, 0, 0], ![0, 571, 0, 0], ![0, 0, 571, 0], ![0, 0, 0, 571]] ![40284202457, 27106418356, 3083778573, -518666137] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI571N0
 g := ![70550267, 47471836, 5400663, -908347]
 hmem := by decide

def P571P0 : CertificateIrreducibleZModOfList' 571 4 2 9 [174, 288, 196, 324, 1] where
 m := 1
 P := ![2]
 exp := ![2] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 405, 138, 496], [201, 350, 407, 342], [12, 386, 26, 304], [0, 1]]
 g := ![![[72, 538, 549, 258], [170, 111, 410, 420], [26, 422, 299], [153, 91, 419, 236], [109, 356, 305, 511], [288, 101, 307, 245], [170, 208, 483], [1], []],![[310, 413, 476, 355, 328, 325], [176, 511, 226, 434, 460, 409], [513, 68, 366], [392, 548, 72, 337, 322, 6], [173, 203, 459, 39, 159, 207], [553, 193, 500, 184, 403, 25], [26, 523, 84], [293, 421, 409], [540, 559, 486]],![[563, 544, 295, 567, 282, 263], [427, 67, 185, 410, 264, 61], [17, 190, 216], [458, 21, 82, 48, 421, 383], [437, 382, 567, 260, 64, 44], [553, 528, 128, 554, 421, 403], [7, 85, 388], [237, 497, 285], [91, 103, 480]],![[489, 498, 274, 425, 489, 348], [533, 205, 46, 291, 97, 408], [517, 128, 126], [293, 360, 259, 559, 240, 546], [561, 35, 408, 429, 89, 491], [277, 194, 477, 216, 228, 165], [78, 548, 362], [300, 391, 105], [61, 276, 485]]]
 h' := ![![[34, 405, 138, 496], [112, 570, 400, 340], [18, 190, 170, 519], [215, 340, 402, 273], [448, 532, 392, 243], [136, 186, 341, 234], [125, 226, 152, 403], [397, 283, 375, 247], [0, 0, 1], [0, 1]],![[201, 350, 407, 342], [551, 39, 391, 431], [99, 110, 479, 5], [209, 5, 378, 450], [549, 109, 318, 259], [72, 368, 521, 520], [167, 123, 503, 498], [252, 369, 275, 93], [269, 299, 165, 235], [34, 405, 138, 496]],![[12, 386, 26, 304], [188, 291, 491, 455], [364, 175, 154, 393], [430, 535, 406, 521], [404, 165, 3, 319], [43, 420, 308, 49], [256, 405, 308, 490], [70, 282, 150, 406], [14, 71, 353, 362], [201, 350, 407, 342]],![[0, 1], [135, 242, 431, 487], [60, 96, 339, 225], [183, 262, 527, 469], [262, 336, 429, 321], [508, 168, 543, 339], [412, 388, 179, 322], [81, 208, 342, 396], [379, 201, 52, 545], [12, 386, 26, 304]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [460, 169, 166], []]
 b := ![[], [], [187, 492, 532, 467], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI571N0 : CertifiedPrimeIdeal O 571 where 
  r := 4
  n := 4
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I571N0
  hcard := NI571N0
  P := [174, 288, 196, 324, 1]
  f := ofList [174, 288, 196, 324, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P571P0
  hneq := by decide
  hlen := by decide
  c := ![40284202457, 27106418356, 3083778573, -518666137]
  a := ![-10, 2, 13, -1]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI571N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI571N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI571N0 : Ideal.IsPrime I571N0 := CertifiedPrimeIdeal.isPrime PI571N0
def PBC571 : IsPrimesAboveP 571 ![I571N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI571N0
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    unfold I571N0
    rw [Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp577 : Fact (Nat.Prime 577) := {out := by norm_num}
def I577N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![577, 0, 0, 0]] i)))

def SI577N0: IdealEqSpanCertificate timesTableO I577N0
 ![![577, 0, 0, 0]] 
 ![![577, 0, 0, 0], ![0, 577, 0, 0], ![0, 0, 577, 0], ![0, 0, 0, 577]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![577, 0, 0, 0], ![0, 577, 0, 0], ![0, 0, 577, 0], ![0, 0, 0, 577]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0]], ![![0, 1, 0, 0]], ![![0, 0, 1, 0]], ![![0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI577N0 : Nat.card (O ⧸ I577N0) = 110841719041 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI577N0)

def MemCI577N0 : IdealMemCertificate B I577N0
  ![![577, 0, 0, 0], ![0, 577, 0, 0], ![0, 0, 577, 0], ![0, 0, 0, 577]] ![126348385167, 120868695793, 37244007898, 3674015765] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI577N0
 g := ![218974671, 209477809, 64547674, 6367445]
 hmem := by decide

def P577P0 : CertificateIrreducibleZModOfList' 577 4 2 9 [298, 311, 43, 145, 1] where
 m := 1
 P := ![2]
 exp := ![2] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [282, 160, 50, 354], [356, 474, 22, 212], [371, 519, 505, 11], [0, 1]]
 g := ![![[274, 201, 521, 44], [3, 298, 54], [351, 532, 338], [112, 117, 298], [128, 191, 481], [332, 225, 453], [106, 510, 19, 253], [1], []],![[308, 559, 289, 236, 299, 362], [80, 568, 177], [183, 542, 545], [144, 524, 91], [282, 29, 574], [447, 389, 512], [549, 367, 337, 459, 43, 305], [311, 315, 16], [339, 267, 107]],![[186, 2, 543, 311, 155, 205], [492, 48, 114], [431, 411, 16], [29, 486, 11], [333, 143, 293], [429, 345, 293], [108, 142, 574, 382, 88, 427], [575, 127, 531], [266, 431, 515]],![[120, 452, 87, 117, 510, 425], [248, 87, 1], [539, 186, 477], [126, 245, 386], [406, 66, 16], [94, 152, 38], [342, 1, 5, 97, 185, 561], [90, 523, 204], [502, 489, 121]]]
 h' := ![![[282, 160, 50, 354], [292, 76, 328, 175], [136, 82, 362, 228], [451, 199, 363, 135], [19, 488, 474, 151], [568, 241, 94, 372], [147, 217, 370, 284], [279, 266, 534, 432], [0, 0, 1], [0, 1]],![[356, 474, 22, 212], [45, 432, 567, 459], [128, 147, 70, 480], [330, 534, 453, 198], [431, 302, 514, 317], [562, 202, 341, 150], [205, 27, 32, 544], [494, 160, 52, 321], [428, 450, 464, 573], [282, 160, 50, 354]],![[371, 519, 505, 11], [296, 100, 426, 534], [164, 46, 29, 445], [331, 371, 125, 4], [310, 366, 575, 201], [351, 323, 565, 51], [551, 422, 171, 51], [78, 386, 502, 57], [154, 538, 245, 115], [356, 474, 22, 212]],![[0, 1], [336, 546, 410, 563], [546, 302, 116, 1], [116, 50, 213, 240], [500, 575, 168, 485], [310, 388, 154, 4], [7, 488, 4, 275], [1, 342, 66, 344], [162, 166, 444, 466], [371, 519, 505, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [52, 411, 111], []]
 b := ![[], [], [91, 548, 22, 454], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI577N0 : CertifiedPrimeIdeal O 577 where 
  r := 4
  n := 4
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I577N0
  hcard := NI577N0
  P := [298, 311, 43, 145, 1]
  f := ofList [298, 311, 43, 145, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P577P0
  hneq := by decide
  hlen := by decide
  c := ![126348385167, 120868695793, 37244007898, 3674015765]
  a := ![1, 1, -4, -1]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI577N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI577N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI577N0 : Ideal.IsPrime I577N0 := CertifiedPrimeIdeal.isPrime PI577N0
def PBC577 : IsPrimesAboveP 577 ![I577N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI577N0
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    unfold I577N0
    rw [Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp587 : Fact (Nat.Prime 587) := {out := by norm_num}
def I587N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![587, 0, 0, 0], ![92, -67, -4, 1]] i)))

def SI587N0: IdealEqSpanCertificate timesTableO I587N0
 ![![587, 0, 0, 0], ![92, -67, -4, 1]] 
 ![![587, 0, 0, 0], ![0, 587, 0, 0], ![72, 223, 1, 0], ![380, 238, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![587, 0, 0, 0], ![0, 587, 0, 0], ![0, 0, 587, 0], ![0, 0, 0, 587]], ![![92, -67, -4, 1], ![383, 424, 13, -3], ![-1149, -613, 184, 10], ![3830, 2171, 187, 194]]]
  hmulB := by decide
  f := ![![![91863105, 102467807, 3150584, -727409], ![2679655, -141436476, 0, 0]], ![![-221894, -247504, -7610, 1757], ![-6457, 341634, 0, 0]], ![![11183386, 12474444, 383553, -88555], ![326375, -17218470, 0, 0]], ![![59378456, 66233172, 2036476, -470183], ![1732250, -91421724, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-72, -223, 587, 0], ![-380, -238, 0, 587]], ![![0, 1, -4, 1], ![1, -3, 13, -3], ![-31, -75, 184, 10], ![-142, -146, 187, 194]]]
  hle1 := by decide
  hle2 := by decide

lemma NI587N0 : Nat.card (O ⧸ I587N0) = 344569 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI587N0)

def MemCI587N0 : IdealMemCertificate B I587N0
  ![![587, 0, 0, 0], ![0, 587, 0, 0], ![72, 223, 1, 0], ![380, 238, 0, 1]] ![30543, 27270, 6183, 761] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI587N0
 g := ![-1199, -2611, 6183, 761]
 hmem := by decide

def P587P0 : CertificateIrreducibleZModOfList' 587 2 2 9 [433, 435, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [152, 586], [0, 1]]
 g := ![![[527, 38], [9, 205], [167], [187, 137], [116], [68], [498, 70], [211], [1]],![[433, 549], [58, 382], [167], [466, 450], [116], [68], [572, 517], [211], [1]]]
 h' := ![![[152, 586], [212, 25], [528, 458], [35, 298], [200, 170], [254, 65], [382, 393], [445, 230], [154, 152], [0, 1]],![[0, 1], [490, 562], [291, 129], [132, 289], [212, 417], [155, 522], [244, 194], [185, 357], [365, 435], [152, 586]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [225]]
 b := ![[], [255, 406]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI587N0 : CertifiedPrimeIdeal O 587 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I587N0
  hcard := NI587N0
  P := [433, 435, 1]
  f := ofList [433, 435, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P587P0
  hneq := by decide
  hlen := by decide
  c := ![30543, 27270, 6183, 761]
  a := ![-3, 1, -1, 1]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI587N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI587N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI587N0 : Ideal.IsPrime I587N0 := CertifiedPrimeIdeal.isPrime PI587N0
def I587N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![587, 0, 0, 0], ![8, 1, 0, 0]] i)))

def SI587N1: IdealEqSpanCertificate timesTableO I587N1
 ![![587, 0, 0, 0], ![8, 1, 0, 0]] 
 ![![587, 0, 0, 0], ![8, 1, 0, 0], ![523, 0, 1, 0], ![512, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![587, 0, 0, 0], ![0, 587, 0, 0], ![0, 0, 587, 0], ![0, 0, 0, 587]], ![![8, 1, 0, 0], ![0, 8, 1, 0], ![0, 0, 8, 1], ![383, 332, 80, 9]]]
  hmulB := by decide
  f := ![![![2873, 335, 942453, 117807], ![-210733, 1761, -69152709, 0]], ![![24, -5, 14679, 1835], ![-1760, 587, -1077145, 0]], ![![2569, 297, 839693, 104962], ![-188435, 1762, -61612694, 0]], ![![2512, 290, 822037, 102755], ![-184254, 1753, -60317184, 0]]]
  g := ![![![1, 0, 0, 0], ![-8, 587, 0, 0], ![-523, 0, 587, 0], ![-512, 0, 0, 587]], ![![0, 1, 0, 0], ![-1, 8, 1, 0], ![-8, 0, 8, 1], ![-83, 332, 80, 9]]]
  hle1 := by decide
  hle2 := by decide

lemma NI587N1 : Nat.card (O ⧸ I587N1) = 587 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI587N1)

lemma isPrimeI587N1 : Ideal.IsPrime I587N1 := prime_ideal_of_norm_prime hp587.out _ NI587N1
def I587N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![587, 0, 0, 0], ![-232, 1, 0, 0]] i)))

def SI587N2: IdealEqSpanCertificate timesTableO I587N2
 ![![587, 0, 0, 0], ![-232, 1, 0, 0]] 
 ![![587, 0, 0, 0], ![355, 1, 0, 0], ![180, 0, 1, 0], ![83, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![587, 0, 0, 0], ![0, 587, 0, 0], ![0, 0, 587, 0], ![0, 0, 0, 587]], ![![-232, 1, 0, 0], ![0, -232, 1, 0], ![0, 0, -232, 1], ![383, 332, 80, -231]]]
  hmulB := by decide
  f := ![![![207641, -18315903, 89848, -47], ![525365, -46340128, 27589, 0]], ![![125281, -11076916, 54239, -28], ![316981, -28025141, 16436, 0]], ![![63660, -5616298, 27687, -15], ![161070, -14209508, 8805, 0]], ![![29393, -2589619, 12786, -7], ![74369, -6551862, 4110, 0]]]
  g := ![![![1, 0, 0, 0], ![-355, 587, 0, 0], ![-180, 0, 587, 0], ![-83, 0, 0, 587]], ![![-1, 1, 0, 0], ![140, -232, 1, 0], ![71, 0, -232, 1], ![-192, 332, 80, -231]]]
  hle1 := by decide
  hle2 := by decide

lemma NI587N2 : Nat.card (O ⧸ I587N2) = 587 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI587N2)

lemma isPrimeI587N2 : Ideal.IsPrime I587N2 := prime_ideal_of_norm_prime hp587.out _ NI587N2
def MulI587N0 : IdealMulEqCertificate timesTableO (I587N0) I587N1
  ![![587, 0, 0, 0], ![92, -67, -4, 1]] ![![587, 0, 0, 0], ![8, 1, 0, 0]]
  ![![587, 0, 0, 0], ![-642, -112, -19, 5]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![344569, 0, 0, 0], ![4696, 587, 0, 0]], ![![54004, -39329, -2348, 587], ![1119, -112, -19, 5]]]
 hmul := by decide
 f :=  ![![![![-12852550066703006022, -1590546985614009486, -703105282165881975826, -87888410625041521338], ![943055512865712209480, -1175300401094754811, 51590497006614275555571, 0]], ![![30285097472610, 0, 0, 0], ![-325785, 0, 0, 0]]], ![![![14056803092883200972, 1739577412320513660, 768984555880218866114, 96123343296929937128], ![-1031417546028814976690, 1285423221651270903, -56424402482175134838081, 0]], ![![-33122738259090, 0, 0, 0], ![356310, 0, 0, 0]]]]
 g :=  ![![![![587, 0, 0, 0], ![0, 0, 0, 0]], ![![8, 1, 0, 0], ![0, 0, 0, 0]]], ![![![92, -67, -4, 1], ![0, 0, 0, 0]], ![![3, 0, 0, 0], ![1, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI587N1 : IdealMulEqCertificate timesTableO (I587N0*I587N1) I587N2
  ![![587, 0, 0, 0], ![-642, -112, -19, 5]] ![![587, 0, 0, 0], ![-232, 1, 0, 0]]
  ![![587, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI587N0
 hI2 := rfl
 M :=  ![![![344569, 0, 0, 0], ![-136184, 587, 0, 0]], ![![-376854, -65744, -11153, 2935], ![150859, 27002, 4696, -1174]]]
 hmul := by decide
 f :=  ![![![![9182831362683, -811736415286141, 3972816373556, -2043634523], ![23234146471487, -2053732938066668, 1199613242961, 0]], ![![44408, 0, 0, 0], ![0, 0, 0, 0]]]]
 g :=  ![![![![587, 0, 0, 0]], ![![-232, 1, 0, 0]]], ![![![-642, -112, -19, 5]], ![![257, 46, 8, -2]]]]
 hle1 := by decide
 hle2 := by decide

def PBC587 : IsPrimesAboveP 587 ![I587N0, I587N1, I587N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI587N0
    exact isPrimeI587N1
    exact isPrimeI587N2
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI587N1, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp593 : Fact (Nat.Prime 593) := {out := by norm_num}
def I593N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-106, -67, -4, 1]] i)))

def SI593N0: IdealEqSpanCertificate timesTableO I593N0
 ![![-106, -67, -4, 1]] 
 ![![593, 0, 0, 0], ![0, 593, 0, 0], ![65, 25, 1, 0], ![154, 33, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![-106, -67, -4, 1], ![383, 226, 13, -3], ![-1149, -613, -14, 10], ![3830, 2171, 187, -4]]]
  hmulB := by decide
  f := ![![![157, 67, 4, -1]], ![![-383, -175, -13, 3]], ![![3, 1, 0, 0]], ![![13, 4, 0, 0]]]
  g := ![![![0, 0, -4, 1], ![0, 0, 13, -3], ![-3, -1, -14, 10], ![-13, -4, 187, -4]]]
  hle1 := by decide
  hle2 := by decide

lemma NI593N0 : Nat.card (O ⧸ I593N0) = 351649 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI593N0)

def MemCI593N0 : IdealMemCertificate B I593N0
  ![![593, 0, 0, 0], ![0, 593, 0, 0], ![65, 25, 1, 0], ![154, 33, 0, 1]] ![495020, 412628, 98642, 1873] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI593N0
 g := ![-10464, -3567, 98642, 1873]
 hmem := by decide

def P593P0 : CertificateIrreducibleZModOfList' 593 2 2 9 [196, 376, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [217, 592], [0, 1]]
 g := ![![[486, 118], [366], [425], [257], [536, 97], [282], [328, 74], [242], [1]],![[0, 475], [366], [425], [257], [237, 496], [282], [375, 519], [242], [1]]]
 h' := ![![[217, 592], [281, 466], [197, 510], [163, 248], [498, 364], [113, 169], [349, 153], [472, 65], [397, 217], [0, 1]],![[0, 1], [0, 127], [569, 83], [16, 345], [24, 229], [20, 424], [342, 440], [345, 528], [46, 376], [217, 592]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [372]]
 b := ![[], [574, 186]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI593N0 : CertifiedPrimeIdeal O 593 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I593N0
  hcard := NI593N0
  P := [196, 376, 1]
  f := ofList [196, 376, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P593P0
  hneq := by decide
  hlen := by decide
  c := ![495020, 412628, 98642, 1873]
  a := ![3, 0, 7, -4]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI593N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI593N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI593N0 : Ideal.IsPrime I593N0 := CertifiedPrimeIdeal.isPrime PI593N0
def I593N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![593, 0, 0, 0], ![216, 1, 0, 0]] i)))

def SI593N1: IdealEqSpanCertificate timesTableO I593N1
 ![![593, 0, 0, 0], ![216, 1, 0, 0]] 
 ![![593, 0, 0, 0], ![216, 1, 0, 0], ![191, 0, 1, 0], ![254, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![593, 0, 0, 0], ![0, 593, 0, 0], ![0, 0, 593, 0], ![0, 0, 0, 593]], ![![216, 1, 0, 0], ![0, 216, 1, 0], ![0, 0, 216, 1], ![383, 332, 80, 217]]]
  hmulB := by decide
  f := ![![![56809, -4936417, -25663, -13], ![-155959, 13553015, 7709, 0]], ![![20520, -1798105, -9405, -5], ![-56334, 4936725, 2965, 0]], ![![18007, -1590109, -8226, -4], ![-49435, 4365667, 2372, 0]], ![![24262, -2114449, -11086, -6], ![-66607, 5805254, 3559, 0]]]
  g := ![![![1, 0, 0, 0], ![-216, 593, 0, 0], ![-191, 0, 593, 0], ![-254, 0, 0, 593]], ![![0, 1, 0, 0], ![-79, 216, 1, 0], ![-70, 0, 216, 1], ![-239, 332, 80, 217]]]
  hle1 := by decide
  hle2 := by decide

lemma NI593N1 : Nat.card (O ⧸ I593N1) = 593 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI593N1)

lemma isPrimeI593N1 : Ideal.IsPrime I593N1 := prime_ideal_of_norm_prime hp593.out _ NI593N1
def I593N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![593, 0, 0, 0], ![-242, 1, 0, 0]] i)))

def SI593N2: IdealEqSpanCertificate timesTableO I593N2
 ![![593, 0, 0, 0], ![-242, 1, 0, 0]] 
 ![![593, 0, 0, 0], ![351, 1, 0, 0], ![143, 0, 1, 0], ![212, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![593, 0, 0, 0], ![0, 593, 0, 0], ![0, 0, 593, 0], ![0, 0, 0, 593]], ![![-242, 1, 0, 0], ![0, -242, 1, 0], ![0, 0, -242, 1], ![383, 332, 80, -241]]]
  hmulB := by decide
  f := ![![![90993, 5190, 9281161, -38352], ![222968, 13639, 22742736, 0]], ![![53967, 3165, 5529202, -22848], ![132240, 8302, 13548864, 0]], ![![22363, 1360, 2238010, -9248], ![54798, 3559, 5484064, 0]], ![![32612, 1900, 3318054, -13711], ![79912, 4986, 8130624, 0]]]
  g := ![![![1, 0, 0, 0], ![-351, 593, 0, 0], ![-143, 0, 593, 0], ![-212, 0, 0, 593]], ![![-1, 1, 0, 0], ![143, -242, 1, 0], ![58, 0, -242, 1], ![-129, 332, 80, -241]]]
  hle1 := by decide
  hle2 := by decide

lemma NI593N2 : Nat.card (O ⧸ I593N2) = 593 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI593N2)

lemma isPrimeI593N2 : Ideal.IsPrime I593N2 := prime_ideal_of_norm_prime hp593.out _ NI593N2
def MulI593N0 : IdealMulEqCertificate timesTableO (I593N0) I593N1
  ![![-106, -67, -4, 1]] ![![593, 0, 0, 0], ![216, 1, 0, 0]]
  ![![593, 0, 0, 0], ![-27850, -14246, -851, 213]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![-62858, -39731, -2372, 593], ![-22513, -14246, -851, 213]]]
 hmul := by decide
 f :=  ![![![![-6809970467751259, 12557617070174053236, 58137255463950795, -30384125], ![18695891145261559, -34475396381964624215, 18017786124, 0]]], ![![![321259154181166467, -592403367620970022518, -2742614759522025299, 1433365731], ![-881975363099220908, 1626370735993510752655, -849985878474, 0]]]]
 g :=  ![![![![27744, 14179, 847, -212], ![593, 0, 0, 0]], ![![9, 0, 0, 0], ![1, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI593N1 : IdealMulEqCertificate timesTableO (I593N0*I593N1) I593N2
  ![![593, 0, 0, 0], ![-27850, -14246, -851, 213]] ![![593, 0, 0, 0], ![-242, 1, 0, 0]]
  ![![593, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI593N0
 hI2 := rfl
 M :=  ![![![351649, 0, 0, 0], ![-143506, 593, 0, 0]], ![![-16515050, -8447878, -504643, 126309], ![6821279, 3490398, 208736, -52184]]]
 hmul := by decide
 f :=  ![![![![495910219701, 62522793196, 109811429016129, -453767379264], ![1215171564226, 158221197087, 269084031110352, 0]], ![![116400, 0, 0, 0], ![0, 0, 0, 0]]]]
 g :=  ![![![![593, 0, 0, 0]], ![![-242, 1, 0, 0]]], ![![![-27850, -14246, -851, 213]], ![![11503, 5886, 352, -88]]]]
 hle1 := by decide
 hle2 := by decide

def PBC593 : IsPrimesAboveP 593 ![I593N0, I593N1, I593N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI593N0
    exact isPrimeI593N1
    exact isPrimeI593N2
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI593N1, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp599 : Fact (Nat.Prime 599) := {out := by norm_num}
def I599N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![599, 0, 0, 0]] i)))

def SI599N0: IdealEqSpanCertificate timesTableO I599N0
 ![![599, 0, 0, 0]] 
 ![![599, 0, 0, 0], ![0, 599, 0, 0], ![0, 0, 599, 0], ![0, 0, 0, 599]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![599, 0, 0, 0], ![0, 599, 0, 0], ![0, 0, 599, 0], ![0, 0, 0, 599]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0]], ![![0, 1, 0, 0]], ![![0, 0, 1, 0]], ![![0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI599N0 : Nat.card (O ⧸ I599N0) = 128738157601 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI599N0)

def MemCI599N0 : IdealMemCertificate B I599N0
  ![![599, 0, 0, 0], ![0, 599, 0, 0], ![0, 0, 599, 0], ![0, 0, 0, 599]] ![18133653988, 16979164150, 5065517776, 474433757] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI599N0
 g := ![30273212, 28345850, 8456624, 792043]
 hmem := by decide

def P599P0 : CertificateIrreducibleZModOfList' 599 4 2 9 [406, 63, 115, 476, 1] where
 m := 1
 P := ![2]
 exp := ![2] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [541, 108, 312, 390], [148, 586, 328, 585], [33, 503, 558, 223], [0, 1]]
 g := ![![[428, 63, 52, 498], [19, 202, 20, 511], [580, 588, 355, 123], [303, 248, 355], [195, 174, 345, 24], [575, 415, 136], [160, 60, 236, 154], [1], []],![[284, 588, 26, 380, 359, 392], [498, 595, 322, 487, 509, 249], [50, 23, 501, 101, 205, 95], [296, 320, 85], [36, 538, 291, 243, 335, 12], [129, 562, 426], [0, 560, 77, 251, 329, 139], [154, 201, 322], [142, 498, 553]],![[580, 1, 20, 88, 22, 151], [301, 63, 31, 406, 106, 78], [411, 30, 567, 498, 428, 543], [267, 458, 179], [452, 149, 438, 527, 531, 30], [118, 257, 553], [166, 434, 252, 274, 318, 380], [465, 21, 53], [67, 548, 196]],![[91, 542, 572, 68, 341, 534], [279, 470, 11, 103, 423, 493], [315, 557, 533, 486, 205, 167], [554, 586, 380], [304, 491, 594, 508, 457, 573], [329, 475, 34], [11, 327, 587, 550, 447, 230], [237, 166, 134], [132, 561, 12]]]
 h' := ![![[541, 108, 312, 390], [73, 589, 167, 405], [526, 276, 374, 117], [597, 234, 108, 159], [497, 366, 34, 445], [104, 405, 371, 120], [331, 413, 248, 391], [193, 536, 484, 123], [0, 0, 1], [0, 1]],![[148, 586, 328, 585], [321, 397, 325, 34], [148, 484, 575, 150], [413, 598, 181, 180], [486, 98, 113, 525], [583, 35, 245, 488], [256, 10, 359, 103], [94, 96, 272, 287], [221, 364, 354, 221], [541, 108, 312, 390]],![[33, 503, 558, 223], [594, 584, 117, 65], [567, 249, 251, 196], [161, 414, 150, 597], [587, 544, 51, 417], [555, 29, 545, 586], [331, 358, 242, 209], [158, 521, 375, 12], [93, 58, 11, 467], [148, 586, 328, 585]],![[0, 1], [335, 227, 589, 95], [577, 189, 597, 136], [103, 551, 160, 262], [40, 190, 401, 410], [243, 130, 37, 4], [290, 417, 349, 495], [171, 45, 67, 177], [209, 177, 233, 510], [33, 503, 558, 223]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [477, 594, 418], []]
 b := ![[], [], [533, 367, 309, 201], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI599N0 : CertifiedPrimeIdeal O 599 where 
  r := 4
  n := 4
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I599N0
  hcard := NI599N0
  P := [406, 63, 115, 476, 1]
  f := ofList [406, 63, 115, 476, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P599P0
  hneq := by decide
  hlen := by decide
  c := ![18133653988, 16979164150, 5065517776, 474433757]
  a := ![0, 1, 1, -1]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI599N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI599N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI599N0 : Ideal.IsPrime I599N0 := CertifiedPrimeIdeal.isPrime PI599N0
def PBC599 : IsPrimesAboveP 599 ![I599N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI599N0
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    unfold I599N0
    rw [Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp601 : Fact (Nat.Prime 601) := {out := by norm_num}
def I601N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![601, 0, 0, 0]] i)))

def SI601N0: IdealEqSpanCertificate timesTableO I601N0
 ![![601, 0, 0, 0]] 
 ![![601, 0, 0, 0], ![0, 601, 0, 0], ![0, 0, 601, 0], ![0, 0, 0, 601]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![601, 0, 0, 0], ![0, 601, 0, 0], ![0, 0, 601, 0], ![0, 0, 0, 601]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0]], ![![0, 1, 0, 0]], ![![0, 0, 1, 0]], ![![0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI601N0 : Nat.card (O ⧸ I601N0) = 130466162401 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI601N0)

def MemCI601N0 : IdealMemCertificate B I601N0
  ![![601, 0, 0, 0], ![0, 601, 0, 0], ![0, 0, 601, 0], ![0, 0, 0, 601]] ![2072582757, 1913478224, 556391376, 49415422] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI601N0
 g := ![3448557, 3183824, 925776, 82222]
 hmem := by decide

def P601P0 : CertificateIrreducibleZModOfList' 601 4 2 9 [210, 577, 247, 559, 1] where
 m := 1
 P := ![2]
 exp := ![2] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [442, 51, 549, 474], [492, 340, 21, 137], [310, 209, 31, 591], [0, 1]]
 g := ![![[576, 529, 50, 89], [195, 17, 293], [533, 342, 578], [589, 305, 24, 225], [30, 185, 68, 549], [115, 458, 122], [521, 290, 452, 562], [1], []],![[408, 405, 92, 328, 28, 159], [600, 107, 211], [162, 122, 120], [61, 370, 182, 228, 48, 88], [484, 133, 169, 47, 487, 291], [2, 371, 294], [101, 160, 263, 12, 233, 29], [344, 127, 282], [362, 77, 503]],![[261, 122, 222, 377, 516, 79], [258, 261, 589], [371, 186, 207], [444, 374, 196, 452, 537, 492], [125, 69, 111, 294, 351, 580], [149, 597, 413], [233, 426, 308, 417, 573, 436], [245, 104, 120], [109, 131, 138]],![[457, 171, 573, 504, 337, 416], [443, 229, 207], [445, 134, 564], [464, 355, 166, 443, 572, 555], [100, 528, 391, 223, 549, 147], [594, 176, 555], [595, 98, 165, 543, 310, 360], [167, 135, 230], [438, 575, 100]]]
 h' := ![![[442, 51, 549, 474], [205, 321, 17, 139], [90, 226, 230, 377], [116, 530, 361, 433], [311, 254, 407, 15], [73, 512, 333, 386], [573, 512, 451, 284], [391, 24, 354, 42], [0, 0, 1], [0, 1]],![[492, 340, 21, 137], [226, 557, 195, 367], [4, 252, 128, 217], [140, 27, 553, 214], [443, 427, 424, 382], [526, 302, 484, 102], [197, 55, 405, 213], [598, 506, 289, 370], [346, 340, 231, 67], [442, 51, 549, 474]],![[310, 209, 31, 591], [267, 262, 174, 134], [87, 350, 269, 503], [91, 445, 11, 105], [84, 518, 483, 96], [561, 363, 232, 66], [497, 398, 377, 138], [56, 281, 49, 40], [410, 151, 567, 214], [492, 340, 21, 137]],![[0, 1], [264, 62, 215, 562], [198, 374, 575, 105], [294, 200, 277, 450], [382, 3, 489, 108], [435, 25, 153, 47], [564, 237, 570, 567], [145, 391, 510, 149], [514, 110, 403, 320], [310, 209, 31, 591]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [146, 154, 148], []]
 b := ![[], [], [171, 245, 379, 306], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI601N0 : CertifiedPrimeIdeal O 601 where 
  r := 4
  n := 4
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I601N0
  hcard := NI601N0
  P := [210, 577, 247, 559, 1]
  f := ofList [210, 577, 247, 559, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P601P0
  hneq := by decide
  hlen := by decide
  c := ![2072582757, 1913478224, 556391376, 49415422]
  a := ![-1, 3, 4, 0]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI601N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI601N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI601N0 : Ideal.IsPrime I601N0 := CertifiedPrimeIdeal.isPrime PI601N0
def PBC601 : IsPrimesAboveP 601 ![I601N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI601N0
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    unfold I601N0
    rw [Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl

