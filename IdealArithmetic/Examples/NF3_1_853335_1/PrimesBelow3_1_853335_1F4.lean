
import IdealArithmetic.Examples.NF3_1_853335_1.RI3_1_853335_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![-68, 93, 1]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![197, 0, 0], ![-68, 93, 1]] 
 ![![197, 0, 0], ![0, 197, 0], ![129, 93, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![-68, 93, 1], ![738, -343, 1119], ![16832, 388, 216]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-129, -93, 197]], ![![-1, 0, 1], ![-729, -530, 1119], ![-56, -100, 216]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 2 2 7 [139, 80, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [117, 196], [0, 1]]
 g := ![![[19, 168], [137], [132, 138], [65], [70], [76], [117, 1]], ![[172, 29], [137], [124, 59], [65], [70], [76], [37, 196]]]
 h' := ![![[117, 196], [7, 103], [170, 149], [12, 170], [24, 38], [135, 142], [88, 154], [0, 1]], ![[0, 1], [41, 94], [70, 48], [5, 27], [136, 159], [4, 55], [179, 43], [117, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [43, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 2
  hpos := by decide
  P := [139, 80, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1066, 599, -288]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![194, 139, -288]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![63, 1, 0]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![197, 0, 0], ![63, 1, 0]] 
 ![![197, 0, 0], ![63, 1, 0], ![178, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![63, 1, 0], ![6, 60, 12], ![180, 4, 66]]]
  hmulB := by decide  
  f := ![![![83770, 938959, 187824], ![31717, -3083444, 0]], ![![26754, 300248, 60060], ![10245, -985985, 0]], ![![75722, 848400, 169709], ![28560, -2786056, 0]]]
  g := ![![![1, 0, 0], ![-63, 197, 0], ![-178, 0, 197]], ![![0, 1, 0], ![-30, 60, 12], ![-60, 4, 66]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![197, 0, 0], ![-68, 93, 1]] ![![197, 0, 0], ![63, 1, 0]]
  ![![197, 0, 0]] where
 M := ![![![38809, 0, 0], ![12411, 197, 0]], ![![-13396, 18321, 197], ![-3546, 5516, 1182]]]
 hmul := by decide  
 g := ![![![![197, 0, 0]], ![![63, 1, 0]]], ![![![-68, 93, 1]], ![![-18, 28, 6]]]]
 hle2 := by decide  


def PBC197 : ContainsPrimesAboveP 197 ![I197N0, I197N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
    exact isPrimeI197N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 197 (by decide) (𝕀 ⊙ MulI197N0)
instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![41, 21, 1]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![199, 0, 0], ![41, 21, 1]] 
 ![![199, 0, 0], ![0, 199, 0], ![41, 21, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![41, 21, 1], ![306, -18, 255], ![3872, 100, 109]]]
  hmulB := by decide  
  f := ![![![-40, -21, -1], ![199, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-41, -21, 199]], ![![0, 0, 1], ![-51, -27, 255], ![-3, -11, 109]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 2 2 7 [23, 128, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [71, 198], [0, 1]]
 g := ![![[144, 26], [29, 8], [188, 45], [62], [25], [58], [71, 1]], ![[0, 173], [0, 191], [0, 154], [62], [25], [58], [142, 198]]]
 h' := ![![[71, 198], [129, 15], [54, 159], [69, 170], [36, 96], [148, 194], [158, 43], [0, 1]], ![[0, 1], [0, 184], [0, 40], [0, 29], [86, 103], [191, 5], [27, 156], [71, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [92]]
 b := ![[], [158, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 2
  hpos := by decide
  P := [23, 128, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2582, 187, 1165]
  a := ![3, -3, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-253, -122, 1165]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 39601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![-56, 1, 0]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![199, 0, 0], ![-56, 1, 0]] 
 ![![199, 0, 0], ![143, 1, 0], ![90, 0, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![-56, 1, 0], ![6, -59, 12], ![180, 4, -53]]]
  hmulB := by decide  
  f := ![![![2783, -29555, 6012], ![-796, -99699, 0]], ![![1993, -21237, 4320], ![-596, -71640, 0]], ![![1282, -13367, 2719], ![-277, -45090, 0]]]
  g := ![![![1, 0, 0], ![-143, 199, 0], ![-90, 0, 199]], ![![-1, 1, 0], ![37, -59, 12], ![22, 4, -53]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![199, 0, 0], ![41, 21, 1]] ![![199, 0, 0], ![-56, 1, 0]]
  ![![199, 0, 0]] where
 M := ![![![39601, 0, 0], ![-11144, 199, 0]], ![![8159, 4179, 199], ![-1990, -1194, 199]]]
 hmul := by decide  
 g := ![![![![199, 0, 0]], ![![-56, 1, 0]]], ![![![41, 21, 1]], ![![-10, -6, 1]]]]
 hle2 := by decide  


def PBC199 : ContainsPrimesAboveP 199 ![I199N0, I199N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI199N0
    exact isPrimeI199N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 199 (by decide) (𝕀 ⊙ MulI199N0)
instance hp211 : Fact (Nat.Prime 211) := {out := by norm_num}

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![80, 57, 1]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![211, 0, 0], ![80, 57, 1]] 
 ![![211, 0, 0], ![0, 211, 0], ![80, 57, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![80, 57, 1], ![522, -87, 687], ![10352, 244, 256]]]
  hmulB := by decide  
  f := ![![![-79, -57, -1], ![211, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-80, -57, 211]], ![![0, 0, 1], ![-258, -186, 687], ![-48, -68, 256]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 2 2 7 [52, 129, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [82, 210], [0, 1]]
 g := ![![[39, 69], [121, 169], [185], [103], [2, 52], [70], [82, 1]], ![[0, 142], [53, 42], [185], [103], [46, 159], [70], [164, 210]]]
 h' := ![![[82, 210], [38, 51], [129, 13], [185, 117], [107, 37], [195, 120], [167, 131], [0, 1]], ![[0, 1], [0, 160], [140, 198], [73, 94], [187, 174], [118, 91], [148, 80], [82, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [93]]
 b := ![[], [98, 152]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 2
  hpos := by decide
  P := [52, 129, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![372890, 69164, 21462]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-6370, -5470, 21462]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![-54, 1, 0]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![211, 0, 0], ![-54, 1, 0]] 
 ![![211, 0, 0], ![157, 1, 0], ![166, 0, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![-54, 1, 0], ![6, -57, 12], ![180, 4, -51]]]
  hmulB := by decide  
  f := ![![![19657, -201068, 42336], ![-5908, -744408, 0]], ![![14617, -149604, 31500], ![-4430, -553875, 0]], ![![15454, -158186, 33307], ![-4690, -585648, 0]]]
  g := ![![![1, 0, 0], ![-157, 211, 0], ![-166, 0, 211]], ![![-1, 1, 0], ![33, -57, 12], ![38, 4, -51]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![211, 0, 0], ![80, 57, 1]] ![![211, 0, 0], ![-54, 1, 0]]
  ![![211, 0, 0]] where
 M := ![![![44521, 0, 0], ![-11394, 211, 0]], ![![16880, 12027, 211], ![-3798, -3165, 633]]]
 hmul := by decide  
 g := ![![![![211, 0, 0]], ![![-54, 1, 0]]], ![![![80, 57, 1]], ![![-18, -15, 3]]]]
 hle2 := by decide  


def PBC211 : ContainsPrimesAboveP 211 ![I211N0, I211N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI211N0
    exact isPrimeI211N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 211 (by decide) (𝕀 ⊙ MulI211N0)
instance hp223 : Fact (Nat.Prime 223) := {out := by norm_num}

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![223, 0, 0]] 
 ![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 3 2 7 [62, 143, 93, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [89, 87, 75], [41, 135, 148], [0, 1]]
 g := ![![[182, 80, 172], [81, 76, 63], [175, 3, 34], [136, 210, 143], [85, 59, 138], [65, 175], [1]], ![[31, 59, 126, 40], [211, 214, 208, 23], [174, 146, 61, 13], [31, 109, 79, 168], [214, 98, 210, 141], [211, 162], [59, 109, 138, 182]], ![[112, 6, 200, 146], [18, 123, 9, 31], [206, 207, 146, 94], [130, 201, 5, 179], [211, 211, 36, 169], [47, 203], [110, 210, 158, 41]]]
 h' := ![![[89, 87, 75], [107, 115, 194], [77, 191, 78], [42, 124, 82], [82, 51, 139], [37, 40, 19], [161, 80, 130], [0, 1]], ![[41, 135, 148], [144, 222, 27], [205, 37, 102], [89, 2, 77], [181, 61, 67], [205, 116, 213], [199, 140, 135], [89, 87, 75]], ![[0, 1], [176, 109, 2], [65, 218, 43], [100, 97, 64], [104, 111, 17], [61, 67, 214], [107, 3, 181], [41, 135, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [68, 38], []]
 b := ![[], [113, 166, 166], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 3
  hpos := by decide
  P := [62, 143, 93, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1966414, -16725, 50175]
  a := ![-4, 3, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-8818, -75, 225]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 11089567 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def PBC223 : ContainsPrimesAboveP 223 ![I223N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI223N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![223, 0, 0]]) timesTableT_eq_Table B_one_repr 223 (by decide) 𝕀

instance hp227 : Fact (Nat.Prime 227) := {out := by norm_num}

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![227, 0, 0]] 
 ![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 3 2 7 [89, 51, 63, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [134, 207, 210], [30, 19, 17], [0, 1]]
 g := ![![[24, 167, 104], [193, 213, 213], [90, 210], [121, 133], [145, 43], [5, 177, 110], [1]], ![[160, 43, 145, 166], [54, 220, 154, 63], [192, 185], [56, 36], [171, 171], [202, 166, 137, 112], [217, 92, 30, 81]], ![[25, 165, 33, 199], [75, 118, 26, 126], [71, 82], [177, 101], [176, 92], [115, 191, 132, 151], [39, 189, 11, 146]]]
 h' := ![![[134, 207, 210], [75, 77, 51], [27, 173, 126], [186, 132, 133], [115, 69, 157], [9, 85, 161], [138, 176, 164], [0, 1]], ![[30, 19, 17], [168, 57, 114], [57, 125, 134], [44, 47, 56], [179, 109, 221], [102, 119, 25], [113, 22, 124], [134, 207, 210]], ![[0, 1], [79, 93, 62], [94, 156, 194], [113, 48, 38], [138, 49, 76], [162, 23, 41], [148, 29, 166], [30, 19, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50, 213], []]
 b := ![[], [165, 194, 106], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 3
  hpos := by decide
  P := [89, 51, 63, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-558874, 681, -4086]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2462, 3, -18]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 11697083 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def PBC227 : ContainsPrimesAboveP 227 ![I227N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI227N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![227, 0, 0]]) timesTableT_eq_Table B_one_repr 227 (by decide) 𝕀

instance hp229 : Fact (Nat.Prime 229) := {out := by norm_num}

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0], ![90, 1, 0]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![229, 0, 0], ![90, 1, 0]] 
 ![![229, 0, 0], ![90, 1, 0], ![35, 0, 1]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]], ![![90, 1, 0], ![6, 87, 12], ![180, 4, 93]]]
  hmulB := by decide  
  f := ![![![-11705, -199729, -27552], ![-5267, 525784, 0]], ![![-4602, -78465, -10824], ![-2060, 206558, 0]], ![![-1855, -30527, -4211], ![-637, 80360, 0]]]
  g := ![![![1, 0, 0], ![-90, 229, 0], ![-35, 0, 229]], ![![0, 1, 0], ![-36, 87, 12], ![-15, 4, 93]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N0 : Nat.card (O ⧸ I229N0) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N0)

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := prime_ideal_of_norm_prime hp229.out _ NI229N0

def I229N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0], ![-65, 1, 0]] i)))

def SI229N1: IdealEqSpanCertificate' Table ![![229, 0, 0], ![-65, 1, 0]] 
 ![![229, 0, 0], ![164, 1, 0], ![52, 0, 1]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]], ![![-65, 1, 0], ![6, -68, 12], ![180, 4, -62]]]
  hmulB := by decide  
  f := ![![![125616, -1559735, 275280], ![-42365, -5253260, 0]], ![![89989, -1116972, 197136], ![-30227, -3762012, 0]], ![![28548, -354176, 62509], ![-9536, -1192880, 0]]]
  g := ![![![1, 0, 0], ![-164, 229, 0], ![-52, 0, 229]], ![![-1, 1, 0], ![46, -68, 12], ![12, 4, -62]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N1 : Nat.card (O ⧸ I229N1) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N1)

lemma isPrimeI229N1 : Ideal.IsPrime I229N1 := prime_ideal_of_norm_prime hp229.out _ NI229N1

def I229N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0], ![-25, 1, 0]] i)))

def SI229N2: IdealEqSpanCertificate' Table ![![229, 0, 0], ![-25, 1, 0]] 
 ![![229, 0, 0], ![204, 1, 0], ![133, 0, 1]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]], ![![-25, 1, 0], ![6, -28, 12], ![180, 4, -22]]]
  hmulB := by decide  
  f := ![![![164716, -779427, 334080], ![-21297, -6375360, 0]], ![![146726, -694317, 297600], ![-19006, -5679200, 0]], ![![95682, -452681, 194029], ![-12211, -3702720, 0]]]
  g := ![![![1, 0, 0], ![-204, 229, 0], ![-133, 0, 229]], ![![-1, 1, 0], ![18, -28, 12], ![10, 4, -22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N2 : Nat.card (O ⧸ I229N2) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N2)

lemma isPrimeI229N2 : Ideal.IsPrime I229N2 := prime_ideal_of_norm_prime hp229.out _ NI229N2
def MulI229N0 : IdealMulLeCertificate' Table 
  ![![229, 0, 0], ![90, 1, 0]] ![![229, 0, 0], ![-65, 1, 0]]
  ![![229, 0, 0], ![-29, 40, 1]] where
 M := ![![![52441, 0, 0], ![-14885, 229, 0]], ![![20610, 229, 0], ![-5844, 22, 12]]]
 hmul := by decide  
 g := ![![![![229, 0, 0], ![0, 0, 0]], ![![-36, -39, -1], ![229, 0, 0]]], ![![![90, 1, 0], ![0, 0, 0]], ![![-24, -2, 0], ![12, 0, 0]]]]
 hle2 := by decide  

def MulI229N1 : IdealMulLeCertificate' Table 
  ![![229, 0, 0], ![-29, 40, 1]] ![![229, 0, 0], ![-25, 1, 0]]
  ![![229, 0, 0]] where
 M := ![![![52441, 0, 0], ![-5725, 229, 0]], ![![-6641, 9160, 229], ![1145, -1145, 458]]]
 hmul := by decide  
 g := ![![![![229, 0, 0]], ![![-25, 1, 0]]], ![![![-29, 40, 1]], ![![5, -5, 2]]]]
 hle2 := by decide  


def PBC229 : ContainsPrimesAboveP 229 ![I229N0, I229N1, I229N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI229N0
    exact isPrimeI229N1
    exact isPrimeI229N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 229 (by decide) (𝕀 ⊙ MulI229N0 ⊙ MulI229N1)
instance hp233 : Fact (Nat.Prime 233) := {out := by norm_num}

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0], ![100, 1, 0]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![233, 0, 0], ![100, 1, 0]] 
 ![![233, 0, 0], ![100, 1, 0], ![163, 0, 1]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]], ![![100, 1, 0], ![6, 97, 12], ![180, 4, 103]]]
  hmulB := by decide  
  f := ![![![5463, 109306, 13524], ![3029, -262591, 0]], ![![2298, 46845, 5796], ![1399, -112539, 0]], ![![3793, 76467, 9461], ![2186, -183701, 0]]]
  g := ![![![1, 0, 0], ![-100, 233, 0], ![-163, 0, 233]], ![![0, 1, 0], ![-50, 97, 12], ![-73, 4, 103]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N0 : Nat.card (O ⧸ I233N0) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N0)

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := prime_ideal_of_norm_prime hp233.out _ NI233N0

def I233N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0], ![-96, 1, 0]] i)))

def SI233N1: IdealEqSpanCertificate' Table ![![233, 0, 0], ![-96, 1, 0]] 
 ![![233, 0, 0], ![137, 1, 0], ![24, 0, 1]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]], ![![-96, 1, 0], ![6, -99, 12], ![180, 4, -93]]]
  hmulB := by decide  
  f := ![![![83905, -1667773, 202176], ![-41707, -3925584, 0]], ![![49357, -980589, 118872], ![-24464, -2308098, 0]], ![![8664, -171788, 20825], ![-4244, -404352, 0]]]
  g := ![![![1, 0, 0], ![-137, 233, 0], ![-24, 0, 233]], ![![-1, 1, 0], ![57, -99, 12], ![8, 4, -93]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N1 : Nat.card (O ⧸ I233N1) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N1)

lemma isPrimeI233N1 : Ideal.IsPrime I233N1 := prime_ideal_of_norm_prime hp233.out _ NI233N1

def I233N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0], ![-4, 1, 0]] i)))

def SI233N2: IdealEqSpanCertificate' Table ![![233, 0, 0], ![-4, 1, 0]] 
 ![![233, 0, 0], ![229, 1, 0], ![37, 0, 1]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]], ![![-4, 1, 0], ![6, -7, 12], ![180, 4, -1]]]
  hmulB := by decide  
  f := ![![![7309, -8526, 14616], ![0, -283794, 0]], ![![7183, -8379, 14364], ![1, -278901, 0]], ![![1161, -1354, 2321], ![20, -45066, 0]]]
  g := ![![![1, 0, 0], ![-229, 233, 0], ![-37, 0, 233]], ![![-1, 1, 0], ![5, -7, 12], ![-3, 4, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N2 : Nat.card (O ⧸ I233N2) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N2)

lemma isPrimeI233N2 : Ideal.IsPrime I233N2 := prime_ideal_of_norm_prime hp233.out _ NI233N2
def MulI233N0 : IdealMulLeCertificate' Table 
  ![![233, 0, 0], ![100, 1, 0]] ![![233, 0, 0], ![-96, 1, 0]]
  ![![233, 0, 0], ![16, -97, 1]] where
 M := ![![![54289, 0, 0], ![-22368, 233, 0]], ![![23300, 233, 0], ![-9594, 1, 12]]]
 hmul := by decide  
 g := ![![![![217, 97, -1], ![233, 0, 0]], ![![-96, 1, 0], ![0, 0, 0]]], ![![![84, 98, -1], ![233, 0, 0]], ![![-42, 5, 0], ![12, 0, 0]]]]
 hle2 := by decide  

def MulI233N1 : IdealMulLeCertificate' Table 
  ![![233, 0, 0], ![16, -97, 1]] ![![233, 0, 0], ![-4, 1, 0]]
  ![![233, 0, 0]] where
 M := ![![![54289, 0, 0], ![-932, 233, 0]], ![![3728, -22601, 233], ![-466, 699, -1165]]]
 hmul := by decide  
 g := ![![![![233, 0, 0]], ![![-4, 1, 0]]], ![![![16, -97, 1]], ![![-2, 3, -5]]]]
 hle2 := by decide  


def PBC233 : ContainsPrimesAboveP 233 ![I233N0, I233N1, I233N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI233N0
    exact isPrimeI233N1
    exact isPrimeI233N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 233 (by decide) (𝕀 ⊙ MulI233N0 ⊙ MulI233N1)
instance hp239 : Fact (Nat.Prime 239) := {out := by norm_num}

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![239, 0, 0]] 
 ![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P0 : CertificateIrreducibleZModOfList' 239 3 2 7 [210, 168, 25, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [28, 70, 181], [186, 168, 58], [0, 1]]
 g := ![![[207, 6, 183], [50, 218, 68], [147, 178, 183], [39, 75, 1], [223, 132], [107, 184, 147], [1]], ![[212, 225, 83, 35], [200, 162, 90, 112], [184, 47, 234, 158], [222, 152, 192, 103], [103, 27], [153, 33, 162, 221], [152, 71, 5, 151]], ![[168, 136, 57, 6], [223, 185, 157, 68], [37, 224, 42, 133], [164, 106, 110, 196], [168, 68], [222, 14, 155, 109], [216, 85, 180, 88]]]
 h' := ![![[28, 70, 181], [16, 160, 30], [200, 97, 207], [175, 108, 209], [30, 50, 1], [235, 151, 128], [29, 71, 214], [0, 1]], ![[186, 168, 58], [236, 107, 62], [51, 108, 231], [50, 11, 168], [93, 79, 136], [149, 14, 79], [70, 153, 47], [28, 70, 181]], ![[0, 1], [164, 211, 147], [148, 34, 40], [163, 120, 101], [201, 110, 102], [78, 74, 32], [70, 15, 217], [186, 168, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [191, 36], []]
 b := ![[], [232, 95, 116], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 3
  hpos := by decide
  P := [210, 168, 25, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![274197530, 13775004, 12913648]
  a := ![22, -1, 43]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1147270, 57636, 54032]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N0 B_one_repr
lemma NI239N0 : Nat.card (O ⧸ I239N0) = 13651919 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N0

def PBC239 : ContainsPrimesAboveP 239 ![I239N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI239N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![239, 0, 0]]) timesTableT_eq_Table B_one_repr 239 (by decide) 𝕀

instance hp241 : Fact (Nat.Prime 241) := {out := by norm_num}

def I241N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0], ![-69, -10, 1]] i)))

def SI241N0: IdealEqSpanCertificate' Table ![![241, 0, 0], ![-69, -10, 1]] 
 ![![241, 0, 0], ![0, 241, 0], ![172, 231, 1]] where
  M :=![![![241, 0, 0], ![0, 241, 0], ![0, 0, 241]], ![![-69, -10, 1], ![120, -35, -117], ![-1708, -24, -94]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-172, -231, 241]], ![![-1, -1, 1], ![84, 112, -117], ![60, 90, -94]]]
  hle1 := by decide   
  hle2 := by decide  


def P241P0 : CertificateIrreducibleZModOfList' 241 2 2 7 [121, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [220, 240], [0, 1]]
 g := ![![[42, 2], [134], [49], [169], [227, 72], [15, 216], [220, 1]], ![[0, 239], [134], [49], [169], [161, 169], [58, 25], [199, 240]]]
 h' := ![![[220, 240], [20, 219], [91, 161], [85, 7], [7, 13], [113, 109], [131, 79], [0, 1]], ![[0, 1], [0, 22], [84, 80], [179, 234], [216, 228], [234, 132], [159, 162], [220, 240]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [129]]
 b := ![[], [135, 185]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 2
  hpos := by decide
  P := [121, 21, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![579, 42, 44]
  a := ![0, 1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-29, -42, 44]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI241N0 : Ideal.IsPrime I241N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI241N0 B_one_repr
lemma NI241N0 : Nat.card (O ⧸ I241N0) = 58081 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI241N0

def I241N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0], ![117, 1, 0]] i)))

def SI241N1: IdealEqSpanCertificate' Table ![![241, 0, 0], ![117, 1, 0]] 
 ![![241, 0, 0], ![117, 1, 0], ![94, 0, 1]] where
  M :=![![![241, 0, 0], ![0, 241, 0], ![0, 0, 241]], ![![117, 1, 0], ![6, 114, 12], ![180, 4, 120]]]
  hmulB := by decide  
  f := ![![![110551, 2700390, 284280], ![65070, -5709290, 0]], ![![53673, 1310869, 138000], ![31572, -2771500, 0]], ![![43102, 1053264, 110881], ![25416, -2226860, 0]]]
  g := ![![![1, 0, 0], ![-117, 241, 0], ![-94, 0, 241]], ![![0, 1, 0], ![-60, 114, 12], ![-48, 4, 120]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI241N1 : Nat.card (O ⧸ I241N1) = 241 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI241N1)

lemma isPrimeI241N1 : Ideal.IsPrime I241N1 := prime_ideal_of_norm_prime hp241.out _ NI241N1
def MulI241N0 : IdealMulLeCertificate' Table 
  ![![241, 0, 0], ![-69, -10, 1]] ![![241, 0, 0], ![117, 1, 0]]
  ![![241, 0, 0]] where
 M := ![![![58081, 0, 0], ![28197, 241, 0]], ![![-16629, -2410, 241], ![-7953, -1205, 0]]]
 hmul := by decide  
 g := ![![![![241, 0, 0]], ![![117, 1, 0]]], ![![![-69, -10, 1]], ![![-33, -5, 0]]]]
 hle2 := by decide  


def PBC241 : ContainsPrimesAboveP 241 ![I241N0, I241N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI241N0
    exact isPrimeI241N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 241 (by decide) (𝕀 ⊙ MulI241N0)
instance hp251 : Fact (Nat.Prime 251) := {out := by norm_num}

def I251N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![251, 0, 0]] i)))

def SI251N0: IdealEqSpanCertificate' Table ![![251, 0, 0]] 
 ![![251, 0, 0], ![0, 251, 0], ![0, 0, 251]] where
  M :=![![![251, 0, 0], ![0, 251, 0], ![0, 0, 251]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P251P0 : CertificateIrreducibleZModOfList' 251 3 2 7 [44, 63, 146, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 60, 29], [99, 190, 222], [0, 1]]
 g := ![![[171, 33, 179], [7, 242, 38], [163, 211], [106, 43, 7], [61, 40, 225], [187, 86, 232], [1]], ![[156, 188, 167, 203], [182, 131, 48, 199], [15, 7], [238, 143, 150, 145], [205, 18, 60, 234], [116, 189, 139, 129], [220, 174, 170, 42]], ![[74, 209, 65, 135], [215, 110, 216, 123], [10, 101], [17, 170, 242, 225], [11, 66, 230, 108], [133, 116, 247, 68], [219, 92, 68, 209]]]
 h' := ![![[6, 60, 29], [194, 169, 44], [88, 125, 234], [105, 120, 151], [77, 183, 42], [55, 176, 15], [207, 188, 105], [0, 1]], ![[99, 190, 222], [223, 102, 209], [129, 186, 144], [6, 99, 42], [18, 52, 235], [142, 167, 173], [74, 24, 51], [6, 60, 29]], ![[0, 1], [235, 231, 249], [75, 191, 124], [196, 32, 58], [209, 16, 225], [209, 159, 63], [86, 39, 95], [99, 190, 222]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [99, 89], []]
 b := ![[], [69, 223, 196], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI251N0 : CertifiedPrimeIdeal' SI251N0 251 where
  n := 3
  hpos := by decide
  P := [44, 63, 146, 1]
  hirr := P251P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3122942, 353408, 132528]
  a := ![5, -2, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![12442, 1408, 528]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI251N0 : Ideal.IsPrime I251N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI251N0 B_one_repr
lemma NI251N0 : Nat.card (O ⧸ I251N0) = 15813251 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI251N0

def PBC251 : ContainsPrimesAboveP 251 ![I251N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI251N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![251, 0, 0]]) timesTableT_eq_Table B_one_repr 251 (by decide) 𝕀

instance hp257 : Fact (Nat.Prime 257) := {out := by norm_num}

def I257N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![257, 0, 0]] i)))

def SI257N0: IdealEqSpanCertificate' Table ![![257, 0, 0]] 
 ![![257, 0, 0], ![0, 257, 0], ![0, 0, 257]] where
  M :=![![![257, 0, 0], ![0, 257, 0], ![0, 0, 257]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P257P0 : CertificateIrreducibleZModOfList' 257 3 2 8 [74, 95, 60, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 233, 179], [188, 23, 78], [0, 1]]
 g := ![![[177, 241, 165], [36, 35], [60, 165], [80, 46], [151, 1], [11, 168], [197, 1], []], ![[111, 49, 225, 149], [211, 169], [143, 225], [224, 13], [193, 67], [73, 226], [151, 15], [46, 173]], ![[197, 201, 112, 166], [66, 200], [48, 44], [173, 133], [3, 104], [234, 248], [159, 62], [147, 173]]]
 h' := ![![[9, 233, 179], [207, 240, 57], [185, 3, 99], [16, 102, 200], [252, 123, 139], [115, 23, 256], [71, 229, 164], [0, 0, 1], [0, 1]], ![[188, 23, 78], [52, 51, 67], [195, 106, 244], [165, 222, 242], [6, 73, 28], [47, 90, 239], [201, 240, 45], [18, 129, 23], [9, 233, 179]], ![[0, 1], [175, 223, 133], [144, 148, 171], [94, 190, 72], [139, 61, 90], [19, 144, 19], [87, 45, 48], [51, 128, 233], [188, 23, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [143, 57], []]
 b := ![[], [195, 77, 149], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N0 : CertifiedPrimeIdeal' SI257N0 257 where
  n := 3
  hpos := by decide
  P := [74, 95, 60, 1]
  hirr := P257P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-313026, 0, -12850]
  a := ![-5, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1218, 0, -50]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI257N0 : Ideal.IsPrime I257N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI257N0 B_one_repr
lemma NI257N0 : Nat.card (O ⧸ I257N0) = 16974593 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI257N0

def PBC257 : ContainsPrimesAboveP 257 ![I257N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI257N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![257, 0, 0]]) timesTableT_eq_Table B_one_repr 257 (by decide) 𝕀



lemma PB262I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 261 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 261 (by omega)

def PB262I4 : PrimesBelowBoundCertificateInterval O 193 261 262 where
  m := 11
  g := ![2, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1]
  P := ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257]
  hP := PB262I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1]
    · exact ![I199N0, I199N1]
    · exact ![I211N0, I211N1]
    · exact ![I223N0]
    · exact ![I227N0]
    · exact ![I229N0, I229N1, I229N2]
    · exact ![I233N0, I233N1, I233N2]
    · exact ![I239N0]
    · exact ![I241N0, I241N1]
    · exact ![I251N0]
    · exact ![I257N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC197
    · exact PBC199
    · exact PBC211
    · exact PBC223
    · exact PBC227
    · exact PBC229
    · exact PBC233
    · exact PBC239
    · exact PBC241
    · exact PBC251
    · exact PBC257
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![38809, 197]
    · exact ![39601, 199]
    · exact ![44521, 211]
    · exact ![11089567]
    · exact ![11697083]
    · exact ![229, 229, 229]
    · exact ![233, 233, 233]
    · exact ![13651919]
    · exact ![58081, 241]
    · exact ![15813251]
    · exact ![16974593]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
      exact NI197N1
    · dsimp ; intro j
      fin_cases j
      exact NI199N0
      exact NI199N1
    · dsimp ; intro j
      fin_cases j
      exact NI211N0
      exact NI211N1
    · dsimp ; intro j
      fin_cases j
      exact NI223N0
    · dsimp ; intro j
      fin_cases j
      exact NI227N0
    · dsimp ; intro j
      fin_cases j
      exact NI229N0
      exact NI229N1
      exact NI229N2
    · dsimp ; intro j
      fin_cases j
      exact NI233N0
      exact NI233N1
      exact NI233N2
    · dsimp ; intro j
      fin_cases j
      exact NI239N0
    · dsimp ; intro j
      fin_cases j
      exact NI241N0
      exact NI241N1
    · dsimp ; intro j
      fin_cases j
      exact NI251N0
    · dsimp ; intro j
      fin_cases j
      exact NI257N0
  β := ![I197N1, I199N1, I211N1, I229N0, I229N1, I229N2, I233N0, I233N1, I233N2, I241N1]
  Il := ![[I197N1], [I199N1], [I211N1], [], [], [I229N0, I229N1, I229N2], [I233N0, I233N1, I233N2], [], [I241N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
