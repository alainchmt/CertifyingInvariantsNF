
import IdealArithmetic.Examples.NF3_1_680884_1.RI3_1_680884_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![-68, 76, 1]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![197, 0, 0], ![-68, 76, 1]] 
 ![![197, 0, 0], ![0, 197, 0], ![129, 76, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![-68, 76, 1], ![431, 5, 153], ![27194, 5762, 81]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-129, -76, 197]], ![![-1, 0, 1], ![-98, -59, 153], ![85, -2, 81]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 2 2 7 [56, 177, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [20, 196], [0, 1]]
 g := ![![[70, 1], [61], [158, 55], [142], [22], [136], [20, 1]], ![[90, 196], [61], [76, 142], [142], [22], [136], [40, 196]]]
 h' := ![![[20, 196], [25, 1], [17, 109], [134, 45], [3, 158], [168, 66], [62, 147], [0, 1]], ![[0, 1], [45, 196], [30, 88], [49, 152], [11, 39], [109, 131], [47, 50], [20, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [94]]
 b := ![[], [121, 47]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 2
  hpos := by decide
  P := [56, 177, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2157, 973, -52]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![45, 25, -52]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![44, 1, 0]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![197, 0, 0], ![44, 1, 0]] 
 ![![197, 0, 0], ![44, 1, 0], ![116, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![44, 1, 0], ![1, 44, 2], ![355, 73, 45]]]
  hmulB := by decide  
  f := ![![![-17456, -847443, -38522], ![-8077, 3794417, 0]], ![![-3905, -189235, -8602], ![-1772, 847297, 0]], ![![-10280, -499002, -22683], ![-4750, 2234276, 0]]]
  g := ![![![1, 0, 0], ![-44, 197, 0], ![-116, 0, 197]], ![![0, 1, 0], ![-11, 44, 2], ![-41, 73, 45]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![197, 0, 0], ![-68, 76, 1]] ![![197, 0, 0], ![44, 1, 0]]
  ![![197, 0, 0]] where
 M := ![![![38809, 0, 0], ![8668, 197, 0]], ![![-13396, 14972, 197], ![-2561, 3349, 197]]]
 hmul := by decide  
 g := ![![![![197, 0, 0]], ![![44, 1, 0]]], ![![![-68, 76, 1]], ![![-13, 17, 1]]]]
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

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![20, 1, 0]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![199, 0, 0], ![20, 1, 0]] 
 ![![199, 0, 0], ![20, 1, 0], ![99, 0, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![20, 1, 0], ![1, 20, 2], ![355, 73, 21]]]
  hmulB := by decide  
  f := ![![![181, 3999, 400], ![199, -39800, 0]], ![![0, 399, 40], ![200, -3980, 0]], ![![81, 1989, 199], ![189, -19800, 0]]]
  g := ![![![1, 0, 0], ![-20, 199, 0], ![-99, 0, 199]], ![![0, 1, 0], ![-3, 20, 2], ![-16, 73, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N0 : Nat.card (O ⧸ I199N0) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N0)

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := prime_ideal_of_norm_prime hp199.out _ NI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![67, 1, 0]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![199, 0, 0], ![67, 1, 0]] 
 ![![199, 0, 0], ![67, 1, 0], ![144, 0, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![67, 1, 0], ![1, 67, 2], ![355, 73, 68]]]
  hmulB := by decide  
  f := ![![![-3336, -277435, -8282], ![-2388, 824059, 0]], ![![-1126, -93394, -2788], ![-795, 277406, 0]], ![![-2415, -200757, -5993], ![-1725, 596304, 0]]]
  g := ![![![1, 0, 0], ![-67, 199, 0], ![-144, 0, 199]], ![![0, 1, 0], ![-24, 67, 2], ![-72, 73, 68]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1

def I199N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![-88, 1, 0]] i)))

def SI199N2: IdealEqSpanCertificate' Table ![![199, 0, 0], ![-88, 1, 0]] 
 ![![199, 0, 0], ![111, 1, 0], ![9, 0, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![-88, 1, 0], ![1, -88, 2], ![355, 73, -87]]]
  hmulB := by decide  
  f := ![![![-5951, 787038, -17888], ![6766, 1779856, 0]], ![![-3315, 438925, -9976], ![3782, 992612, 0]], ![![-209, 35594, -809], ![442, 80496, 0]]]
  g := ![![![1, 0, 0], ![-111, 199, 0], ![-9, 0, 199]], ![![-1, 1, 0], ![49, -88, 2], ![-35, 73, -87]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N2 : Nat.card (O ⧸ I199N2) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N2)

lemma isPrimeI199N2 : Ideal.IsPrime I199N2 := prime_ideal_of_norm_prime hp199.out _ NI199N2
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![199, 0, 0], ![20, 1, 0]] ![![199, 0, 0], ![67, 1, 0]]
  ![![199, 0, 0], ![-26, -56, 1]] where
 M := ![![![39601, 0, 0], ![13333, 199, 0]], ![![3980, 199, 0], ![1341, 87, 2]]]
 hmul := by decide  
 g := ![![![![199, 0, 0], ![0, 0, 0]], ![![67, 1, 0], ![0, 0, 0]]], ![![![20, 1, 0], ![0, 0, 0]], ![![7, 1, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI199N1 : IdealMulLeCertificate' Table 
  ![![199, 0, 0], ![-26, -56, 1]] ![![199, 0, 0], ![-88, 1, 0]]
  ![![199, 0, 0]] where
 M := ![![![39601, 0, 0], ![-17512, 199, 0]], ![![-5174, -11144, 199], ![2587, 4975, -199]]]
 hmul := by decide  
 g := ![![![![199, 0, 0]], ![![-88, 1, 0]]], ![![![-26, -56, 1]], ![![13, 25, -1]]]]
 hle2 := by decide  


def PBC199 : ContainsPrimesAboveP 199 ![I199N0, I199N1, I199N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI199N0
    exact isPrimeI199N1
    exact isPrimeI199N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 199 (by decide) (𝕀 ⊙ MulI199N0 ⊙ MulI199N1)
instance hp211 : Fact (Nat.Prime 211) := {out := by norm_num}

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![211, 0, 0]] 
 ![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 3 2 7 [10, 146, 110, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [79, 135, 7], [22, 75, 204], [0, 1]]
 g := ![![[182, 69, 196], [46, 100, 83], [60, 37], [203, 54], [70, 30, 30], [36, 73], [1]], ![[101, 22, 152, 186], [189, 16, 44, 159], [127, 123], [29, 51], [2, 109, 57, 124], [129, 144], [178, 105, 50, 132]], ![[6, 58, 119, 87], [199, 169], [198, 16], [194, 144], [73, 121, 67, 171], [47, 109], [32, 112, 14, 79]]]
 h' := ![![[79, 135, 7], [173, 64, 197], [87, 91, 111], [138, 25, 167], [144, 110, 73], [162, 99, 36], [201, 65, 101], [0, 1]], ![[22, 75, 204], [87, 208, 31], [208, 74, 100], [210, 205, 40], [17, 189, 126], [45, 172, 17], [51, 6, 12], [79, 135, 7]], ![[0, 1], [83, 150, 194], [40, 46], [200, 192, 4], [36, 123, 12], [73, 151, 158], [200, 140, 98], [22, 75, 204]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [167, 83], []]
 b := ![[], [59, 139, 169], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 3
  hpos := by decide
  P := [10, 146, 110, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7347864, 3548598, 866577]
  a := ![2, -2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![34824, 16818, 4107]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 9393931 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def PBC211 : ContainsPrimesAboveP 211 ![I211N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI211N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![211, 0, 0]]) timesTableT_eq_Table B_one_repr 211 (by decide) 𝕀

instance hp223 : Fact (Nat.Prime 223) := {out := by norm_num}

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![-158, -79, 1]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![223, 0, 0], ![-158, -79, 1]] 
 ![![223, 0, 0], ![0, 223, 0], ![65, 144, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![-158, -79, 1], ![276, -85, -157], ![-27831, -5553, -164]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-65, -144, 223]], ![![-1, -1, 1], ![47, 101, -157], ![-77, 81, -164]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 2 2 7 [124, 139, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [84, 222], [0, 1]]
 g := ![![[136, 9], [38, 196], [120, 126], [102, 210], [31, 169], [138], [84, 1]], ![[0, 214], [0, 27], [0, 97], [125, 13], [178, 54], [138], [168, 222]]]
 h' := ![![[84, 222], [194, 3], [61, 209], [63, 55], [170, 136], [47, 13], [65, 19], [0, 1]], ![[0, 1], [0, 220], [0, 14], [0, 168], [221, 87], [24, 210], [100, 204], [84, 222]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [175]]
 b := ![[], [116, 199]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 2
  hpos := by decide
  P := [124, 139, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![880639, 922557, 317264]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-88527, -200733, 317264]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 49729 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![-66, 1, 0]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![223, 0, 0], ![-66, 1, 0]] 
 ![![223, 0, 0], ![157, 1, 0], ![164, 0, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![-66, 1, 0], ![1, -66, 2], ![355, 73, -65]]]
  hmulB := by decide  
  f := ![![![-22643, 1781934, -54000], ![14718, 6021000, 0]], ![![-15905, 1254481, -38016], ![10482, 4238784, 0]], ![![-16612, 1310480, -39713], ![10960, 4428000, 0]]]
  g := ![![![1, 0, 0], ![-157, 223, 0], ![-164, 0, 223]], ![![-1, 1, 0], ![45, -66, 2], ![-2, 73, -65]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N1 : Nat.card (O ⧸ I223N1) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N1)

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := prime_ideal_of_norm_prime hp223.out _ NI223N1
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![223, 0, 0], ![-158, -79, 1]] ![![223, 0, 0], ![-66, 1, 0]]
  ![![223, 0, 0]] where
 M := ![![![49729, 0, 0], ![-14718, 223, 0]], ![![-35234, -17617, 223], ![10704, 5129, -223]]]
 hmul := by decide  
 g := ![![![![223, 0, 0]], ![![-66, 1, 0]]], ![![![-158, -79, 1]], ![![48, 23, -1]]]]
 hle2 := by decide  


def PBC223 : ContainsPrimesAboveP 223 ![I223N0, I223N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI223N0
    exact isPrimeI223N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 223 (by decide) (𝕀 ⊙ MulI223N0)
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


def P227P0 : CertificateIrreducibleZModOfList' 227 3 2 7 [171, 17, 54, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [142, 186, 118], [31, 40, 109], [0, 1]]
 g := ![![[189, 140, 69], [160, 207, 81], [136, 132], [202, 169], [137, 222], [202, 94, 192], [1]], ![[224, 15, 134, 125], [27, 68, 170, 216], [82, 90], [22, 28], [127, 53], [75, 57, 226, 198], [195, 139, 193, 6]], ![[226, 204, 151, 177], [141, 100, 156, 131], [178, 113], [179, 78], [21, 71], [84, 170, 121, 10], [150, 160, 30, 221]]]
 h' := ![![[142, 186, 118], [107, 1, 117], [45, 86, 218], [123, 0, 86], [36, 200, 214], [189, 199, 201], [56, 210, 173], [0, 1]], ![[31, 40, 109], [50, 196, 31], [154, 210, 27], [130, 116, 35], [184, 97, 153], [91, 36, 196], [161, 186, 147], [142, 186, 118]], ![[0, 1], [209, 30, 79], [226, 158, 209], [84, 111, 106], [200, 157, 87], [188, 219, 57], [55, 58, 134], [31, 40, 109]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [212, 20], []]
 b := ![[], [98, 117, 46], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 3
  hpos := by decide
  P := [171, 17, 54, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9408242, -3274475, -596102]
  a := ![-2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-41446, -14425, -2626]
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

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0], ![-23, -86, 1]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![229, 0, 0], ![-23, -86, 1]] 
 ![![229, 0, 0], ![0, 229, 0], ![206, 143, 1]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]], ![![-23, -86, 1], ![269, 50, -171], ![-30316, -6064, -36]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-206, -143, 229]], ![![-1, -1, 1], ![155, 107, -171], ![-100, -4, -36]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 2 2 7 [32, 80, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [149, 228], [0, 1]]
 g := ![![[117, 64], [64], [78, 159], [134], [148], [209, 104], [149, 1]], ![[35, 165], [64], [182, 70], [134], [148], [133, 125], [69, 228]]]
 h' := ![![[149, 228], [84, 8], [23, 221], [127, 173], [221, 135], [182, 182], [41, 185], [0, 1]], ![[0, 1], [131, 221], [205, 8], [27, 56], [184, 94], [49, 47], [126, 44], [149, 228]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [72]]
 b := ![[], [66, 36]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 2
  hpos := by decide
  P := [32, 80, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2230, 1070, 142]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-118, -84, 142]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 52441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def I229N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0], ![-58, 1, 0]] i)))

def SI229N1: IdealEqSpanCertificate' Table ![![229, 0, 0], ![-58, 1, 0]] 
 ![![229, 0, 0], ![171, 1, 0], ![36, 0, 1]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]], ![![-58, 1, 0], ![1, -58, 2], ![355, 73, -57]]]
  hmulB := by decide  
  f := ![![![-2034, 134845, -4650], ![1145, 532425, 0]], ![![-1503, 100684, -3472], ![917, 397544, 0]], ![![-300, 21198, -731], ![258, 83700, 0]]]
  g := ![![![1, 0, 0], ![-171, 229, 0], ![-36, 0, 229]], ![![-1, 1, 0], ![43, -58, 2], ![-44, 73, -57]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N1 : Nat.card (O ⧸ I229N1) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N1)

lemma isPrimeI229N1 : Ideal.IsPrime I229N1 := prime_ideal_of_norm_prime hp229.out _ NI229N1
def MulI229N0 : IdealMulLeCertificate' Table 
  ![![229, 0, 0], ![-23, -86, 1]] ![![229, 0, 0], ![-58, 1, 0]]
  ![![229, 0, 0]] where
 M := ![![![52441, 0, 0], ![-13282, 229, 0]], ![![-5267, -19694, 229], ![1603, 5038, -229]]]
 hmul := by decide  
 g := ![![![![229, 0, 0]], ![![-58, 1, 0]]], ![![![-23, -86, 1]], ![![7, 22, -1]]]]
 hle2 := by decide  


def PBC229 : ContainsPrimesAboveP 229 ![I229N0, I229N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI229N0
    exact isPrimeI229N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 229 (by decide) (𝕀 ⊙ MulI229N0)
instance hp233 : Fact (Nat.Prime 233) := {out := by norm_num}

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![233, 0, 0]] 
 ![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 3 2 7 [230, 13, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [182, 32, 150], [48, 200, 83], [0, 1]]
 g := ![![[216, 165, 36], [213, 183], [93, 178], [211, 153, 161], [1, 231], [114, 51, 9], [1]], ![[182, 91, 232, 5], [28, 8], [126, 1], [88, 18, 46, 44], [70, 141], [117, 107, 133, 186], [13, 217, 105, 228]], ![[220, 101, 134, 176], [56, 126], [194, 232], [157, 8, 194, 146], [25, 220], [178, 48, 90, 145], [149, 124, 198, 5]]]
 h' := ![![[182, 32, 150], [99, 152, 227], [208, 111, 79], [167, 47, 143], [1, 209, 45], [109, 78, 109], [3, 220, 230], [0, 1]], ![[48, 200, 83], [32, 209, 164], [114, 30, 63], [40, 181, 1], [90, 10, 41], [87, 114, 181], [198, 169, 13], [182, 32, 150]], ![[0, 1], [45, 105, 75], [24, 92, 91], [52, 5, 89], [151, 14, 147], [141, 41, 176], [131, 77, 223], [48, 200, 83]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45, 229], []]
 b := ![[], [75, 71, 174], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 3
  hpos := by decide
  P := [230, 13, 3, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![22522712, 6178927, 917321]
  a := ![2, 19, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![96664, 26519, 3937]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N0 B_one_repr
lemma NI233N0 : Nat.card (O ⧸ I233N0) = 12649337 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N0

def PBC233 : ContainsPrimesAboveP 233 ![I233N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI233N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![233, 0, 0]]) timesTableT_eq_Table B_one_repr 233 (by decide) 𝕀



lemma PB234I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227, 229, 233] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 233 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 233 (by omega)

def PB234I4 : PrimesBelowBoundCertificateInterval O 193 233 234 where
  m := 7
  g := ![2, 3, 1, 2, 1, 2, 1]
  P := ![197, 199, 211, 223, 227, 229, 233]
  hP := PB234I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1]
    · exact ![I199N0, I199N1, I199N2]
    · exact ![I211N0]
    · exact ![I223N0, I223N1]
    · exact ![I227N0]
    · exact ![I229N0, I229N1]
    · exact ![I233N0]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![38809, 197]
    · exact ![199, 199, 199]
    · exact ![9393931]
    · exact ![49729, 223]
    · exact ![11697083]
    · exact ![52441, 229]
    · exact ![12649337]
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
      exact NI199N2
    · dsimp ; intro j
      fin_cases j
      exact NI211N0
    · dsimp ; intro j
      fin_cases j
      exact NI223N0
      exact NI223N1
    · dsimp ; intro j
      fin_cases j
      exact NI227N0
    · dsimp ; intro j
      fin_cases j
      exact NI229N0
      exact NI229N1
    · dsimp ; intro j
      fin_cases j
      exact NI233N0
  β := ![I197N1, I199N0, I199N1, I199N2, I223N1, I229N1]
  Il := ![[I197N1], [I199N0, I199N1, I199N2], [], [I223N1], [], [I229N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
