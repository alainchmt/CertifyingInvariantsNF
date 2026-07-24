
import IdealArithmetic.Examples.NF3_1_761019_1.RI3_1_761019_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![51, 40, 1]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![197, 0, 0], ![51, 40, 1]] 
 ![![197, 0, 0], ![0, 197, 0], ![51, 40, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![51, 40, 1], ![-12, -21, 162], ![-3765, -1319, 100]]]
  hmulB := by decide  
  f := ![![![-50, -40, -1], ![197, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-51, -40, 197]], ![![0, 0, 1], ![-42, -33, 162], ![-45, -27, 100]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 2 2 7 [94, 174, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [23, 196], [0, 1]]
 g := ![![[27, 135], [127], [96, 90], [148], [155], [105], [23, 1]], ![[177, 62], [127], [196, 107], [148], [155], [105], [46, 196]]]
 h' := ![![[23, 196], [144, 174], [38, 179], [179, 22], [33, 98], [5, 67], [5, 41], [0, 1]], ![[0, 1], [9, 23], [18, 18], [94, 175], [120, 99], [167, 130], [160, 156], [23, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [192, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 2
  hpos := by decide
  P := [94, 174, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2373, -853, -2144]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![543, 431, -2144]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![35, 1, 0]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![197, 0, 0], ![35, 1, 0]] 
 ![![197, 0, 0], ![35, 1, 0], ![97, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![35, 1, 0], ![2, 34, 4], ![-92, -32, 37]]]
  hmulB := by decide  
  f := ![![![49301, 878492, 103360], ![13396, -5090480, 0]], ![![8760, 156048, 18360], ![2365, -904230, 0]], ![![24276, 432557, 50893], ![6591, -2506480, 0]]]
  g := ![![![1, 0, 0], ![-35, 197, 0], ![-97, 0, 197]], ![![0, 1, 0], ![-8, 34, 4], ![-13, -32, 37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![197, 0, 0], ![51, 40, 1]] ![![197, 0, 0], ![35, 1, 0]]
  ![![197, 0, 0]] where
 M := ![![![38809, 0, 0], ![6895, 197, 0]], ![![10047, 7880, 197], ![1773, 1379, 197]]]
 hmul := by decide  
 g := ![![![![197, 0, 0]], ![![35, 1, 0]]], ![![![51, 40, 1]], ![![9, 7, 1]]]]
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

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![39, 48, 1]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![199, 0, 0], ![39, 48, 1]] 
 ![![199, 0, 0], ![0, 199, 0], ![39, 48, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![39, 48, 1], ![4, -41, 194], ![-4501, -1575, 104]]]
  hmulB := by decide  
  f := ![![![-38, -48, -1], ![199, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-39, -48, 199]], ![![0, 0, 1], ![-38, -47, 194], ![-43, -33, 104]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 2 2 7 [173, 186, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [13, 198], [0, 1]]
 g := ![![[100, 90], [80, 116], [126, 175], [43], [122], [16], [13, 1]], ![[76, 109], [195, 83], [13, 24], [43], [122], [16], [26, 198]]]
 h' := ![![[13, 198], [90, 182], [92, 135], [64, 162], [90, 178], [36, 91], [139, 195], [0, 1]], ![[0, 1], [68, 17], [56, 64], [180, 37], [16, 21], [25, 108], [87, 4], [13, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [86]]
 b := ![[], [19, 43]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 2
  hpos := by decide
  P := [173, 186, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![457, -1152, -223]
  a := ![3, -3, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![46, 48, -223]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 39601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![5, 1, 0]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![199, 0, 0], ![5, 1, 0]] 
 ![![199, 0, 0], ![5, 1, 0], ![95, 0, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![5, 1, 0], ![2, 4, 4], ![-92, -32, 7]]]
  hmulB := by decide  
  f := ![![![-4399, -8800, -8800], ![0, 437800, 0]], ![![-110, -220, -220], ![1, 10945, 0]], ![![-2100, -4201, -4201], ![-1, 209000, 0]]]
  g := ![![![1, 0, 0], ![-5, 199, 0], ![-95, 0, 199]], ![![0, 1, 0], ![-2, 4, 4], ![-3, -32, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![199, 0, 0], ![39, 48, 1]] ![![199, 0, 0], ![5, 1, 0]]
  ![![199, 0, 0]] where
 M := ![![![39601, 0, 0], ![995, 199, 0]], ![![7761, 9552, 199], ![199, 199, 199]]]
 hmul := by decide  
 g := ![![![![199, 0, 0]], ![![5, 1, 0]]], ![![![39, 48, 1]], ![![1, 1, 1]]]]
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

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![52, 1, 0]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![211, 0, 0], ![52, 1, 0]] 
 ![![211, 0, 0], ![52, 1, 0], ![76, 0, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![52, 1, 0], ![2, 51, 4], ![-92, -32, 54]]]
  hmulB := by decide  
  f := ![![![-14431, -401141, -31464], ![-5275, 1659726, 0]], ![![-3564, -98832, -7752], ![-1265, 408918, 0]], ![![-5208, -144487, -11333], ![-1859, 597816, 0]]]
  g := ![![![1, 0, 0], ![-52, 211, 0], ![-76, 0, 211]], ![![0, 1, 0], ![-14, 51, 4], ![-12, -32, 54]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N0 : Nat.card (O ⧸ I211N0) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N0)

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := prime_ideal_of_norm_prime hp211.out _ NI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![65, 1, 0]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![211, 0, 0], ![65, 1, 0]] 
 ![![211, 0, 0], ![65, 1, 0], ![121, 0, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![65, 1, 0], ![2, 64, 4], ![-92, -32, 67]]]
  hmulB := by decide  
  f := ![![![1106, 41597, 2600], ![633, -137150, 0]], ![![335, 12799, 800], ![212, -42200, 0]], ![![621, 23854, 1491], ![406, -78650, 0]]]
  g := ![![![1, 0, 0], ![-65, 211, 0], ![-121, 0, 211]], ![![0, 1, 0], ![-22, 64, 4], ![-29, -32, 67]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1

def I211N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![93, 1, 0]] i)))

def SI211N2: IdealEqSpanCertificate' Table ![![211, 0, 0], ![93, 1, 0]] 
 ![![211, 0, 0], ![93, 1, 0], ![77, 0, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![93, 1, 0], ![2, 92, 4], ![-92, -32, 95]]]
  hmulB := by decide  
  f := ![![![-12377, -749022, -32568], ![-8862, 1717962, 0]], ![![-5502, -330078, -14352], ![-3797, 757068, 0]], ![![-4537, -273340, -11885], ![-3188, 626934, 0]]]
  g := ![![![1, 0, 0], ![-93, 211, 0], ![-77, 0, 211]], ![![0, 1, 0], ![-42, 92, 4], ![-21, -32, 95]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N2 : Nat.card (O ⧸ I211N2) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N2)

lemma isPrimeI211N2 : Ideal.IsPrime I211N2 := prime_ideal_of_norm_prime hp211.out _ NI211N2
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![211, 0, 0], ![52, 1, 0]] ![![211, 0, 0], ![65, 1, 0]]
  ![![211, 0, 0], ![107, 29, 1]] where
 M := ![![![44521, 0, 0], ![13715, 211, 0]], ![![10972, 211, 0], ![3382, 116, 4]]]
 hmul := by decide  
 g := ![![![![104, -29, -1], ![211, 0, 0]], ![![-42, -28, -1], ![211, 0, 0]]], ![![![-55, -28, -1], ![211, 0, 0]], ![![-93, -29, -1], ![215, 0, 0]]]]
 hle2 := by decide  

def MulI211N1 : IdealMulLeCertificate' Table 
  ![![211, 0, 0], ![107, 29, 1]] ![![211, 0, 0], ![93, 1, 0]]
  ![![211, 0, 0]] where
 M := ![![![44521, 0, 0], ![19623, 211, 0]], ![![22577, 6119, 211], ![9917, 2743, 211]]]
 hmul := by decide  
 g := ![![![![211, 0, 0]], ![![93, 1, 0]]], ![![![107, 29, 1]], ![![47, 13, 1]]]]
 hle2 := by decide  


def PBC211 : ContainsPrimesAboveP 211 ![I211N0, I211N1, I211N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI211N0
    exact isPrimeI211N1
    exact isPrimeI211N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 211 (by decide) (𝕀 ⊙ MulI211N0 ⊙ MulI211N1)
instance hp223 : Fact (Nat.Prime 223) := {out := by norm_num}

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![-44, -10, 1]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![223, 0, 0], ![-44, -10, 1]] 
 ![![223, 0, 0], ![0, 223, 0], ![179, 213, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![-44, -10, 1], ![-112, -66, -38], ![835, 281, -95]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-179, -213, 223]], ![![-1, -1, 1], ![30, 36, -38], ![80, 92, -95]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 2 2 7 [163, 196, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [27, 222], [0, 1]]
 g := ![![[190, 139], [60, 183], [66, 203], [92, 175], [5, 1], [128], [27, 1]], ![[152, 84], [95, 40], [195, 20], [134, 48], [32, 222], [128], [54, 222]]]
 h' := ![![[27, 222], [32, 129], [169, 39], [168, 181], [77, 93], [11, 222], [59, 120], [0, 1]], ![[0, 1], [170, 94], [107, 184], [149, 42], [135, 130], [207, 1], [177, 103], [27, 222]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [110]]
 b := ![[], [38, 55]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 2
  hpos := by decide
  P := [163, 196, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-366466, -165595, -139652]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![110454, 132647, -139652]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 49729 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![38, 1, 0]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![223, 0, 0], ![38, 1, 0]] 
 ![![223, 0, 0], ![38, 1, 0], ![95, 0, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![38, 1, 0], ![2, 37, 4], ![-92, -32, 40]]]
  hmulB := by decide  
  f := ![![![40335, 779173, 84240], ![10481, -4696380, 0]], ![![6872, 132748, 14352], ![1785, -800124, 0]], ![![17157, 331934, 35887], ![4618, -2000700, 0]]]
  g := ![![![1, 0, 0], ![-38, 223, 0], ![-95, 0, 223]], ![![0, 1, 0], ![-8, 37, 4], ![-12, -32, 40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N1 : Nat.card (O ⧸ I223N1) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N1)

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := prime_ideal_of_norm_prime hp223.out _ NI223N1
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![223, 0, 0], ![-44, -10, 1]] ![![223, 0, 0], ![38, 1, 0]]
  ![![223, 0, 0]] where
 M := ![![![49729, 0, 0], ![8474, 223, 0]], ![![-9812, -2230, 223], ![-1784, -446, 0]]]
 hmul := by decide  
 g := ![![![![223, 0, 0]], ![![38, 1, 0]]], ![![![-44, -10, 1]], ![![-8, -2, 0]]]]
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


def P227P0 : CertificateIrreducibleZModOfList' 227 3 2 7 [51, 11, 123, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [197, 146, 98], [134, 80, 129], [0, 1]]
 g := ![![[54, 32, 78], [220, 149, 4], [197, 3], [149, 104], [70, 16], [142, 61, 147], [1]], ![[8, 116, 13, 164], [48, 102, 223, 51], [201, 104], [164, 189], [29, 171], [56, 79, 1, 216], [189, 132, 221, 50]], ![[201, 204, 96, 89], [65, 79, 38, 19], [25, 213], [160, 104], [70, 214], [9, 179, 113, 29], [24, 213, 23, 177]]]
 h' := ![![[197, 146, 98], [130, 191, 87], [201, 10, 225], [184, 126, 177], [92, 89, 176], [22, 198, 4], [176, 216, 104], [0, 1]], ![[134, 80, 129], [199, 176, 27], [26, 221, 139], [210, 133, 176], [42, 127, 102], [188, 60, 202], [135, 170, 205], [197, 146, 98]], ![[0, 1], [155, 87, 113], [31, 223, 90], [202, 195, 101], [72, 11, 176], [64, 196, 21], [42, 68, 145], [134, 80, 129]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46, 173], []]
 b := ![[], [116, 62, 121], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 3
  hpos := by decide
  P := [51, 11, 123, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2672925, -1237377, -988812]
  a := ![-4, 3, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-11775, -5451, -4356]
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

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0], ![-80, -114, 1]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![229, 0, 0], ![-80, -114, 1]] 
 ![![229, 0, 0], ![0, 229, 0], ![149, 115, 1]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]], ![![-80, -114, 1], ![-320, 2, -454], ![10403, 3609, -339]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-149, -115, 229]], ![![-1, -1, 1], ![294, 228, -454], ![266, 186, -339]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 2 2 7 [124, 62, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [167, 228], [0, 1]]
 g := ![![[115, 176], [176], [207, 148], [58], [178], [5, 159], [167, 1]], ![[195, 53], [176], [191, 81], [58], [178], [223, 70], [105, 228]]]
 h' := ![![[167, 228], [102, 136], [209, 136], [117, 182], [50, 79], [67, 112], [131, 56], [0, 1]], ![[0, 1], [143, 93], [21, 93], [54, 47], [190, 150], [222, 117], [94, 173], [167, 228]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [106, 129]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 2
  hpos := by decide
  P := [124, 62, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2007, -965, -1472]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![949, 735, -1472]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 52441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def I229N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0], ![-4, 1, 0]] i)))

def SI229N1: IdealEqSpanCertificate' Table ![![229, 0, 0], ![-4, 1, 0]] 
 ![![229, 0, 0], ![225, 1, 0], ![110, 0, 1]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]], ![![-4, 1, 0], ![2, -5, 4], ![-92, -32, -2]]]
  hmulB := by decide  
  f := ![![![-11619, 29068, -23256], ![458, 1331406, 0]], ![![-11415, 28558, -22848], ![459, 1308048, 0]], ![![-5582, 13963, -11171], ![173, 639540, 0]]]
  g := ![![![1, 0, 0], ![-225, 229, 0], ![-110, 0, 229]], ![![-1, 1, 0], ![3, -5, 4], ![32, -32, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N1 : Nat.card (O ⧸ I229N1) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N1)

lemma isPrimeI229N1 : Ideal.IsPrime I229N1 := prime_ideal_of_norm_prime hp229.out _ NI229N1
def MulI229N0 : IdealMulLeCertificate' Table 
  ![![229, 0, 0], ![-80, -114, 1]] ![![229, 0, 0], ![-4, 1, 0]]
  ![![229, 0, 0]] where
 M := ![![![52441, 0, 0], ![-916, 229, 0]], ![![-18320, -26106, 229], ![0, 458, -458]]]
 hmul := by decide  
 g := ![![![![229, 0, 0]], ![![-4, 1, 0]]], ![![![-80, -114, 1]], ![![0, 2, -2]]]]
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

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0], ![92, 68, 1]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![233, 0, 0], ![92, 68, 1]] 
 ![![233, 0, 0], ![0, 233, 0], ![92, 68, 1]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]], ![![92, 68, 1], ![44, -8, 274], ![-6341, -2215, 197]]]
  hmulB := by decide  
  f := ![![![-91, -68, -1], ![233, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-92, -68, 233]], ![![0, 0, 1], ![-108, -80, 274], ![-105, -67, 197]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 2 2 7 [2, 145, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [88, 232], [0, 1]]
 g := ![![[189, 117], [25], [32], [215, 26], [157], [196, 13], [88, 1]], ![[0, 116], [25], [32], [173, 207], [157], [175, 220], [176, 232]]]
 h' := ![![[88, 232], [12, 74], [67, 5], [36, 126], [36, 78], [74, 200], [57, 53], [0, 1]], ![[0, 1], [0, 159], [41, 228], [173, 107], [143, 155], [199, 33], [61, 180], [88, 232]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [223]]
 b := ![[], [220, 228]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 2
  hpos := by decide
  P := [2, 145, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-145575, -69549, -49360]
  a := ![22, -1, 43]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![18865, 14107, -49360]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N0 B_one_repr
lemma NI233N0 : Nat.card (O ⧸ I233N0) = 54289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N0

def I233N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0], ![-41, 1, 0]] i)))

def SI233N1: IdealEqSpanCertificate' Table ![![233, 0, 0], ![-41, 1, 0]] 
 ![![233, 0, 0], ![192, 1, 0], ![36, 0, 1]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]], ![![-41, 1, 0], ![2, -42, 4], ![-92, -32, -39]]]
  hmulB := by decide  
  f := ![![![36779, -808458, 77000], ![-9786, -4485250, 0]], ![![30290, -666169, 63448], ![-8154, -3695846, 0]], ![![5684, -124912, 11897], ![-1504, -693000, 0]]]
  g := ![![![1, 0, 0], ![-192, 233, 0], ![-36, 0, 233]], ![![-1, 1, 0], ![34, -42, 4], ![32, -32, -39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N1 : Nat.card (O ⧸ I233N1) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N1)

lemma isPrimeI233N1 : Ideal.IsPrime I233N1 := prime_ideal_of_norm_prime hp233.out _ NI233N1
def MulI233N0 : IdealMulLeCertificate' Table 
  ![![233, 0, 0], ![92, 68, 1]] ![![233, 0, 0], ![-41, 1, 0]]
  ![![233, 0, 0]] where
 M := ![![![54289, 0, 0], ![-9553, 233, 0]], ![![21436, 15844, 233], ![-3728, -2796, 233]]]
 hmul := by decide  
 g := ![![![![233, 0, 0]], ![![-41, 1, 0]]], ![![![92, 68, 1]], ![![-16, -12, 1]]]]
 hle2 := by decide  


def PBC233 : ContainsPrimesAboveP 233 ![I233N0, I233N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI233N0
    exact isPrimeI233N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 233 (by decide) (𝕀 ⊙ MulI233N0)
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


def P239P0 : CertificateIrreducibleZModOfList' 239 3 2 7 [16, 216, 62, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [129, 238, 119], [48, 0, 120], [0, 1]]
 g := ![![[216, 226, 127], [135, 144, 32], [39, 80, 108], [46, 43, 93], [75, 183], [230, 210, 20], [1]], ![[232, 147, 81, 41], [66, 54, 150, 59], [118, 178, 236, 227], [165, 178, 122, 214], [94, 127], [189, 177, 126, 143], [160, 226, 7, 209]], ![[99, 19, 142, 29], [174, 216, 234, 142], [235, 26, 13, 45], [235, 146, 194, 113], [58, 216], [187, 224, 161, 102], [3, 131, 52, 30]]]
 h' := ![![[129, 238, 119], [230, 129, 137], [93, 217, 82], [220, 151, 81], [177, 34, 103], [144, 35, 30], [223, 23, 177], [0, 1]], ![[48, 0, 120], [134, 145, 55], [138, 186, 11], [212, 11, 44], [172, 172, 222], [106, 25, 102], [60, 92, 108], [129, 238, 119]], ![[0, 1], [175, 204, 47], [132, 75, 146], [36, 77, 114], [92, 33, 153], [231, 179, 107], [126, 124, 193], [48, 0, 120]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [224, 72], []]
 b := ![[], [126, 196, 144], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 3
  hpos := by decide
  P := [16, 216, 62, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3107, -1434, -1434]
  a := ![0, 1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-13, -6, -6]
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

def I241N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0]] i)))

def SI241N0: IdealEqSpanCertificate' Table ![![241, 0, 0]] 
 ![![241, 0, 0], ![0, 241, 0], ![0, 0, 241]] where
  M :=![![![241, 0, 0], ![0, 241, 0], ![0, 0, 241]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P241P0 : CertificateIrreducibleZModOfList' 241 3 2 7 [72, 147, 135, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [59, 72, 15], [47, 168, 226], [0, 1]]
 g := ![![[36, 6, 166], [44, 183], [158, 211], [183, 192], [125, 119, 79], [50, 160, 150], [1]], ![[60, 54, 83, 80], [240, 187], [79, 30], [185, 107], [60, 25, 160, 221], [62, 145, 148, 61], [85, 39, 24, 1]], ![[141, 5], [180, 16], [1, 225], [227, 143], [132, 59], [62, 138, 158, 121], [168, 184, 24, 240]]]
 h' := ![![[59, 72, 15], [112, 220, 86], [151, 136, 122], [220, 69, 115], [158, 33, 34], [15, 51, 101], [169, 94, 106], [0, 1]], ![[47, 168, 226], [236, 192, 155], [37, 36, 123], [69, 11, 111], [161, 68, 182], [127, 119, 140], [193, 97, 179], [59, 72, 15]], ![[0, 1], [79, 70], [5, 69, 237], [42, 161, 15], [203, 140, 25], [164, 71], [147, 50, 197], [47, 168, 226]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [195, 142], []]
 b := ![[], [97, 37, 103], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 3
  hpos := by decide
  P := [72, 147, 135, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3814307, 1478776, 455008]
  a := ![5, -2, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![15827, 6136, 1888]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI241N0 : Ideal.IsPrime I241N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI241N0 B_one_repr
lemma NI241N0 : Nat.card (O ⧸ I241N0) = 13997521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI241N0

def PBC241 : ContainsPrimesAboveP 241 ![I241N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI241N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![241, 0, 0]]) timesTableT_eq_Table B_one_repr 241 (by decide) 𝕀



lemma PB247I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227, 229, 233, 239, 241] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 246 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 246 (by omega)

def PB247I4 : PrimesBelowBoundCertificateInterval O 193 246 247 where
  m := 9
  g := ![2, 2, 3, 2, 1, 2, 2, 1, 1]
  P := ![197, 199, 211, 223, 227, 229, 233, 239, 241]
  hP := PB247I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1]
    · exact ![I199N0, I199N1]
    · exact ![I211N0, I211N1, I211N2]
    · exact ![I223N0, I223N1]
    · exact ![I227N0]
    · exact ![I229N0, I229N1]
    · exact ![I233N0, I233N1]
    · exact ![I239N0]
    · exact ![I241N0]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![38809, 197]
    · exact ![39601, 199]
    · exact ![211, 211, 211]
    · exact ![49729, 223]
    · exact ![11697083]
    · exact ![52441, 229]
    · exact ![54289, 233]
    · exact ![13651919]
    · exact ![13997521]
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
      exact NI211N2
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
      exact NI233N1
    · dsimp ; intro j
      fin_cases j
      exact NI239N0
    · dsimp ; intro j
      fin_cases j
      exact NI241N0
  β := ![I197N1, I199N1, I211N0, I211N1, I211N2, I223N1, I229N1, I233N1]
  Il := ![[I197N1], [I199N1], [I211N0, I211N1, I211N2], [I223N1], [], [I229N1], [I233N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
