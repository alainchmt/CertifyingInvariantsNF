
import IdealArithmetic.Examples.NF3_1_648324_3.RI3_1_648324_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4201, 798, -146]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![4201, 798, -146]] 
 ![![197, 0, 0], ![0, 197, 0], ![121, 62, 1]] where
  M :=![![![4201, 798, -146], ![-62196, -7625, 1596], ![339948, 33540, -7625]]]
  hmulB := by decide  
  f := ![![![23405, 6030, 814]], ![![346764, 89339, 12060]], ![![136549, 35180, 4749]]]
  g := ![![![111, 50, -146], ![-1296, -541, 1596], ![6409, 2570, -7625]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 2 2 7 [76, 33, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [164, 196], [0, 1]]
 g := ![![[143, 70], [146], [89, 70], [143], [174], [193], [164, 1]], ![[0, 127], [146], [143, 127], [143], [174], [193], [131, 196]]]
 h' := ![![[164, 196], [155, 142], [131, 46], [63, 55], [117, 145], [158, 119], [144, 28], [0, 1]], ![[0, 1], [0, 55], [189, 151], [21, 142], [60, 52], [171, 78], [8, 169], [164, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [67]]
 b := ![[], [11, 132]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 2
  hpos := by decide
  P := [76, 33, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![928, 342, 50]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-26, -14, 50]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23405, 6030, 814]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![23405, 6030, 814]] 
 ![![197, 0, 0], ![73, 1, 0], ![192, 0, 1]] where
  M :=![![![23405, 6030, 814], ![346764, 89339, 12060], ![2568780, 661812, 89339]]]
  hmulB := by decide  
  f := ![![![4201, 798, -146]], ![![1241, 257, -46]], ![![5820, 948, -181]]]
  g := ![![![-2909, 6030, 814], ![-43099, 89339, 12060], ![-319272, 661812, 89339]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![4201, 798, -146]] ![![23405, 6030, 814]]
  ![![197, 0, 0]] where
 M := ![![![197, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![-99, 1, 0]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![199, 0, 0], ![-99, 1, 0]] 
 ![![199, 0, 0], ![100, 1, 0], ![174, 0, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![-99, 1, 0], ![0, -99, 2], ![426, 81, -99]]]
  hmulB := by decide  
  f := ![![![19702, -199, 0], ![39601, 0, 0]], ![![10000, -101, 0], ![20100, 0, 0]], ![![17202, -124, -1], ![34576, 100, 0]]]
  g := ![![![1, 0, 0], ![-100, 199, 0], ![-174, 0, 199]], ![![-1, 1, 0], ![48, -99, 2], ![48, 81, -99]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N0 : Nat.card (O ⧸ I199N0) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N0)

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := prime_ideal_of_norm_prime hp199.out _ NI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3508561019, -199586283, 58910188]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![-3508561019, -199586283, 58910188]] 
 ![![199, 0, 0], ![144, 1, 0], ![179, 0, 1]] where
  M :=![![![-3508561019, -199586283, 58910188], ![25095740088, 1263164209, -399172566], ![-85023756558, -3618618879, 1263164209]]]
  hmulB := by decide  
  f := ![![![151130435592122167, 38936730830705895, 5256127696450886]], ![![120612528261073716, 31074201098624587, 4194753014825826]], ![![219293443743068237, 56498016157424982, 7626751943062073]]]
  g := ![![![73803719, -199586283, 58910188], ![-428884506, 1263164209, -399172566], ![1055029993, -3618618879, 1263164209]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1

def I199N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![-45, 1, 0]] i)))

def SI199N2: IdealEqSpanCertificate' Table ![![199, 0, 0], ![-45, 1, 0]] 
 ![![199, 0, 0], ![154, 1, 0], ![82, 0, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![-45, 1, 0], ![0, -45, 2], ![426, 81, -45]]]
  hmulB := by decide  
  f := ![![![6166, -137, 0], ![27263, 0, 0]], ![![4816, -107, 0], ![21294, 0, 0]], ![![2548, -34, -1], ![11266, 100, 0]]]
  g := ![![![1, 0, 0], ![-154, 199, 0], ![-82, 0, 199]], ![![-1, 1, 0], ![34, -45, 2], ![-42, 81, -45]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N2 : Nat.card (O ⧸ I199N2) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N2)

lemma isPrimeI199N2 : Ideal.IsPrime I199N2 := prime_ideal_of_norm_prime hp199.out _ NI199N2
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![199, 0, 0], ![-99, 1, 0]] ![![-3508561019, -199586283, 58910188]]
  ![![199, 0, 0], ![36, -77, 1]] where
 M := ![![![-698203642781, -39717670317, 11723127412]], ![![372443280969, 21022206226, -6231281178]]]
 hmul := by decide  
 g := ![![![![-3423317015, -381913736, 61278077], ![-471209911, 0, 0]]], ![![![1826053491, 203003129, -32577437], ![251628785, 0, 0]]]]
 hle2 := by decide  

def MulI199N1 : IdealMulLeCertificate' Table 
  ![![199, 0, 0], ![36, -77, 1]] ![![199, 0, 0], ![-45, 1, 0]]
  ![![199, 0, 0]] where
 M := ![![![39601, 0, 0], ![-8955, 199, 0]], ![![7164, -15323, 199], ![-1194, 3582, -199]]]
 hmul := by decide  
 g := ![![![![199, 0, 0]], ![![-45, 1, 0]]], ![![![36, -77, 1]], ![![-6, 18, -1]]]]
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


def P211P0 : CertificateIrreducibleZModOfList' 211 3 2 7 [98, 112, 150, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [51, 29, 159], [10, 181, 52], [0, 1]]
 g := ![![[49, 8, 83], [91, 61, 189], [28, 45], [174, 114], [103, 52, 53], [207, 134], [1]], ![[25, 100, 132, 206], [55, 148, 57, 138], [15, 199], [205, 95], [18, 136, 111, 72], [16, 14], [156, 100, 45, 129]], ![[70, 201, 139, 178], [127, 51, 137, 117], [145, 201], [156, 100], [87, 184, 81, 14], [45, 6], [20, 31, 72, 82]]]
 h' := ![![[51, 29, 159], [155, 20, 111], [187, 139, 191], [140, 197, 195], [34, 159, 122], [79, 195, 106], [113, 99, 61], [0, 1]], ![[10, 181, 52], [86, 171, 61], [53, 109, 124], [62, 170, 153], [23, 8, 99], [8, 151, 184], [47, 42, 196], [51, 29, 159]], ![[0, 1], [105, 20, 39], [50, 174, 107], [171, 55, 74], [30, 44, 201], [184, 76, 132], [95, 70, 165], [10, 181, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [205, 176], []]
 b := ![[], [206, 108, 117], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 3
  hpos := by decide
  P := [98, 112, 150, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-171543, 730693, 267759]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-813, 3463, 1269]
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

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![-94, 95, 1]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![223, 0, 0], ![-94, 95, 1]] 
 ![![223, 0, 0], ![0, 223, 0], ![129, 95, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![-94, 95, 1], ![426, -13, 190], ![40470, 7908, -13]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-129, -95, 223]], ![![-1, 0, 1], ![-108, -81, 190], ![189, 41, -13]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 2 2 7 [181, 47, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [176, 222], [0, 1]]
 g := ![![[121, 69], [183, 132], [142, 188], [174, 15], [58, 32], [218], [176, 1]], ![[0, 154], [0, 91], [3, 35], [138, 208], [115, 191], [218], [129, 222]]]
 h' := ![![[176, 222], [104, 192], [166, 32], [172, 100], [206, 125], [210, 60], [33, 21], [0, 1]], ![[0, 1], [0, 31], [0, 191], [155, 123], [129, 98], [66, 163], [161, 202], [176, 222]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47]]
 b := ![[], [162, 135]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 2
  hpos := by decide
  P := [181, 47, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![417, -30, 164]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-93, -70, 164]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 49729 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![33, 1, 0]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![223, 0, 0], ![33, 1, 0]] 
 ![![223, 0, 0], ![33, 1, 0], ![13, 0, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![33, 1, 0], ![0, 33, 2], ![426, 81, 33]]]
  hmulB := by decide  
  f := ![![![4819, 146, 0], ![-32558, 0, 0]], ![![693, 21, 0], ![-4682, 0, 0]], ![![217, -10, -1], ![-1466, 112, 0]]]
  g := ![![![1, 0, 0], ![-33, 223, 0], ![-13, 0, 223]], ![![0, 1, 0], ![-5, 33, 2], ![-12, 81, 33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N1 : Nat.card (O ⧸ I223N1) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N1)

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := prime_ideal_of_norm_prime hp223.out _ NI223N1
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![223, 0, 0], ![-94, 95, 1]] ![![223, 0, 0], ![33, 1, 0]]
  ![![223, 0, 0]] where
 M := ![![![49729, 0, 0], ![7359, 223, 0]], ![![-20962, 21185, 223], ![-2676, 3122, 223]]]
 hmul := by decide  
 g := ![![![![223, 0, 0]], ![![33, 1, 0]]], ![![![-94, 95, 1]], ![![-12, 14, 1]]]]
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

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![-140, -68, 1]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![227, 0, 0], ![-140, -68, 1]] 
 ![![227, 0, 0], ![0, 227, 0], ![87, 159, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![-140, -68, 1], ![426, -59, -136], ![-28968, -5295, -59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-87, -159, 227]], ![![-1, -1, 1], ![54, 95, -136], ![-105, 18, -59]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 2 2 7 [39, 71, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [156, 226], [0, 1]]
 g := ![![[223, 63], [137, 121], [16], [47], [25], [35, 64], [156, 1]], ![[63, 164], [172, 106], [16], [47], [25], [31, 163], [85, 226]]]
 h' := ![![[156, 226], [105, 111], [16, 216], [169, 4], [169, 71], [224, 222], [45, 8], [0, 1]], ![[0, 1], [169, 116], [116, 11], [112, 223], [122, 156], [125, 5], [158, 219], [156, 226]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [100]]
 b := ![[], [186, 50]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 2
  hpos := by decide
  P := [39, 71, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2445, 1504, 512]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-207, -352, 512]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 51529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![-91, 1, 0]] i)))

def SI227N1: IdealEqSpanCertificate' Table ![![227, 0, 0], ![-91, 1, 0]] 
 ![![227, 0, 0], ![136, 1, 0], ![59, 0, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![-91, 1, 0], ![0, -91, 2], ![426, 81, -91]]]
  hmulB := by decide  
  f := ![![![820, -9, 0], ![2043, 0, 0]], ![![638, -7, 0], ![1590, 0, 0]], ![![246, 43, -1], ![613, 114, 0]]]
  g := ![![![1, 0, 0], ![-136, 227, 0], ![-59, 0, 227]], ![![-1, 1, 0], ![54, -91, 2], ![-23, 81, -91]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N1 : Nat.card (O ⧸ I227N1) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N1)

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := prime_ideal_of_norm_prime hp227.out _ NI227N1
def MulI227N0 : IdealMulLeCertificate' Table 
  ![![227, 0, 0], ![-140, -68, 1]] ![![227, 0, 0], ![-91, 1, 0]]
  ![![227, 0, 0]] where
 M := ![![![51529, 0, 0], ![-20657, 227, 0]], ![![-31780, -15436, 227], ![13166, 6129, -227]]]
 hmul := by decide  
 g := ![![![![227, 0, 0]], ![![-91, 1, 0]]], ![![![-140, -68, 1]], ![![58, 27, -1]]]]
 hle2 := by decide  


def PBC227 : ContainsPrimesAboveP 227 ![I227N0, I227N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI227N0
    exact isPrimeI227N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 227 (by decide) (𝕀 ⊙ MulI227N0)


lemma PB228I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 227 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 227 (by omega)

def PB228I4 : PrimesBelowBoundCertificateInterval O 193 227 228 where
  m := 5
  g := ![2, 3, 1, 2, 2]
  P := ![197, 199, 211, 223, 227]
  hP := PB228I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1]
    · exact ![I199N0, I199N1, I199N2]
    · exact ![I211N0]
    · exact ![I223N0, I223N1]
    · exact ![I227N0, I227N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC197
    · exact PBC199
    · exact PBC211
    · exact PBC223
    · exact PBC227
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![38809, 197]
    · exact ![199, 199, 199]
    · exact ![9393931]
    · exact ![49729, 223]
    · exact ![51529, 227]
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
      exact NI227N1
  β := ![I197N1, I199N0, I199N1, I199N2, I223N1, I227N1]
  Il := ![[I197N1], [I199N0, I199N1, I199N2], [], [I223N1], [I227N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
