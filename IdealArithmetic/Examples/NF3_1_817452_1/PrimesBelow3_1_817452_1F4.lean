
import IdealArithmetic.Examples.NF3_1_817452_1.RI3_1_817452_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![-25, -70, 1]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![197, 0, 0], ![-25, -70, 1]] 
 ![![197, 0, 0], ![0, 197, 0], ![172, 127, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![-25, -70, 1], ![174, -25, -70], ![-12180, 174, -25]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-172, -127, 197]], ![![-1, -1, 1], ![62, 45, -70], ![-40, 17, -25]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 2 2 7 [32, 95, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [102, 196], [0, 1]]
 g := ![![[83, 191], [7], [48, 196], [40], [23], [33], [102, 1]], ![[62, 6], [7], [143, 1], [40], [23], [33], [7, 196]]]
 h' := ![![[102, 196], [194, 114], [40, 91], [65, 183], [153, 51], [62, 107], [85, 128], [0, 1]], ![[0, 1], [2, 83], [63, 106], [16, 14], [36, 146], [141, 90], [139, 69], [102, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [123]]
 b := ![[], [114, 160]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 2
  hpos := by decide
  P := [32, 95, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![380, 79, -94]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![84, 61, -94]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![70, 1, 0]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![197, 0, 0], ![70, 1, 0]] 
 ![![197, 0, 0], ![70, 1, 0], ![25, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![70, 1, 0], ![0, 70, 1], ![174, 0, 70]]]
  hmulB := by decide  
  f := ![![![3921, 56, 0], ![-11032, 0, 0]], ![![1330, 19, 0], ![-3742, 0, 0]], ![![445, 6, 0], ![-1252, 1, 0]]]
  g := ![![![1, 0, 0], ![-70, 197, 0], ![-25, 0, 197]], ![![0, 1, 0], ![-25, 70, 1], ![-8, 0, 70]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![197, 0, 0], ![-25, -70, 1]] ![![197, 0, 0], ![70, 1, 0]]
  ![![197, 0, 0]] where
 M := ![![![38809, 0, 0], ![13790, 197, 0]], ![![-4925, -13790, 197], ![-1576, -4925, 0]]]
 hmul := by decide  
 g := ![![![![197, 0, 0]], ![![70, 1, 0]]], ![![![-25, -70, 1]], ![![-8, -25, 0]]]]
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

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![46, 1, 0]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![199, 0, 0], ![46, 1, 0]] 
 ![![199, 0, 0], ![46, 1, 0], ![73, 0, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![46, 1, 0], ![0, 46, 1], ![174, 0, 46]]]
  hmulB := by decide  
  f := ![![![507, 11, 0], ![-2189, 0, 0]], ![![46, 1, 0], ![-198, 0, 0]], ![![149, 3, 0], ![-643, 1, 0]]]
  g := ![![![1, 0, 0], ![-46, 199, 0], ![-73, 0, 199]], ![![0, 1, 0], ![-11, 46, 1], ![-16, 0, 46]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N0 : Nat.card (O ⧸ I199N0) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N0)

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := prime_ideal_of_norm_prime hp199.out _ NI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![53, 1, 0]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![199, 0, 0], ![53, 1, 0]] 
 ![![199, 0, 0], ![53, 1, 0], ![176, 0, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![53, 1, 0], ![0, 53, 1], ![174, 0, 53]]]
  hmulB := by decide  
  f := ![![![5195, 98, 0], ![-19502, 0, 0]], ![![1325, 25, 0], ![-4974, 0, 0]], ![![4626, 87, 0], ![-17366, 1, 0]]]
  g := ![![![1, 0, 0], ![-53, 199, 0], ![-176, 0, 199]], ![![0, 1, 0], ![-15, 53, 1], ![-46, 0, 53]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1

def I199N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![-99, 1, 0]] i)))

def SI199N2: IdealEqSpanCertificate' Table ![![199, 0, 0], ![-99, 1, 0]] 
 ![![199, 0, 0], ![100, 1, 0], ![149, 0, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![-99, 1, 0], ![0, -99, 1], ![174, 0, -99]]]
  hmulB := by decide  
  f := ![![![19702, -199, 0], ![39601, 0, 0]], ![![10000, -101, 0], ![20100, 0, 0]], ![![14900, -150, 0], ![29949, 1, 0]]]
  g := ![![![1, 0, 0], ![-100, 199, 0], ![-149, 0, 199]], ![![-1, 1, 0], ![49, -99, 1], ![75, 0, -99]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N2 : Nat.card (O ⧸ I199N2) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N2)

lemma isPrimeI199N2 : Ideal.IsPrime I199N2 := prime_ideal_of_norm_prime hp199.out _ NI199N2
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![199, 0, 0], ![46, 1, 0]] ![![199, 0, 0], ![53, 1, 0]]
  ![![199, 0, 0], ![50, 99, 1]] where
 M := ![![![39601, 0, 0], ![10547, 199, 0]], ![![9154, 199, 0], ![2438, 99, 1]]]
 hmul := by decide  
 g := ![![![![149, -99, -1], ![199, 0, 0]], ![![3, -98, -1], ![199, 0, 0]]], ![![![-4, -98, -1], ![199, 0, 0]], ![![-38, -99, -1], ![200, 0, 0]]]]
 hle2 := by decide  

def MulI199N1 : IdealMulLeCertificate' Table 
  ![![199, 0, 0], ![50, 99, 1]] ![![199, 0, 0], ![-99, 1, 0]]
  ![![199, 0, 0]] where
 M := ![![![39601, 0, 0], ![-19701, 199, 0]], ![![9950, 19701, 199], ![-4776, -9751, 0]]]
 hmul := by decide  
 g := ![![![![199, 0, 0]], ![![-99, 1, 0]]], ![![![50, 99, 1]], ![![-24, -49, 0]]]]
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


def P211P0 : CertificateIrreducibleZModOfList' 211 3 2 7 [56, 181, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [38, 29, 128], [170, 181, 83], [0, 1]]
 g := ![![[37, 64, 120], [210, 52, 83], [171, 13], [162, 73], [77, 125, 78], [4, 9], [1]], ![[59, 99, 86, 40], [144, 133, 152, 158], [19, 95], [81, 122], [69, 98, 103, 168], [190, 122], [74, 73, 34, 23]], ![[154, 139, 151, 103], [8, 186, 61, 107], [123, 44], [171, 62], [167, 138, 39, 178], [100, 183], [14, 59, 188, 188]]]
 h' := ![![[38, 29, 128], [56, 126, 139], [122, 200, 111], [25, 51, 151], [119, 28, 101], [169, 54, 17], [155, 30, 208], [0, 1]], ![[170, 181, 83], [141, 69, 142], [53, 12, 115], [189, 74, 99], [111, 100, 132], [58, 153, 72], [88, 114, 132], [38, 29, 128]], ![[0, 1], [111, 16, 141], [76, 210, 196], [210, 86, 172], [49, 83, 189], [25, 4, 122], [136, 67, 82], [170, 181, 83]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 119], []]
 b := ![[], [79, 136, 126], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 3
  hpos := by decide
  P := [56, 181, 3, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![815937, 5908, -8862]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3867, 28, -42]
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

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![36, 1, 0]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![223, 0, 0], ![36, 1, 0]] 
 ![![223, 0, 0], ![36, 1, 0], ![42, 0, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![36, 1, 0], ![0, 36, 1], ![174, 0, 36]]]
  hmulB := by decide  
  f := ![![![1045, 29, 0], ![-6467, 0, 0]], ![![108, 3, 0], ![-668, 0, 0]], ![![150, 4, 0], ![-928, 1, 0]]]
  g := ![![![1, 0, 0], ![-36, 223, 0], ![-42, 0, 223]], ![![0, 1, 0], ![-6, 36, 1], ![-6, 0, 36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N0 : Nat.card (O ⧸ I223N0) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N0)

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := prime_ideal_of_norm_prime hp223.out _ NI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![66, 1, 0]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![223, 0, 0], ![66, 1, 0]] 
 ![![223, 0, 0], ![66, 1, 0], ![104, 0, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![66, 1, 0], ![0, 66, 1], ![174, 0, 66]]]
  hmulB := by decide  
  f := ![![![4885, 74, 0], ![-16502, 0, 0]], ![![1386, 21, 0], ![-4682, 0, 0]], ![![2264, 34, 0], ![-7648, 1, 0]]]
  g := ![![![1, 0, 0], ![-66, 223, 0], ![-104, 0, 223]], ![![0, 1, 0], ![-20, 66, 1], ![-30, 0, 66]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N1 : Nat.card (O ⧸ I223N1) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N1)

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := prime_ideal_of_norm_prime hp223.out _ NI223N1

def I223N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![-102, 1, 0]] i)))

def SI223N2: IdealEqSpanCertificate' Table ![![223, 0, 0], ![-102, 1, 0]] 
 ![![223, 0, 0], ![121, 1, 0], ![77, 0, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![-102, 1, 0], ![0, -102, 1], ![174, 0, -102]]]
  hmulB := by decide  
  f := ![![![17443, -171, 0], ![38133, 0, 0]], ![![9589, -94, 0], ![20963, 0, 0]], ![![6065, -59, 0], ![13259, 1, 0]]]
  g := ![![![1, 0, 0], ![-121, 223, 0], ![-77, 0, 223]], ![![-1, 1, 0], ![55, -102, 1], ![36, 0, -102]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N2 : Nat.card (O ⧸ I223N2) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N2)

lemma isPrimeI223N2 : Ideal.IsPrime I223N2 := prime_ideal_of_norm_prime hp223.out _ NI223N2
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![223, 0, 0], ![36, 1, 0]] ![![223, 0, 0], ![66, 1, 0]]
  ![![223, 0, 0], ![-77, 102, 1]] where
 M := ![![![49729, 0, 0], ![14718, 223, 0]], ![![8028, 223, 0], ![2376, 102, 1]]]
 hmul := by decide  
 g := ![![![![223, 0, 0], ![0, 0, 0]], ![![66, 1, 0], ![0, 0, 0]]], ![![![36, 1, 0], ![0, 0, 0]], ![![11, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI223N1 : IdealMulLeCertificate' Table 
  ![![223, 0, 0], ![-77, 102, 1]] ![![223, 0, 0], ![-102, 1, 0]]
  ![![223, 0, 0]] where
 M := ![![![49729, 0, 0], ![-22746, 223, 0]], ![![-17171, 22746, 223], ![8028, -10481, 0]]]
 hmul := by decide  
 g := ![![![![223, 0, 0]], ![![-102, 1, 0]]], ![![![-77, 102, 1]], ![![36, -47, 0]]]]
 hle2 := by decide  


def PBC223 : ContainsPrimesAboveP 223 ![I223N0, I223N1, I223N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI223N0
    exact isPrimeI223N1
    exact isPrimeI223N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 223 (by decide) (𝕀 ⊙ MulI223N0 ⊙ MulI223N1)
instance hp227 : Fact (Nat.Prime 227) := {out := by norm_num}

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![113, 106, 1]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![227, 0, 0], ![113, 106, 1]] 
 ![![227, 0, 0], ![0, 227, 0], ![113, 106, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![113, 106, 1], ![174, 113, 106], ![18444, 174, 113]]]
  hmulB := by decide  
  f := ![![![-112, -106, -1], ![227, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-113, -106, 227]], ![![0, 0, 1], ![-52, -49, 106], ![25, -52, 113]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 2 2 7 [133, 121, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [106, 226], [0, 1]]
 g := ![![[175, 99], [116, 76], [182], [9], [136], [3, 173], [106, 1]], ![[0, 128], [0, 151], [182], [9], [136], [181, 54], [212, 226]]]
 h' := ![![[106, 226], [8, 107], [102, 59], [143, 78], [146, 224], [55, 131], [203, 207], [0, 1]], ![[0, 1], [0, 120], [0, 168], [12, 149], [55, 3], [94, 96], [126, 20], [106, 226]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [175]]
 b := ![[], [16, 201]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 2
  hpos := by decide
  P := [133, 121, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3863, 167, 8]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-21, -3, 8]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 51529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![-106, 1, 0]] i)))

def SI227N1: IdealEqSpanCertificate' Table ![![227, 0, 0], ![-106, 1, 0]] 
 ![![227, 0, 0], ![121, 1, 0], ![114, 0, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![-106, 1, 0], ![0, -106, 1], ![174, 0, -106]]]
  hmulB := by decide  
  f := ![![![2863, -27, 0], ![6129, 0, 0]], ![![1485, -14, 0], ![3179, 0, 0]], ![![1534, -14, 0], ![3284, 1, 0]]]
  g := ![![![1, 0, 0], ![-121, 227, 0], ![-114, 0, 227]], ![![-1, 1, 0], ![56, -106, 1], ![54, 0, -106]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N1 : Nat.card (O ⧸ I227N1) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N1)

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := prime_ideal_of_norm_prime hp227.out _ NI227N1
def MulI227N0 : IdealMulLeCertificate' Table 
  ![![227, 0, 0], ![113, 106, 1]] ![![227, 0, 0], ![-106, 1, 0]]
  ![![227, 0, 0]] where
 M := ![![![51529, 0, 0], ![-24062, 227, 0]], ![![25651, 24062, 227], ![-11804, -11123, 0]]]
 hmul := by decide  
 g := ![![![![227, 0, 0]], ![![-106, 1, 0]]], ![![![113, 106, 1]], ![![-52, -49, 0]]]]
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
instance hp229 : Fact (Nat.Prime 229) := {out := by norm_num}

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![229, 0, 0]] 
 ![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 3 2 7 [13, 195, 226, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [49, 153, 126], [183, 75, 103], [0, 1]]
 g := ![![[190, 26, 100], [1, 25], [52, 36, 125], [209, 45], [135, 45], [16, 2, 9], [1]], ![[67, 110, 19, 58], [108, 70], [58, 207, 124, 218], [154, 82], [119, 80], [186, 109, 189, 149], [30, 175, 29, 61]], ![[195, 22, 46, 43], [220, 17], [146, 29, 183, 161], [83, 171], [42, 5], [141, 215, 188, 181], [223, 111, 204, 168]]]
 h' := ![![[49, 153, 126], [108, 55, 10], [11, 99, 224], [196, 38, 101], [60, 112, 31], [21, 0, 31], [216, 34, 3], [0, 1]], ![[183, 75, 103], [154, 162, 123], [118, 152, 191], [58, 21, 226], [107, 185, 178], [76, 224, 35], [11, 1, 158], [49, 153, 126]], ![[0, 1], [81, 12, 96], [45, 207, 43], [210, 170, 131], [217, 161, 20], [63, 5, 163], [67, 194, 68], [183, 75, 103]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [124, 103], []]
 b := ![[], [112, 202, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 3
  hpos := by decide
  P := [13, 195, 226, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1055919, 357698, 2977]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4611, 1562, 13]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 12008989 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def PBC229 : ContainsPrimesAboveP 229 ![I229N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI229N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![229, 0, 0]]) timesTableT_eq_Table B_one_repr 229 (by decide) 𝕀

instance hp233 : Fact (Nat.Prime 233) := {out := by norm_num}

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0], ![-25, 21, 1]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![233, 0, 0], ![-25, 21, 1]] 
 ![![233, 0, 0], ![0, 233, 0], ![208, 21, 1]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]], ![![-25, 21, 1], ![174, -25, 21], ![3654, 174, -25]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-208, -21, 233]], ![![-1, 0, 1], ![-18, -2, 21], ![38, 3, -25]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 2 2 7 [193, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [229, 232], [0, 1]]
 g := ![![[163, 9], [15], [63], [102, 15], [13], [59, 107], [229, 1]], ![[127, 224], [15], [63], [42, 218], [13], [97, 126], [225, 232]]]
 h' := ![![[229, 232], [72, 3], [138, 99], [119, 210], [22, 99], [30, 53], [73, 56], [0, 1]], ![[0, 1], [60, 230], [208, 134], [211, 23], [92, 134], [51, 180], [82, 177], [229, 232]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [90]]
 b := ![[], [90, 45]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 2
  hpos := by decide
  P := [193, 4, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![541, 170, -3]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5, 1, -3]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N0 B_one_repr
lemma NI233N0 : Nat.card (O ⧸ I233N0) = 54289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N0

def I233N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0], ![-21, 1, 0]] i)))

def SI233N1: IdealEqSpanCertificate' Table ![![233, 0, 0], ![-21, 1, 0]] 
 ![![233, 0, 0], ![212, 1, 0], ![25, 0, 1]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]], ![![-21, 1, 0], ![0, -21, 1], ![174, 0, -21]]]
  hmulB := by decide  
  f := ![![![2584, -123, 0], ![28659, 0, 0]], ![![2332, -111, 0], ![25864, 0, 0]], ![![296, -14, 0], ![3283, 1, 0]]]
  g := ![![![1, 0, 0], ![-212, 233, 0], ![-25, 0, 233]], ![![-1, 1, 0], ![19, -21, 1], ![3, 0, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N1 : Nat.card (O ⧸ I233N1) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N1)

lemma isPrimeI233N1 : Ideal.IsPrime I233N1 := prime_ideal_of_norm_prime hp233.out _ NI233N1
def MulI233N0 : IdealMulLeCertificate' Table 
  ![![233, 0, 0], ![-25, 21, 1]] ![![233, 0, 0], ![-21, 1, 0]]
  ![![233, 0, 0]] where
 M := ![![![54289, 0, 0], ![-4893, 233, 0]], ![![-5825, 4893, 233], ![699, -466, 0]]]
 hmul := by decide  
 g := ![![![![233, 0, 0]], ![![-21, 1, 0]]], ![![![-25, 21, 1]], ![![3, -2, 0]]]]
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

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0], ![-86, 48, 1]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![239, 0, 0], ![-86, 48, 1]] 
 ![![239, 0, 0], ![0, 239, 0], ![153, 48, 1]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]], ![![-86, 48, 1], ![174, -86, 48], ![8352, 174, -86]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-153, -48, 239]], ![![-1, 0, 1], ![-30, -10, 48], ![90, 18, -86]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P0 : CertificateIrreducibleZModOfList' 239 2 2 7 [182, 107, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [132, 238], [0, 1]]
 g := ![![[191, 109], [80, 170], [53, 22], [8, 124], [75], [43, 200], [132, 1]], ![[0, 130], [54, 69], [89, 217], [124, 115], [75], [153, 39], [25, 238]]]
 h' := ![![[132, 238], [19, 161], [153, 130], [217, 168], [109, 210], [61, 187], [115, 34], [0, 1]], ![[0, 1], [0, 78], [105, 109], [166, 71], [105, 29], [128, 52], [62, 205], [132, 238]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [211]]
 b := ![[], [207, 225]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 2
  hpos := by decide
  P := [182, 107, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6902, 2245, 470]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-272, -85, 470]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N0 B_one_repr
lemma NI239N0 : Nat.card (O ⧸ I239N0) = 57121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N0

def I239N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0], ![-48, 1, 0]] i)))

def SI239N1: IdealEqSpanCertificate' Table ![![239, 0, 0], ![-48, 1, 0]] 
 ![![239, 0, 0], ![191, 1, 0], ![86, 0, 1]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]], ![![-48, 1, 0], ![0, -48, 1], ![174, 0, -48]]]
  hmulB := by decide  
  f := ![![![337, -7, 0], ![1673, 0, 0]], ![![289, -6, 0], ![1435, 0, 0]], ![![202, -4, 0], ![1004, 1, 0]]]
  g := ![![![1, 0, 0], ![-191, 239, 0], ![-86, 0, 239]], ![![-1, 1, 0], ![38, -48, 1], ![18, 0, -48]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N1 : Nat.card (O ⧸ I239N1) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N1)

lemma isPrimeI239N1 : Ideal.IsPrime I239N1 := prime_ideal_of_norm_prime hp239.out _ NI239N1
def MulI239N0 : IdealMulLeCertificate' Table 
  ![![239, 0, 0], ![-86, 48, 1]] ![![239, 0, 0], ![-48, 1, 0]]
  ![![239, 0, 0]] where
 M := ![![![57121, 0, 0], ![-11472, 239, 0]], ![![-20554, 11472, 239], ![4302, -2390, 0]]]
 hmul := by decide  
 g := ![![![![239, 0, 0]], ![![-48, 1, 0]]], ![![![-86, 48, 1]], ![![18, -10, 0]]]]
 hle2 := by decide  


def PBC239 : ContainsPrimesAboveP 239 ![I239N0, I239N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI239N0
    exact isPrimeI239N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 239 (by decide) (𝕀 ⊙ MulI239N0)
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


def P241P0 : CertificateIrreducibleZModOfList' 241 3 2 7 [153, 123, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [75, 97, 76], [163, 143, 165], [0, 1]]
 g := ![![[146, 237, 231], [200, 232], [144, 82], [86, 30], [221, 33, 75], [34, 229, 9], [1]], ![[17, 131, 27, 152], [75, 216], [52, 151], [42, 196], [153, 98, 179, 127], [67, 111, 2, 206], [162, 138, 219, 115]], ![[123, 4, 98, 73], [91, 177], [8, 64], [112, 10], [16, 15, 183, 17], [83, 216, 205, 21], [240, 228, 46, 126]]]
 h' := ![![[75, 97, 76], [36, 46, 183], [92, 78, 49], [124, 99, 75], [168, 181, 111], [100, 96, 39], [88, 118, 238], [0, 1]], ![[163, 143, 165], [187, 143, 22], [24, 0, 162], [168, 34, 174], [91, 98, 227], [165, 162, 100], [162, 174, 104], [75, 97, 76]], ![[0, 1], [238, 52, 36], [122, 163, 30], [83, 108, 233], [146, 203, 144], [144, 224, 102], [130, 190, 140], [163, 143, 165]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12, 157], []]
 b := ![[], [88, 174, 166], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 3
  hpos := by decide
  P := [153, 123, 3, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-25546, -4338, 1446]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-106, -18, 6]
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

instance hp251 : Fact (Nat.Prime 251) := {out := by norm_num}

def I251N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![251, 0, 0], ![-44, -61, 1]] i)))

def SI251N0: IdealEqSpanCertificate' Table ![![251, 0, 0], ![-44, -61, 1]] 
 ![![251, 0, 0], ![0, 251, 0], ![207, 190, 1]] where
  M :=![![![251, 0, 0], ![0, 251, 0], ![0, 0, 251]], ![![-44, -61, 1], ![174, -44, -61], ![-10614, 174, -44]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-207, -190, 251]], ![![-1, -1, 1], ![51, 46, -61], ![-6, 34, -44]]]
  hle1 := by decide   
  hle2 := by decide  


def P251P0 : CertificateIrreducibleZModOfList' 251 2 2 7 [73, 102, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [149, 250], [0, 1]]
 g := ![![[163, 196], [228, 17], [149], [219, 58], [157, 73], [7, 94], [149, 1]], ![[0, 55], [0, 234], [149], [76, 193], [241, 178], [208, 157], [47, 250]]]
 h' := ![![[149, 250], [173, 14], [72, 45], [77, 231], [85, 73], [242, 233], [167, 40], [0, 1]], ![[0, 1], [0, 237], [0, 206], [109, 20], [169, 178], [70, 18], [103, 211], [149, 250]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [237]]
 b := ![[], [145, 244]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI251N0 : CertifiedPrimeIdeal' SI251N0 251 where
  n := 2
  hpos := by decide
  P := [73, 102, 1]
  hirr := P251P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![769, 798, 205]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-166, -152, 205]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI251N0 : Ideal.IsPrime I251N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI251N0 B_one_repr
lemma NI251N0 : Nat.card (O ⧸ I251N0) = 63001 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI251N0

def I251N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![251, 0, 0], ![61, 1, 0]] i)))

def SI251N1: IdealEqSpanCertificate' Table ![![251, 0, 0], ![61, 1, 0]] 
 ![![251, 0, 0], ![61, 1, 0], ![44, 0, 1]] where
  M :=![![![251, 0, 0], ![0, 251, 0], ![0, 0, 251]], ![![61, 1, 0], ![0, 61, 1], ![174, 0, 61]]]
  hmulB := by decide  
  f := ![![![5186, 85, 0], ![-21335, 0, 0]], ![![1220, 20, 0], ![-5019, 0, 0]], ![![808, 13, 0], ![-3324, 1, 0]]]
  g := ![![![1, 0, 0], ![-61, 251, 0], ![-44, 0, 251]], ![![0, 1, 0], ![-15, 61, 1], ![-10, 0, 61]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N1 : Nat.card (O ⧸ I251N1) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N1)

lemma isPrimeI251N1 : Ideal.IsPrime I251N1 := prime_ideal_of_norm_prime hp251.out _ NI251N1
def MulI251N0 : IdealMulLeCertificate' Table 
  ![![251, 0, 0], ![-44, -61, 1]] ![![251, 0, 0], ![61, 1, 0]]
  ![![251, 0, 0]] where
 M := ![![![63001, 0, 0], ![15311, 251, 0]], ![![-11044, -15311, 251], ![-2510, -3765, 0]]]
 hmul := by decide  
 g := ![![![![251, 0, 0]], ![![61, 1, 0]]], ![![![-44, -61, 1]], ![![-10, -15, 0]]]]
 hle2 := by decide  


def PBC251 : ContainsPrimesAboveP 251 ![I251N0, I251N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI251N0
    exact isPrimeI251N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 251 (by decide) (𝕀 ⊙ MulI251N0)


lemma PB256I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 255 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 255 (by omega)

def PB256I4 : PrimesBelowBoundCertificateInterval O 193 255 256 where
  m := 10
  g := ![2, 3, 1, 3, 2, 1, 2, 2, 1, 2]
  P := ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251]
  hP := PB256I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1]
    · exact ![I199N0, I199N1, I199N2]
    · exact ![I211N0]
    · exact ![I223N0, I223N1, I223N2]
    · exact ![I227N0, I227N1]
    · exact ![I229N0]
    · exact ![I233N0, I233N1]
    · exact ![I239N0, I239N1]
    · exact ![I241N0]
    · exact ![I251N0, I251N1]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![38809, 197]
    · exact ![199, 199, 199]
    · exact ![9393931]
    · exact ![223, 223, 223]
    · exact ![51529, 227]
    · exact ![12008989]
    · exact ![54289, 233]
    · exact ![57121, 239]
    · exact ![13997521]
    · exact ![63001, 251]
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
      exact NI223N2
    · dsimp ; intro j
      fin_cases j
      exact NI227N0
      exact NI227N1
    · dsimp ; intro j
      fin_cases j
      exact NI229N0
    · dsimp ; intro j
      fin_cases j
      exact NI233N0
      exact NI233N1
    · dsimp ; intro j
      fin_cases j
      exact NI239N0
      exact NI239N1
    · dsimp ; intro j
      fin_cases j
      exact NI241N0
    · dsimp ; intro j
      fin_cases j
      exact NI251N0
      exact NI251N1
  β := ![I197N1, I199N0, I199N1, I199N2, I223N0, I223N1, I223N2, I227N1, I233N1, I239N1, I251N1]
  Il := ![[I197N1], [I199N0, I199N1, I199N2], [], [I223N0, I223N1, I223N2], [I227N1], [], [I233N1], [I239N1], [], [I251N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
