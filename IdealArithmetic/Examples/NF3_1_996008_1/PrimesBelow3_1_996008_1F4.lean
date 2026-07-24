
import IdealArithmetic.Examples.NF3_1_996008_1.RI3_1_996008_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![53, 1, 0]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![197, 0, 0], ![53, 1, 0]] 
 ![![197, 0, 0], ![53, 1, 0], ![146, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![53, 1, 0], ![0, 53, 1], ![198, 25, 53]]]
  hmulB := by decide  
  f := ![![![5036, 95, 0], ![-18715, 0, 0]], ![![1272, 24, 0], ![-4727, 0, 0]], ![![3778, 71, 0], ![-14040, 1, 0]]]
  g := ![![![1, 0, 0], ![-53, 197, 0], ![-146, 0, 197]], ![![0, 1, 0], ![-15, 53, 1], ![-45, 25, 53]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N0 : Nat.card (O ⧸ I197N0) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N0)

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := prime_ideal_of_norm_prime hp197.out _ NI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![66, 1, 0]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![197, 0, 0], ![66, 1, 0]] 
 ![![197, 0, 0], ![66, 1, 0], ![175, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![66, 1, 0], ![0, 66, 1], ![198, 25, 66]]]
  hmulB := by decide  
  f := ![![![67, 1, 0], ![-197, 0, 0]], ![![-66, -1, 0], ![198, 0, 0]], ![![89, 1, 0], ![-263, 1, 0]]]
  g := ![![![1, 0, 0], ![-66, 197, 0], ![-175, 0, 197]], ![![0, 1, 0], ![-23, 66, 1], ![-66, 25, 66]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1

def I197N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![78, 1, 0]] i)))

def SI197N2: IdealEqSpanCertificate' Table ![![197, 0, 0], ![78, 1, 0]] 
 ![![197, 0, 0], ![78, 1, 0], ![23, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![78, 1, 0], ![0, 78, 1], ![198, 25, 78]]]
  hmulB := by decide  
  f := ![![![2965, 38, 0], ![-7486, 0, 0]], ![![1170, 15, 0], ![-2954, 0, 0]], ![![343, 4, 0], ![-866, 1, 0]]]
  g := ![![![1, 0, 0], ![-78, 197, 0], ![-23, 0, 197]], ![![0, 1, 0], ![-31, 78, 1], ![-18, 25, 78]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N2 : Nat.card (O ⧸ I197N2) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N2)

lemma isPrimeI197N2 : Ideal.IsPrime I197N2 := prime_ideal_of_norm_prime hp197.out _ NI197N2
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![197, 0, 0], ![53, 1, 0]] ![![197, 0, 0], ![66, 1, 0]]
  ![![197, 0, 0], ![-48, -78, 1]] where
 M := ![![![38809, 0, 0], ![13002, 197, 0]], ![![10441, 197, 0], ![3498, 119, 1]]]
 hmul := by decide  
 g := ![![![![197, 0, 0], ![0, 0, 0]], ![![66, 1, 0], ![0, 0, 0]]], ![![![53, 1, 0], ![0, 0, 0]], ![![18, 1, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI197N1 : IdealMulLeCertificate' Table 
  ![![197, 0, 0], ![-48, -78, 1]] ![![197, 0, 0], ![78, 1, 0]]
  ![![197, 0, 0]] where
 M := ![![![38809, 0, 0], ![15366, 197, 0]], ![![-9456, -15366, 197], ![-3546, -6107, 0]]]
 hmul := by decide  
 g := ![![![![197, 0, 0]], ![![78, 1, 0]]], ![![![-48, -78, 1]], ![![-18, -31, 0]]]]
 hle2 := by decide  


def PBC197 : ContainsPrimesAboveP 197 ![I197N0, I197N1, I197N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
    exact isPrimeI197N1
    exact isPrimeI197N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 197 (by decide) (𝕀 ⊙ MulI197N0 ⊙ MulI197N1)
instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![78, -74, 1]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![199, 0, 0], ![78, -74, 1]] 
 ![![199, 0, 0], ![0, 199, 0], ![78, 125, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![78, -74, 1], ![198, 103, -74], ![-14652, -1652, 103]]]
  hmulB := by decide  
  f := ![![![-77, 74, -1], ![199, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-78, -125, 199]], ![![0, -1, 1], ![30, 47, -74], ![-114, -73, 103]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 2 2 7 [193, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [178, 198], [0, 1]]
 g := ![![[96, 33], [102, 29], [134, 43], [139], [91], [13], [178, 1]], ![[0, 166], [90, 170], [27, 156], [139], [91], [13], [157, 198]]]
 h' := ![![[178, 198], [15, 86], [8, 32], [198, 178], [110, 138], [34, 115], [73, 49], [0, 1]], ![[0, 1], [0, 113], [132, 167], [42, 21], [197, 61], [7, 84], [39, 150], [178, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [193]]
 b := ![[], [68, 196]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 2
  hpos := by decide
  P := [193, 21, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![589, 227, 5]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1, -2, 5]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 39601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![74, 1, 0]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![199, 0, 0], ![74, 1, 0]] 
 ![![199, 0, 0], ![74, 1, 0], ![96, 0, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![74, 1, 0], ![0, 74, 1], ![198, 25, 74]]]
  hmulB := by decide  
  f := ![![![4293, 58, 0], ![-11542, 0, 0]], ![![1554, 21, 0], ![-4178, 0, 0]], ![![1952, 26, 0], ![-5248, 1, 0]]]
  g := ![![![1, 0, 0], ![-74, 199, 0], ![-96, 0, 199]], ![![0, 1, 0], ![-28, 74, 1], ![-44, 25, 74]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![199, 0, 0], ![78, -74, 1]] ![![199, 0, 0], ![74, 1, 0]]
  ![![199, 0, 0]] where
 M := ![![![39601, 0, 0], ![14726, 199, 0]], ![![15522, -14726, 199], ![5970, -5373, 0]]]
 hmul := by decide  
 g := ![![![![199, 0, 0]], ![![74, 1, 0]]], ![![![78, -74, 1]], ![![30, -27, 0]]]]
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

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![80, 1, 0]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![211, 0, 0], ![80, 1, 0]] 
 ![![211, 0, 0], ![80, 1, 0], ![141, 0, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![80, 1, 0], ![0, 80, 1], ![198, 25, 80]]]
  hmulB := by decide  
  f := ![![![6081, 76, 0], ![-16036, 0, 0]], ![![2320, 29, 0], ![-6118, 0, 0]], ![![4031, 50, 0], ![-10630, 1, 0]]]
  g := ![![![1, 0, 0], ![-80, 211, 0], ![-141, 0, 211]], ![![0, 1, 0], ![-31, 80, 1], ![-62, 25, 80]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N0 : Nat.card (O ⧸ I211N0) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N0)

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := prime_ideal_of_norm_prime hp211.out _ NI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![-57, 1, 0]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![211, 0, 0], ![-57, 1, 0]] 
 ![![211, 0, 0], ![154, 1, 0], ![127, 0, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![-57, 1, 0], ![0, -57, 1], ![198, 25, -57]]]
  hmulB := by decide  
  f := ![![![10831, -190, 0], ![40090, 0, 0]], ![![7924, -139, 0], ![29330, 0, 0]], ![![6571, -115, 0], ![24322, 1, 0]]]
  g := ![![![1, 0, 0], ![-154, 211, 0], ![-127, 0, 211]], ![![-1, 1, 0], ![41, -57, 1], ![17, 25, -57]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1

def I211N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![-23, 1, 0]] i)))

def SI211N2: IdealEqSpanCertificate' Table ![![211, 0, 0], ![-23, 1, 0]] 
 ![![211, 0, 0], ![188, 1, 0], ![104, 0, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![-23, 1, 0], ![0, -23, 1], ![198, 25, -23]]]
  hmulB := by decide  
  f := ![![![3819, -166, 0], ![35026, 0, 0]], ![![3382, -147, 0], ![31018, 0, 0]], ![![1912, -83, 0], ![17536, 1, 0]]]
  g := ![![![1, 0, 0], ![-188, 211, 0], ![-104, 0, 211]], ![![-1, 1, 0], ![20, -23, 1], ![-10, 25, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N2 : Nat.card (O ⧸ I211N2) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N2)

lemma isPrimeI211N2 : Ideal.IsPrime I211N2 := prime_ideal_of_norm_prime hp211.out _ NI211N2
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![211, 0, 0], ![80, 1, 0]] ![![211, 0, 0], ![-57, 1, 0]]
  ![![211, 0, 0], ![82, 23, 1]] where
 M := ![![![44521, 0, 0], ![-12027, 211, 0]], ![![16880, 211, 0], ![-4560, 23, 1]]]
 hmul := by decide  
 g := ![![![![129, -23, -1], ![211, 0, 0]], ![![-57, 1, 0], ![0, 0, 0]]], ![![![-2, -22, -1], ![211, 0, 0]], ![![-22, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI211N1 : IdealMulLeCertificate' Table 
  ![![211, 0, 0], ![82, 23, 1]] ![![211, 0, 0], ![-23, 1, 0]]
  ![![211, 0, 0]] where
 M := ![![![44521, 0, 0], ![-4853, 211, 0]], ![![17302, 4853, 211], ![-1688, -422, 0]]]
 hmul := by decide  
 g := ![![![![211, 0, 0]], ![![-23, 1, 0]]], ![![![82, 23, 1]], ![![-8, -2, 0]]]]
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

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![223, 0, 0]] 
 ![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 3 2 7 [216, 95, 76, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [92, 89, 218], [55, 133, 5], [0, 1]]
 g := ![![[45, 145, 100], [64, 184, 188], [122, 117, 196], [98, 57, 73], [129, 0, 9], [56, 201], [1]], ![[14, 176, 120, 201], [88, 106, 101, 1], [164, 124, 129, 8], [159, 91, 207, 179], [132, 160, 187, 83], [29, 152], [170, 186, 119, 98]], ![[24, 178, 33, 107], [86, 194, 139, 10], [1, 211, 158, 57], [103, 22, 66, 190], [4, 34, 48, 184], [16, 128], [204, 46, 29, 125]]]
 h' := ![![[92, 89, 218], [2, 220, 10], [185, 222, 123], [17, 130, 14], [11, 35, 96], [218, 109, 220], [7, 128, 147], [0, 1]], ![[55, 133, 5], [120, 145, 7], [167, 28, 85], [219, 194, 97], [145, 68, 105], [182, 33, 171], [47, 99, 179], [92, 89, 218]], ![[0, 1], [222, 81, 206], [71, 196, 15], [124, 122, 112], [57, 120, 22], [188, 81, 55], [107, 219, 120], [55, 133, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48, 143], []]
 b := ![[], [200, 73, 207], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 3
  hpos := by decide
  P := [216, 95, 76, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![616372, 348772, 23638]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2764, 1564, 106]
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

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![49, 55, 1]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![227, 0, 0], ![49, 55, 1]] 
 ![![227, 0, 0], ![0, 227, 0], ![49, 55, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![49, 55, 1], ![198, 74, 55], ![10890, 1573, 74]]]
  hmulB := by decide  
  f := ![![![-48, -55, -1], ![227, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-49, -55, 227]], ![![0, 0, 1], ![-11, -13, 55], ![32, -11, 74]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 2 2 7 [102, 159, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [68, 226], [0, 1]]
 g := ![![[75, 69], [149, 177], [82], [110], [121], [9, 97], [68, 1]], ![[0, 158], [154, 50], [82], [110], [121], [22, 130], [136, 226]]]
 h' := ![![[68, 226], [11, 110], [119, 75], [159, 189], [16, 63], [217, 11], [101, 209], [0, 1]], ![[0, 1], [0, 117], [225, 152], [72, 38], [214, 164], [57, 216], [12, 18], [68, 226]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [213]]
 b := ![[], [11, 220]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 2
  hpos := by decide
  P := [102, 159, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6374, 179, -5]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-27, 2, -5]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 51529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![-55, 1, 0]] i)))

def SI227N1: IdealEqSpanCertificate' Table ![![227, 0, 0], ![-55, 1, 0]] 
 ![![227, 0, 0], ![172, 1, 0], ![153, 0, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![-55, 1, 0], ![0, -55, 1], ![198, 25, -55]]]
  hmulB := by decide  
  f := ![![![11441, -208, 0], ![47216, 0, 0]], ![![8636, -157, 0], ![35640, 0, 0]], ![![7769, -141, 0], ![32062, 1, 0]]]
  g := ![![![1, 0, 0], ![-172, 227, 0], ![-153, 0, 227]], ![![-1, 1, 0], ![41, -55, 1], ![19, 25, -55]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N1 : Nat.card (O ⧸ I227N1) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N1)

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := prime_ideal_of_norm_prime hp227.out _ NI227N1
def MulI227N0 : IdealMulLeCertificate' Table 
  ![![227, 0, 0], ![49, 55, 1]] ![![227, 0, 0], ![-55, 1, 0]]
  ![![227, 0, 0]] where
 M := ![![![51529, 0, 0], ![-12485, 227, 0]], ![![11123, 12485, 227], ![-2497, -2951, 0]]]
 hmul := by decide  
 g := ![![![![227, 0, 0]], ![![-55, 1, 0]]], ![![![49, 55, 1]], ![![-11, -13, 0]]]]
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

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0], ![-40, -108, 1]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![229, 0, 0], ![-40, -108, 1]] 
 ![![229, 0, 0], ![0, 229, 0], ![189, 121, 1]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]], ![![-40, -108, 1], ![198, -15, -108], ![-21384, -2502, -15]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-189, -121, 229]], ![![-1, -1, 1], ![90, 57, -108], ![-81, -3, -15]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 2 2 7 [212, 85, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [144, 228], [0, 1]]
 g := ![![[224, 202], [82], [140, 148], [184], [19], [20, 68], [144, 1]], ![[0, 27], [82], [155, 81], [184], [19], [194, 161], [59, 228]]]
 h' := ![![[144, 228], [105, 109], [90, 178], [33, 47], [49, 111], [111, 146], [158, 143], [0, 1]], ![[0, 1], [0, 120], [74, 51], [160, 182], [3, 118], [67, 83], [140, 86], [144, 228]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59]]
 b := ![[], [166, 144]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 2
  hpos := by decide
  P := [212, 85, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-890, 1719, -35]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![25, 26, -35]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 52441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def I229N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0], ![108, 1, 0]] i)))

def SI229N1: IdealEqSpanCertificate' Table ![![229, 0, 0], ![108, 1, 0]] 
 ![![229, 0, 0], ![108, 1, 0], ![15, 0, 1]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]], ![![108, 1, 0], ![0, 108, 1], ![198, 25, 108]]]
  hmulB := by decide  
  f := ![![![7561, 70, 0], ![-16030, 0, 0]], ![![3564, 33, 0], ![-7556, 0, 0]], ![![483, 4, 0], ![-1024, 1, 0]]]
  g := ![![![1, 0, 0], ![-108, 229, 0], ![-15, 0, 229]], ![![0, 1, 0], ![-51, 108, 1], ![-18, 25, 108]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N1 : Nat.card (O ⧸ I229N1) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N1)

lemma isPrimeI229N1 : Ideal.IsPrime I229N1 := prime_ideal_of_norm_prime hp229.out _ NI229N1
def MulI229N0 : IdealMulLeCertificate' Table 
  ![![229, 0, 0], ![-40, -108, 1]] ![![229, 0, 0], ![108, 1, 0]]
  ![![229, 0, 0]] where
 M := ![![![52441, 0, 0], ![24732, 229, 0]], ![![-9160, -24732, 229], ![-4122, -11679, 0]]]
 hmul := by decide  
 g := ![![![![229, 0, 0]], ![![108, 1, 0]]], ![![![-40, -108, 1]], ![![-18, -51, 0]]]]
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

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0], ![-129, 96, 1]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![233, 0, 0], ![-129, 96, 1]] 
 ![![233, 0, 0], ![0, 233, 0], ![104, 96, 1]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]], ![![-129, 96, 1], ![198, -104, 96], ![19008, 2598, -104]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-104, -96, 233]], ![![-1, 0, 1], ![-42, -40, 96], ![128, 54, -104]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 2 2 7 [4, 58, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [175, 232], [0, 1]]
 g := ![![[131, 175], [171], [197], [208, 201], [220], [108, 51], [175, 1]], ![[0, 58], [171], [197], [200, 32], [220], [179, 182], [117, 232]]]
 h' := ![![[175, 232], [29, 117], [125, 138], [100, 165], [43, 203], [34, 57], [232, 98], [0, 1]], ![[0, 1], [0, 116], [43, 95], [83, 68], [152, 30], [223, 176], [140, 135], [175, 232]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [130]]
 b := ![[], [21, 65]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 2
  hpos := by decide
  P := [4, 58, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![400, 190, -32]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![16, 14, -32]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N0 B_one_repr
lemma NI233N0 : Nat.card (O ⧸ I233N0) = 54289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N0

def I233N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0], ![-96, 1, 0]] i)))

def SI233N1: IdealEqSpanCertificate' Table ![![233, 0, 0], ![-96, 1, 0]] 
 ![![233, 0, 0], ![137, 1, 0], ![104, 0, 1]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]], ![![-96, 1, 0], ![0, -96, 1], ![198, 25, -96]]]
  hmulB := by decide  
  f := ![![![2785, -29, 0], ![6757, 0, 0]], ![![1729, -18, 0], ![4195, 0, 0]], ![![1384, -14, 0], ![3358, 1, 0]]]
  g := ![![![1, 0, 0], ![-137, 233, 0], ![-104, 0, 233]], ![![-1, 1, 0], ![56, -96, 1], ![29, 25, -96]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N1 : Nat.card (O ⧸ I233N1) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N1)

lemma isPrimeI233N1 : Ideal.IsPrime I233N1 := prime_ideal_of_norm_prime hp233.out _ NI233N1
def MulI233N0 : IdealMulLeCertificate' Table 
  ![![233, 0, 0], ![-129, 96, 1]] ![![233, 0, 0], ![-96, 1, 0]]
  ![![233, 0, 0]] where
 M := ![![![54289, 0, 0], ![-22368, 233, 0]], ![![-30057, 22368, 233], ![12582, -9320, 0]]]
 hmul := by decide  
 g := ![![![![233, 0, 0]], ![![-96, 1, 0]]], ![![![-129, 96, 1]], ![![54, -40, 0]]]]
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


def P239P0 : CertificateIrreducibleZModOfList' 239 3 2 7 [68, 15, 186, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [171, 103, 233], [121, 135, 6], [0, 1]]
 g := ![![[1, 133, 48], [195, 111, 202], [5, 99, 48], [11, 56, 176], [75, 150], [109, 63, 180], [1]], ![[17, 41, 34, 63], [208, 155, 190, 156], [127, 155, 113, 172], [26, 132, 152, 117], [198, 213], [186, 118, 219, 188], [128, 233, 154, 23]], ![[9, 36, 147, 110], [196, 37, 95, 125], [186, 161, 32, 30], [76, 177, 141, 124], [100, 161], [42, 48, 20, 75], [130, 147, 216, 216]]]
 h' := ![![[171, 103, 233], [124, 206, 185], [138, 129, 21], [208, 16, 185], [167, 30, 196], [236, 139, 129], [171, 224, 53], [0, 1]], ![[121, 135, 6], [185, 86, 78], [9, 234, 149], [44, 114, 23], [164, 45, 229], [208, 30, 90], [231, 235, 75], [171, 103, 233]], ![[0, 1], [13, 186, 215], [216, 115, 69], [51, 109, 31], [90, 164, 53], [213, 70, 20], [96, 19, 111], [121, 135, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77, 104], []]
 b := ![[], [200, 66, 97], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 3
  hpos := by decide
  P := [68, 15, 186, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3101742, 655816, 112330]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![12978, 2744, 470]
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


def P241P0 : CertificateIrreducibleZModOfList' 241 3 2 7 [90, 116, 53, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [227, 71, 47], [202, 169, 194], [0, 1]]
 g := ![![[43, 156, 67], [34, 145], [144, 200], [155, 235], [226, 120, 180], [206, 66, 158], [1]], ![[211, 177, 5, 182], [66, 192], [151, 80], [156, 151], [165, 46, 101, 75], [167, 73, 11, 60], [54, 65, 219, 193]], ![[86, 2, 52, 113], [138, 30], [83, 232], [171, 96], [217, 181, 113, 49], [237, 151, 154, 53], [65, 16, 143, 48]]]
 h' := ![![[227, 71, 47], [32, 97, 157], [220, 230, 164], [86, 77, 220], [145, 146, 200], [17, 195, 136], [151, 125, 188], [0, 1]], ![[202, 169, 194], [229, 114, 3], [12, 140, 207], [180, 219, 70], [240, 74, 174], [14, 137, 96], [108, 232, 51], [227, 71, 47]], ![[0, 1], [187, 30, 81], [202, 112, 111], [116, 186, 192], [166, 21, 108], [106, 150, 9], [142, 125, 2], [202, 169, 194]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77, 40], []]
 b := ![[], [99, 13, 194], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 3
  hpos := by decide
  P := [90, 116, 53, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-48682, -6507, 2169]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-202, -27, 9]
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

def I251N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![251, 0, 0], ![46, 1, 0]] i)))

def SI251N0: IdealEqSpanCertificate' Table ![![251, 0, 0], ![46, 1, 0]] 
 ![![251, 0, 0], ![46, 1, 0], ![143, 0, 1]] where
  M :=![![![251, 0, 0], ![0, 251, 0], ![0, 0, 251]], ![![46, 1, 0], ![0, 46, 1], ![198, 25, 46]]]
  hmulB := by decide  
  f := ![![![6395, 139, 0], ![-34889, 0, 0]], ![![1150, 25, 0], ![-6274, 0, 0]], ![![3643, 79, 0], ![-19875, 1, 0]]]
  g := ![![![1, 0, 0], ![-46, 251, 0], ![-143, 0, 251]], ![![0, 1, 0], ![-9, 46, 1], ![-30, 25, 46]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N0 : Nat.card (O ⧸ I251N0) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N0)

lemma isPrimeI251N0 : Ideal.IsPrime I251N0 := prime_ideal_of_norm_prime hp251.out _ NI251N0

def I251N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![251, 0, 0], ![91, 1, 0]] i)))

def SI251N1: IdealEqSpanCertificate' Table ![![251, 0, 0], ![91, 1, 0]] 
 ![![251, 0, 0], ![91, 1, 0], ![2, 0, 1]] where
  M :=![![![251, 0, 0], ![0, 251, 0], ![0, 0, 251]], ![![91, 1, 0], ![0, 91, 1], ![198, 25, 91]]]
  hmulB := by decide  
  f := ![![![5643, 62, 0], ![-15562, 0, 0]], ![![2093, 23, 0], ![-5772, 0, 0]], ![![-58, -1, 0], ![160, 1, 0]]]
  g := ![![![1, 0, 0], ![-91, 251, 0], ![-2, 0, 251]], ![![0, 1, 0], ![-33, 91, 1], ![-9, 25, 91]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N1 : Nat.card (O ⧸ I251N1) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N1)

lemma isPrimeI251N1 : Ideal.IsPrime I251N1 := prime_ideal_of_norm_prime hp251.out _ NI251N1

def I251N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![251, 0, 0], ![114, 1, 0]] i)))

def SI251N2: IdealEqSpanCertificate' Table ![![251, 0, 0], ![114, 1, 0]] 
 ![![251, 0, 0], ![114, 1, 0], ![56, 0, 1]] where
  M :=![![![251, 0, 0], ![0, 251, 0], ![0, 0, 251]], ![![114, 1, 0], ![0, 114, 1], ![198, 25, 114]]]
  hmulB := by decide  
  f := ![![![7525, 66, 0], ![-16566, 0, 0]], ![![3306, 29, 0], ![-7278, 0, 0]], ![![1648, 14, 0], ![-3628, 1, 0]]]
  g := ![![![1, 0, 0], ![-114, 251, 0], ![-56, 0, 251]], ![![0, 1, 0], ![-52, 114, 1], ![-36, 25, 114]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N2 : Nat.card (O ⧸ I251N2) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N2)

lemma isPrimeI251N2 : Ideal.IsPrime I251N2 := prime_ideal_of_norm_prime hp251.out _ NI251N2
def MulI251N0 : IdealMulLeCertificate' Table 
  ![![251, 0, 0], ![46, 1, 0]] ![![251, 0, 0], ![91, 1, 0]]
  ![![251, 0, 0], ![-81, -114, 1]] where
 M := ![![![63001, 0, 0], ![22841, 251, 0]], ![![11546, 251, 0], ![4186, 137, 1]]]
 hmul := by decide  
 g := ![![![![251, 0, 0], ![0, 0, 0]], ![![91, 1, 0], ![0, 0, 0]]], ![![![46, 1, 0], ![0, 0, 0]], ![![17, 1, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI251N1 : IdealMulLeCertificate' Table 
  ![![251, 0, 0], ![-81, -114, 1]] ![![251, 0, 0], ![114, 1, 0]]
  ![![251, 0, 0]] where
 M := ![![![63001, 0, 0], ![28614, 251, 0]], ![![-20331, -28614, 251], ![-9036, -13052, 0]]]
 hmul := by decide  
 g := ![![![![251, 0, 0]], ![![114, 1, 0]]], ![![![-81, -114, 1]], ![![-36, -52, 0]]]]
 hle2 := by decide  


def PBC251 : ContainsPrimesAboveP 251 ![I251N0, I251N1, I251N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI251N0
    exact isPrimeI251N1
    exact isPrimeI251N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 251 (by decide) (𝕀 ⊙ MulI251N0 ⊙ MulI251N1)
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


def P257P0 : CertificateIrreducibleZModOfList' 257 3 2 8 [235, 2, 157, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [197, 84, 177], [160, 172, 80], [0, 1]]
 g := ![![[44, 113, 208], [159, 178], [169, 146], [77, 227], [11, 195], [211, 111], [100, 1], []], ![[58, 20, 52, 80], [105, 116], [56, 25], [211, 231], [224, 253], [72, 207], [222, 29], [251, 232]], ![[166, 173, 218, 20], [188, 196], [155, 59], [252, 207], [204, 95], [216, 99], [122, 117], [91, 232]]]
 h' := ![![[197, 84, 177], [241, 35, 112], [220, 3, 101], [247, 105, 143], [98, 6, 235], [192, 100, 130], [144, 79, 232], [0, 0, 1], [0, 1]], ![[160, 172, 80], [29, 36, 16], [17, 38, 170], [29, 64, 5], [28, 230, 105], [165, 183, 225], [196, 180, 174], [127, 176, 172], [197, 84, 177]], ![[0, 1], [158, 186, 129], [52, 216, 243], [165, 88, 109], [77, 21, 174], [27, 231, 159], [186, 255, 108], [103, 81, 84], [160, 172, 80]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [224, 54], []]
 b := ![[], [162, 49, 187], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N0 : CertifiedPrimeIdeal' SI257N0 257 where
  n := 3
  hpos := by decide
  P := [235, 2, 157, 1]
  hirr := P257P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![497809, 227959, 23387]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1937, 887, 91]
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



lemma PB283I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 257 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 257 (by omega)

def PB283I4 : PrimesBelowBoundCertificateInterval O 193 257 283 where
  m := 11
  g := ![3, 2, 3, 1, 2, 2, 2, 1, 1, 3, 1]
  P := ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257]
  hP := PB283I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1, I197N2]
    · exact ![I199N0, I199N1]
    · exact ![I211N0, I211N1, I211N2]
    · exact ![I223N0]
    · exact ![I227N0, I227N1]
    · exact ![I229N0, I229N1]
    · exact ![I233N0, I233N1]
    · exact ![I239N0]
    · exact ![I241N0]
    · exact ![I251N0, I251N1, I251N2]
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
    · exact ![197, 197, 197]
    · exact ![39601, 199]
    · exact ![211, 211, 211]
    · exact ![11089567]
    · exact ![51529, 227]
    · exact ![52441, 229]
    · exact ![54289, 233]
    · exact ![13651919]
    · exact ![13997521]
    · exact ![251, 251, 251]
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
      exact NI197N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI227N0
      exact NI227N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI251N0
      exact NI251N1
      exact NI251N2
    · dsimp ; intro j
      fin_cases j
      exact NI257N0
  β := ![I197N0, I197N1, I197N2, I199N1, I211N0, I211N1, I211N2, I227N1, I229N1, I233N1, I251N0, I251N1, I251N2]
  Il := ![[I197N0, I197N1, I197N2], [I199N1], [I211N0, I211N1, I211N2], [], [I227N1], [I229N1], [I233N1], [], [], [I251N0, I251N1, I251N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
