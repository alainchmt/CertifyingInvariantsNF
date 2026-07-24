
import IdealArithmetic.Examples.NF3_1_732108_1.RI3_1_732108_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![-71, 28, 1]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![197, 0, 0], ![-71, 28, 1]] 
 ![![197, 0, 0], ![0, 197, 0], ![126, 28, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![-71, 28, 1], ![-19, -48, 139], ![1027, -910, -131]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-126, -28, 197]], ![![-1, 0, 1], ![-89, -20, 139], ![89, 14, -131]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 2 2 7 [4, 109, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [88, 196], [0, 1]]
 g := ![![[175, 148], [163], [158, 26], [90], [62], [97], [88, 1]], ![[0, 49], [163], [82, 171], [90], [62], [97], [176, 196]]]
 h' := ![![[88, 196], [44, 98], [156, 44], [25, 115], [155, 175], [194, 125], [42, 57], [0, 1]], ![[0, 1], [0, 99], [88, 153], [98, 82], [189, 22], [162, 72], [133, 140], [88, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [140]]
 b := ![[], [72, 70]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 2
  hpos := by decide
  P := [4, 109, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1093, -961, -1350]
  a := ![2, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![869, 187, -1350]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![58, 1, 0]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![197, 0, 0], ![58, 1, 0]] 
 ![![197, 0, 0], ![58, 1, 0], ![131, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![58, 1, 0], ![-2, 60, 5], ![37, -33, 57]]]
  hmulB := by decide  
  f := ![![![-5027, 156063, 13005], ![-591, -512397, 0]], ![![-1472, 45901, 3825], ![-196, -150705, 0]], ![![-3339, 103778, 8648], ![-406, -340731, 0]]]
  g := ![![![1, 0, 0], ![-58, 197, 0], ![-131, 0, 197]], ![![0, 1, 0], ![-21, 60, 5], ![-28, -33, 57]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![197, 0, 0], ![-71, 28, 1]] ![![197, 0, 0], ![58, 1, 0]]
  ![![197, 0, 0]] where
 M := ![![![38809, 0, 0], ![11426, 197, 0]], ![![-13987, 5516, 197], ![-4137, 1576, 197]]]
 hmul := by decide  
 g := ![![![![197, 0, 0]], ![![58, 1, 0]]], ![![![-71, 28, 1]], ![![-21, 8, 1]]]]
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

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![199, 0, 0]] 
 ![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 3 2 7 [38, 97, 196, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [80, 161, 176], [122, 37, 23], [0, 1]]
 g := ![![[155, 145, 177], [40, 95, 100], [135, 126, 23], [144, 106], [184, 5], [42, 9], [1]], ![[142, 50, 107, 133], [169, 76, 55, 142], [83, 93, 128, 137], [2, 49], [13, 62], [194, 126], [147, 110, 106, 171]], ![[108, 28, 52, 145], [193, 22, 26, 14], [147, 194, 151, 32], [21, 61], [2, 132], [185, 58], [12, 88, 98, 28]]]
 h' := ![![[80, 161, 176], [72, 18, 133], [44, 139, 10], [149, 70, 53], [192, 131, 92], [47, 170, 76], [161, 102, 3], [0, 1]], ![[122, 37, 23], [8, 167, 129], [73, 149, 158], [40, 115, 152], [135, 53, 192], [80, 110, 96], [158, 2, 153], [80, 161, 176]], ![[0, 1], [62, 14, 136], [174, 110, 31], [16, 14, 193], [139, 15, 114], [195, 118, 27], [114, 95, 43], [122, 37, 23]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [150, 134], []]
 b := ![[], [180, 86, 101], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 3
  hpos := by decide
  P := [38, 97, 196, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![440984, -568344, 933708]
  a := ![-5, 2, 12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2216, -2856, 4692]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 7880599 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def PBC199 : ContainsPrimesAboveP 199 ![I199N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI199N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![199, 0, 0]]) timesTableT_eq_Table B_one_repr 199 (by decide) 𝕀

instance hp211 : Fact (Nat.Prime 211) := {out := by norm_num}

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![63, 1, 0]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![211, 0, 0], ![63, 1, 0]] 
 ![![211, 0, 0], ![63, 1, 0], ![109, 0, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![63, 1, 0], ![-2, 65, 5], ![37, -33, 62]]]
  hmulB := by decide  
  f := ![![![-15851, 535675, 41205], ![-2110, -1738851, 0]], ![![-4731, 159903, 12300], ![-632, -519060, 0]], ![![-8195, 276723, 21286], ![-1068, -898269, 0]]]
  g := ![![![1, 0, 0], ![-63, 211, 0], ![-109, 0, 211]], ![![0, 1, 0], ![-22, 65, 5], ![-22, -33, 62]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N0 : Nat.card (O ⧸ I211N0) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N0)

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := prime_ideal_of_norm_prime hp211.out _ NI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![-57, 1, 0]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![211, 0, 0], ![-57, 1, 0]] 
 ![![211, 0, 0], ![154, 1, 0], ![90, 0, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![-57, 1, 0], ![-2, -55, 5], ![37, -33, -58]]]
  hmulB := by decide  
  f := ![![![-7114, -203505, 18500], ![1055, -780700, 0]], ![![-5171, -148504, 13500], ![845, -569700, 0]], ![![-3039, -86803, 7891], ![433, -333000, 0]]]
  g := ![![![1, 0, 0], ![-154, 211, 0], ![-90, 0, 211]], ![![-1, 1, 0], ![38, -55, 5], ![49, -33, -58]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1

def I211N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![-7, 1, 0]] i)))

def SI211N2: IdealEqSpanCertificate' Table ![![211, 0, 0], ![-7, 1, 0]] 
 ![![211, 0, 0], ![204, 1, 0], ![77, 0, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![-7, 1, 0], ![-2, -5, 5], ![37, -33, -8]]]
  hmulB := by decide  
  f := ![![![-11265, -28202, 28200], ![422, -1190040, 0]], ![![-10889, -27262, 27260], ![423, -1150372, 0]], ![![-4109, -10292, 10291], ![212, -434280, 0]]]
  g := ![![![1, 0, 0], ![-204, 211, 0], ![-77, 0, 211]], ![![-1, 1, 0], ![3, -5, 5], ![35, -33, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N2 : Nat.card (O ⧸ I211N2) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N2)

lemma isPrimeI211N2 : Ideal.IsPrime I211N2 := prime_ideal_of_norm_prime hp211.out _ NI211N2
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![211, 0, 0], ![63, 1, 0]] ![![211, 0, 0], ![-57, 1, 0]]
  ![![211, 0, 0], ![41, 86, 1]] where
 M := ![![![44521, 0, 0], ![-12027, 211, 0]], ![![13293, 211, 0], ![-3593, 8, 5]]]
 hmul := by decide  
 g := ![![![![170, -86, -1], ![211, 0, 0]], ![![-57, 1, 0], ![0, 0, 0]]], ![![![22, -85, -1], ![211, 0, 0]], ![![-18, -2, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI211N1 : IdealMulLeCertificate' Table 
  ![![211, 0, 0], ![41, 86, 1]] ![![211, 0, 0], ![-7, 1, 0]]
  ![![211, 0, 0]] where
 M := ![![![44521, 0, 0], ![-1477, 211, 0]], ![![8651, 18146, 211], ![-422, -422, 422]]]
 hmul := by decide  
 g := ![![![![211, 0, 0]], ![![-7, 1, 0]]], ![![![41, 86, 1]], ![![-2, -2, 2]]]]
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


def P223P0 : CertificateIrreducibleZModOfList' 223 3 2 7 [191, 222, 60, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [161, 114, 218], [2, 108, 5], [0, 1]]
 g := ![![[12, 80, 116], [76, 72, 148], [115, 103, 119], [213, 145, 146], [170, 145, 65], [190, 32], [1]], ![[145, 195, 16, 181], [0, 122, 85, 9], [135, 95, 112, 73], [55, 16, 137, 73], [90, 179, 119, 66], [69, 101], [156, 7, 217, 98]], ![[176, 112, 2, 77], [128, 39, 85, 103], [127, 81, 165, 149], [135, 161, 19, 159], [63, 111, 83, 108], [100, 63], [64, 83, 154, 125]]]
 h' := ![![[161, 114, 218], [202, 206, 134], [112, 109, 172], [126, 109, 157], [88, 36, 102], [191, 163, 180], [32, 1, 163], [0, 1]], ![[2, 108, 5], [159, 85, 62], [137, 95, 191], [139, 10, 132], [123, 222, 132], [41, 201, 116], [145, 220, 205], [161, 114, 218]], ![[0, 1], [23, 155, 27], [64, 19, 83], [26, 104, 157], [23, 188, 212], [26, 82, 150], [49, 2, 78], [2, 108, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51, 195], []]
 b := ![[], [42, 65, 39], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 3
  hpos := by decide
  P := [191, 222, 60, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11754244591, -9164357602, -7899017692]
  a := ![66, -129, -197]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![52709617, -41095774, -35421604]
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

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![-84, 5, 1]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![227, 0, 0], ![-84, 5, 1]] 
 ![![227, 0, 0], ![0, 227, 0], ![143, 5, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![-84, 5, 1], ![27, -107, 24], ![176, -151, -121]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-143, -5, 227]], ![![-1, 0, 1], ![-15, -1, 24], ![77, 2, -121]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 2 2 7 [153, 139, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [88, 226], [0, 1]]
 g := ![![[38, 101], [207, 205], [57], [70], [44], [22, 12], [88, 1]], ![[73, 126], [87, 22], [57], [70], [44], [170, 215], [176, 226]]]
 h' := ![![[88, 226], [109, 151], [208, 81], [59, 114], [10, 129], [39, 147], [156, 100], [0, 1]], ![[0, 1], [4, 76], [72, 146], [103, 113], [12, 98], [36, 80], [103, 127], [88, 226]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [172]]
 b := ![[], [75, 86]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 2
  hpos := by decide
  P := [153, 139, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2223, -789, -6423]
  a := ![5, -3, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4056, 138, -6423]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 51529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![-24, 1, 0]] i)))

def SI227N1: IdealEqSpanCertificate' Table ![![227, 0, 0], ![-24, 1, 0]] 
 ![![227, 0, 0], ![203, 1, 0], ![121, 0, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![-24, 1, 0], ![-2, -22, 5], ![37, -33, -25]]]
  hmulB := by decide  
  f := ![![![-32023, -354649, 80600], ![2043, -3659240, 0]], ![![-28637, -317138, 72075], ![1817, -3272205, 0]], ![![-17069, -189042, 42963], ![1094, -1950520, 0]]]
  g := ![![![1, 0, 0], ![-203, 227, 0], ![-121, 0, 227]], ![![-1, 1, 0], ![17, -22, 5], ![43, -33, -25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N1 : Nat.card (O ⧸ I227N1) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N1)

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := prime_ideal_of_norm_prime hp227.out _ NI227N1
def MulI227N0 : IdealMulLeCertificate' Table 
  ![![227, 0, 0], ![-84, 5, 1]] ![![227, 0, 0], ![-24, 1, 0]]
  ![![227, 0, 0]] where
 M := ![![![51529, 0, 0], ![-5448, 227, 0]], ![![-19068, 1135, 227], ![2043, -227, 0]]]
 hmul := by decide  
 g := ![![![![227, 0, 0]], ![![-24, 1, 0]]], ![![![-84, 5, 1]], ![![9, -1, 0]]]]
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


def P229P0 : CertificateIrreducibleZModOfList' 229 3 2 7 [159, 76, 130, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [213, 53, 227], [115, 175, 2], [0, 1]]
 g := ![![[111, 151, 167], [130, 20], [93, 131, 193], [224, 129], [176, 48], [180, 92, 183], [1]], ![[227, 134, 71, 160], [58, 104], [126, 9, 133, 21], [82, 214], [4, 176], [123, 6, 74, 105], [191, 178, 73, 221]], ![[106, 39, 176, 89], [100, 61], [175, 186, 126, 2], [170, 55], [144, 70], [56, 14, 109, 86], [50, 6, 144, 8]]]
 h' := ![![[213, 53, 227], [155, 167, 25], [98, 78, 132], [91, 181, 45], [208, 18, 154], [5, 179, 174], [70, 153, 99], [0, 1]], ![[115, 175, 2], [16, 98, 148], [188, 45, 44], [14, 158, 185], [107, 191, 121], [133, 27, 93], [114, 176, 73], [213, 53, 227]], ![[0, 1], [198, 193, 56], [143, 106, 53], [17, 119, 228], [224, 20, 183], [92, 23, 191], [151, 129, 57], [115, 175, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [99, 189], []]
 b := ![[], [125, 21, 209], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 3
  hpos := by decide
  P := [159, 76, 130, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![281899, -210680, -235870]
  a := ![2, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1231, -920, -1030]
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

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0], ![70, -97, 1]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![233, 0, 0], ![70, -97, 1]] 
 ![![233, 0, 0], ![0, 233, 0], ![70, 136, 1]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]], ![![70, -97, 1], ![231, -157, -486], ![-3598, 3215, 135]]]
  hmulB := by decide  
  f := ![![![-69, 97, -1], ![233, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-70, -136, 233]], ![![0, -1, 1], ![147, 283, -486], ![-56, -65, 135]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 2 2 7 [100, 191, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [42, 232], [0, 1]]
 g := ![![[172, 7], [215], [71], [213, 55], [4], [140, 157], [42, 1]], ![[0, 226], [215], [71], [193, 178], [4], [210, 76], [84, 232]]]
 h' := ![![[42, 232], [144, 163], [212, 139], [136, 184], [0, 88], [213, 2], [227, 33], [0, 1]], ![[0, 1], [0, 70], [225, 94], [175, 49], [201, 145], [64, 231], [215, 200], [42, 232]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [192]]
 b := ![[], [81, 96]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 2
  hpos := by decide
  P := [100, 191, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11518, -5935, 1709]
  a := ![-3, 23, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-464, -1023, 1709]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N0 B_one_repr
lemma NI233N0 : Nat.card (O ⧸ I233N0) = 54289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N0

def I233N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0], ![20, 1, 0]] i)))

def SI233N1: IdealEqSpanCertificate' Table ![![233, 0, 0], ![20, 1, 0]] 
 ![![233, 0, 0], ![20, 1, 0], ![98, 0, 1]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]], ![![20, 1, 0], ![-2, 22, 5], ![37, -33, 19]]]
  hmulB := by decide  
  f := ![![![-2659, 29260, 6650], ![0, -309890, 0]], ![![-228, 2508, 570], ![1, -26562, 0]], ![![-1134, 12306, 2797], ![182, -130340, 0]]]
  g := ![![![1, 0, 0], ![-20, 233, 0], ![-98, 0, 233]], ![![0, 1, 0], ![-4, 22, 5], ![-5, -33, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N1 : Nat.card (O ⧸ I233N1) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N1)

lemma isPrimeI233N1 : Ideal.IsPrime I233N1 := prime_ideal_of_norm_prime hp233.out _ NI233N1
def MulI233N0 : IdealMulLeCertificate' Table 
  ![![233, 0, 0], ![70, -97, 1]] ![![233, 0, 0], ![20, 1, 0]]
  ![![233, 0, 0]] where
 M := ![![![54289, 0, 0], ![4660, 233, 0]], ![![16310, -22601, 233], ![1631, -2097, -466]]]
 hmul := by decide  
 g := ![![![![233, 0, 0]], ![![20, 1, 0]]], ![![![70, -97, 1]], ![![7, -9, -2]]]]
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

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, -29, 7]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![31, -29, 7]] 
 ![![239, 0, 0], ![0, 239, 0], ![141, 30, 1]] where
  M :=![![![31, -29, 7], ![317, -258, -152], ![-1136, 1055, -164]]]
  hmulB := by decide  
  f := ![![![848, 11, 26]], ![![940, 12, 29]], ![![619, 8, 19]]]
  g := ![![![-4, -1, 7], ![91, 18, -152], ![92, 25, -164]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P0 : CertificateIrreducibleZModOfList' 239 2 2 7 [4, 37, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [202, 238], [0, 1]]
 g := ![![[69, 60], [85, 91], [144, 197], [23, 99], [4], [116, 220], [202, 1]], ![[0, 179], [64, 148], [25, 42], [184, 140], [4], [102, 19], [165, 238]]]
 h' := ![![[202, 238], [138, 120], [141, 197], [147, 83], [180, 147], [14, 2], [148, 170], [0, 1]], ![[0, 1], [0, 119], [22, 42], [183, 156], [238, 92], [179, 237], [72, 69], [202, 238]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [207, 121]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 2
  hpos := by decide
  P := [4, 37, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2622, -1705, -2885]
  a := ![-4, 5, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1713, 355, -2885]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N0 B_one_repr
lemma NI239N0 : Nat.card (O ⧸ I239N0) = 57121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N0

def I239N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![848, 11, 26]] i)))

def SI239N1: IdealEqSpanCertificate' Table ![![848, 11, 26]] 
 ![![239, 0, 0], ![90, 1, 0], ![160, 0, 1]] where
  M :=![![![848, 11, 26], ![940, 12, 29], ![173, 1, 5]]]
  hmulB := by decide  
  f := ![![![31, -29, 7]], ![![13, -12, 2]], ![![16, -15, 4]]]
  g := ![![![-18, 11, 26], ![-20, 12, 29], ![-3, 1, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N1 : Nat.card (O ⧸ I239N1) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N1)

lemma isPrimeI239N1 : Ideal.IsPrime I239N1 := prime_ideal_of_norm_prime hp239.out _ NI239N1
def MulI239N0 : IdealMulLeCertificate' Table 
  ![![31, -29, 7]] ![![848, 11, 26]]
  ![![239, 0, 0]] where
 M := ![![![239, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P241P0 : CertificateIrreducibleZModOfList' 241 3 2 7 [42, 174, 225, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [76, 74, 99], [181, 166, 142], [0, 1]]
 g := ![![[90, 50, 83], [88, 49], [122, 100], [154, 108], [235, 24, 221], [119, 215, 15], [1]], ![[154, 4, 168, 172], [33, 49], [1, 209], [148, 166], [91, 6, 103, 163], [231, 85, 71, 130], [214, 214, 120, 33]], ![[71, 191, 11, 66], [], [26, 216], [65, 81], [20, 97, 64, 88], [74, 204, 126, 66], [34, 118, 120, 208]]]
 h' := ![![[76, 74, 99], [0, 85, 18], [232, 88, 7], [160, 143, 10], [11, 149, 95], [63, 225, 170], [199, 67, 16], [0, 1]], ![[181, 166, 142], [45, 154, 76], [181, 2, 234], [127, 77, 152], [199, 37, 155], [64, 17, 126], [44, 200, 131], [76, 74, 99]], ![[0, 1], [141, 2, 147], [83, 151], [115, 21, 79], [215, 55, 232], [72, 240, 186], [195, 215, 94], [181, 166, 142]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 3], []]
 b := ![[], [111, 212, 73], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 3
  hpos := by decide
  P := [42, 174, 225, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7285912, -5636990, -5051360]
  a := ![5, -10, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![30232, -23390, -20960]
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



lemma PB243I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227, 229, 233, 239, 241] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 242 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 242 (by omega)

def PB243I4 : PrimesBelowBoundCertificateInterval O 193 242 243 where
  m := 9
  g := ![2, 1, 3, 1, 2, 1, 2, 2, 1]
  P := ![197, 199, 211, 223, 227, 229, 233, 239, 241]
  hP := PB243I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1]
    · exact ![I199N0]
    · exact ![I211N0, I211N1, I211N2]
    · exact ![I223N0]
    · exact ![I227N0, I227N1]
    · exact ![I229N0]
    · exact ![I233N0, I233N1]
    · exact ![I239N0, I239N1]
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
    · exact ![7880599]
    · exact ![211, 211, 211]
    · exact ![11089567]
    · exact ![51529, 227]
    · exact ![12008989]
    · exact ![54289, 233]
    · exact ![57121, 239]
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
  β := ![I197N1, I211N0, I211N1, I211N2, I227N1, I233N1, I239N1]
  Il := ![[I197N1], [], [I211N0, I211N1, I211N2], [], [I227N1], [], [I233N1], [I239N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
